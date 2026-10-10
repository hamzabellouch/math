import OAI.Combinatorics.VariableWL.Wrapping

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6

namespace VariableWL.ProductImages
open scoped CharTwo
open VariableWL.Affine

variable (r : ℕ) (P : Type uVariable1) (E : Type uVariable2)

structure Instance where
  dimension : P → ℕ
  dimension_one_or_two : ∀ p, dimension p = 1 ∨ dimension p = 2
  source : E → P
  target : E → P
  domain : E → Fin r → Finset Bool
  domain_nonempty : ∀ e i, (domain e i).Nonempty
  map : E → Fin r → Bool → Bool
  map_injective : ∀ e i, Set.InjOn (map e i) (domain e i)
  linearLeft : ∀ e, Vec (dimension (source e)) →ₗ[Bit] Bit
  linearRight : ∀ e, Vec (dimension (target e)) →ₗ[Bit] Bit
  constantLeft : E → Bit
  constantRight : E → Bit

namespace Instance
variable {r : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : Instance r P E)

abbrev Address (r : ℕ) := Fin r → Bool

def Allowed (e : E) (a : Address r) : Prop := ∀ i, a i ∈ J.domain e i

def mapAddress (e : E) (a : Address r) : Address r := fun i => J.map e i (a i)

def leftForm (e : E) (v : Vec (J.dimension (J.source e))) : Bit :=
  J.linearLeft e v + J.constantLeft e

def rightForm (e : E) (v : Vec (J.dimension (J.target e))) : Bit :=
  J.linearRight e v + J.constantRight e

structure Witness where
  values : ∀ p : P, Address r → Set (Vec (J.dimension p))
  nonempty : ∀ p a, (values p a).Nonempty
  images : ∀ e a, J.Allowed e a →
    J.leftForm e '' values (J.source e) a =
      J.rightForm e '' values (J.target e) (J.mapAddress e a)

def Consistent : Prop := Nonempty J.Witness

namespace Witness
variable {J} (Q : J.Witness)

def wireValues (e : E) (a : Address r) : Set Bit :=
  J.leftForm e '' Q.values (J.source e) a

theorem wireValues_nonempty (e : E) (a : Address r) :
    (Q.wireValues e a).Nonempty := (Q.nonempty _ _).image _

theorem right_image (e : E) (a : Address r) (ha : J.Allowed e a) :
    J.rightForm e '' Q.values (J.target e) (J.mapAddress e a) =
      Q.wireValues e a := (Q.images e a ha).symm

theorem lift_left (e : E) (a : Address r) {b : Bit} (hb : b ∈ Q.wireValues e a) :
    ∃ v ∈ Q.values (J.source e) a, J.leftForm e v = b := hb

theorem lift_right (e : E) (a : Address r) (ha : J.Allowed e a)
    {b : Bit} (hb : b ∈ Q.wireValues e a) :
    ∃ v ∈ Q.values (J.target e) (J.mapAddress e a), J.rightForm e v = b := by
  rw [← Q.right_image e a ha] at hb
  exact hb

end Witness

theorem exists_ambient (e : E) (i : Fin r) :
    ∃ f : Equiv.Perm Bool, ∀ a ∈ J.domain e i, f a = J.map e i a := by
  obtain ⟨f,hf⟩ := Equiv.Perm.exists_extending_pair
    (fun a : {a // a ∈ J.domain e i} => a.val)
    (fun a : {a // a ∈ J.domain e i} => J.map e i a.val)
    Subtype.val_injective (fun a b h => Subtype.ext (J.map_injective e i a.property b.property h))
  exact ⟨f, fun a ha => hf ⟨a,ha⟩⟩

noncomputable def ambient (e : E) (i : Fin r) : Equiv.Perm Bool :=
  (J.exists_ambient e i).choose

theorem ambient_on_domain (e : E) (i : Fin r) (a : Bool) (ha : a ∈ J.domain e i) :
    J.ambient e i a = J.map e i a := (J.exists_ambient e i).choose_spec a ha

open Subdivision
variable {n : ℕ}

def labels : Vertex P E n → Fin r → Finset Bool
  | .inl _, _ => Finset.univ
  | .inr (e,_), i => J.domain e i

def Matches (l : Link E n) (i : Fin r) (a b : Bool) : Prop :=
  a ∈ J.domain l.1 i ∧ b = if l.2.val = n then J.map l.1 i a else a

theorem matches_left (l : Link E n) (i : Fin r) {a b : Bool} (h : J.Matches l i a b) :
    a ∈ J.labels (left J.source l) i := by
  unfold left
  split_ifs <;> simp only [labels]
  · exact Finset.mem_univ _
  · exact h.1

theorem matches_right (l : Link E n) (i : Fin r) {a b : Bool} (h : J.Matches l i a b) :
    b ∈ J.labels (right J.target l) i := by
  unfold right
  split_ifs with hn
  · exact Finset.mem_univ _
  · simp only [labels]
    rw [h.2, ite_eq_right hn]
    exact h.1

noncomputable def alignment (cut : E → Fin (n+1)) :
    Vertex P E n → Fin r → Equiv.Perm Bool
  | .inl _, _ => Equiv.refl _
  | .inr (e,j), i => if j.val < (cut e).val then Equiv.refl _ else J.ambient e i

theorem alignment_match (hn : 0 < n) (cut : E → Fin (n+1))
    (l : Link E n) (hc : l.2 ≠ cut l.1) (i : Fin r)
    {a b : Bool} (h : J.Matches l i a b) :
    J.alignment cut (left J.source l) i a =
      J.alignment cut (right J.target l) i b := by
  have hv : l.2.val ≠ (cut l.1).val := fun hh => hc (Fin.ext hh)
  have hl := l.2.isLt
  have hk := (cut l.1).isLt
  unfold left right
  split_ifs with h₀ h₁ h₁
  · omega
  · simp only [alignment]
    rw [ite_eq_left (by omega)]
    simp only [Equiv.refl_apply]
    exact (h.2.trans (ite_eq_right h₁)).symm
  · simp only [alignment]
    rw [ite_eq_right (by omega), Equiv.refl_apply]
    rw [J.ambient_on_domain _ _ _ h.1, h.2, ite_eq_left h₁]
  · simp only [alignment]
    have hi : l.2.val - 1 < (cut l.1).val ↔ l.2.val < (cut l.1).val := by omega
    rw [h.2, ite_eq_right h₁]
    simp only [hi]

end Instance
end VariableWL.ProductImages

namespace VariableWL.ProductImages.Instance
open VariableWL.Affine Subdivision
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

abbrev Shifts (n : ℕ) := (∀ p, Vec (J.dimension p)) × (E × Fin n → Bit)

def shiftLeft (h : J.Shifts n) (l : Link E n) : Bit :=
  if h₀ : l.2.val = 0 then J.leftForm l.1 (h.1 (J.source l.1))
  else h.2 (l.1, ⟨l.2.val-1, by omega⟩)

def shiftRight (h : J.Shifts n) (l : Link E n) : Bit :=
  if h₁ : l.2.val = n then J.rightForm l.1 (h.1 (J.target l.1))
  else h.2 (l.1, ⟨l.2.val, by omega⟩)

def ShiftSystem (S : Set (Link E n)) (h : J.Shifts n) : Prop :=
  ∀ l ∈ S, J.shiftLeft h l = J.shiftRight h l

def cutShifts (cut : E → Fin (n+1)) (v : ∀ p, Vec (J.dimension p)) : J.Shifts n :=
  (v, fun (e,j) => if j.val < (cut e).val then J.leftForm e (v (J.source e))
    else J.rightForm e (v (J.target e)))

theorem cutShifts_equation (hn : 0 < n) (cut : E → Fin (n+1))
    (v : ∀ p, Vec (J.dimension p)) (l : Link E n) (hc : l.2 ≠ cut l.1) :
    J.shiftLeft (J.cutShifts cut v) l = J.shiftRight (J.cutShifts cut v) l := by
  have hv : l.2.val ≠ (cut l.1).val := fun h => hc (Fin.ext h)
  have hl := l.2.isLt
  have hk := (cut l.1).isLt
  unfold shiftLeft shiftRight
  split_ifs with h₀ h₁ h₁
  · omega
  · simp only [cutShifts]
    rw [ite_eq_left (by omega)]
  · simp only [cutShifts]
    rw [ite_eq_right (by omega)]
  · simp only [cutShifts]
    have hi : l.2.val - 1 < (cut l.1).val ↔ l.2.val < (cut l.1).val := by omega
    simp only [hi]

theorem small_shift_exists [DecidableEq E] (hn : 0 < n)
    (S : Finset (Link E n)) (hS : S.card < n+1) (v : ∀ p, Vec (J.dimension p)) :
    ∃ h : J.Shifts n, h.1 = v ∧ J.ShiftSystem S h := by
  obtain ⟨cut,hc⟩ := exists_unused_cut S hS
  refine ⟨J.cutShifts cut v, rfl, fun l hl => J.cutShifts_equation hn cut v l ?_⟩
  intro h
  exact hc l.1 (by change l ∈ S at hl; simpa only [← h, Prod.eta] using hl)

theorem internal_equation (h : J.Shifts n) (l : Link E n)
    (heq : J.shiftLeft h l = J.shiftRight h l)
    {e f : E} {i j : Fin n}
    (hl : left J.source l = .inr (e,i)) (hr : right J.target l = .inr (f,j)) :
    h.2 (e,i) = h.2 (f,j) := by
  unfold left at hl
  split at hl
  · cases hl
  · rename_i h₀
    unfold right at hr
    split at hr
    · cases hr
    · rename_i h₁
      have hl' := Sum.inr.inj hl
      have hr' := Sum.inr.inj hr
      simp only [shiftLeft, shiftRight, dite_eq_right h₀, dite_eq_right h₁] at heq
      simpa only [hl', hr'] using heq

end VariableWL.ProductImages.Instance

end OAI

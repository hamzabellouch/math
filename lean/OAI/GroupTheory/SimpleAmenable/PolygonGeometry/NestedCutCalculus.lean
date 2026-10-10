import Mathlib

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section NestedCutCalculus

variable {E H : Type*} [Group E] [Group H]

theorem commute_ratio_of_conjugation {u v x : H}
    (h : v*x*v⁻¹ = u*x*u⁻¹) : Commute x (u⁻¹*v) := by
  change x*(u⁻¹*v) = (u⁻¹*v)*x
  have ht := congrArg (fun z => u⁻¹*z*v) h
  simpa only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using ht.symm

def differenceHom (l g : E →* H)
    (h : ∀ s t, Commute (l s) ((l t)⁻¹*g t)) : E →* H where
  toFun t := (l t)⁻¹*g t
  map_one' := by simp
  map_mul' s t := by
    simp only [map_mul, mul_inv_rev]
    calc
      (l t)⁻¹*(l s)⁻¹*(g s*g t) = (l t)⁻¹*((l s)⁻¹*g s)*g t := by group
      _ = ((l s)⁻¹*g s)*(l t)⁻¹*g t := by rw [(h t s).inv_left.eq]
      _ = ((l s)⁻¹*g s)*((l t)⁻¹*g t) := by group

@[simp] theorem differenceHom_apply (l g : E →* H)
    (h : ∀ s t, Commute (l s) ((l t)⁻¹*g t)) (t : E) :
    differenceHom l g h t = (l t)⁻¹*g t := rfl

theorem split_conjugation (l k : E →* H) (h : ∀ s t, Commute (l s) (k t))
    (s t : E) : (l t*k t)*l s*(l t*k t)⁻¹ = l t*l s*(l t)⁻¹ := by
  calc
    (l t*k t)*l s*(l t*k t)⁻¹ = l t*(k t*l s)*(k t)⁻¹*(l t)⁻¹ := by group
    _ = l t*(l s*k t)*(k t)⁻¹*(l t)⁻¹ := by rw [(h s t).symm.eq]
    _ = l t*l s*(l t)⁻¹ := by group

theorem nested_cut_commute_ratio (f l₁ h₁ l₂ h₂ : E →* H)
    (hf₁ : ∀ s, f s = l₁ s*h₁ s) (hf₂ : ∀ s, f s = l₂ s*h₂ s)
    (hc₁ : ∀ s t, Commute (l₁ s) (h₁ t))
    (hc₁₂ : ∀ s t, Commute (l₁ s) (h₂ t)) :
    ∀ s t, Commute (l₁ s) ((l₂ t)⁻¹*f t) ∧
      Commute (l₁ s) ((l₁ t)⁻¹*l₂ t) := by
  intro s t
  constructor
  · simpa [hf₂] using hc₁₂ s t
  · apply commute_ratio_of_conjugation
    calc
      l₂ t*l₁ s*(l₂ t)⁻¹ = f t*l₁ s*(f t)⁻¹ := by
        rw [hf₂]
        calc
          l₂ t*l₁ s*(l₂ t)⁻¹ = l₂ t*(l₁ s*h₂ t)*(h₂ t)⁻¹*(l₂ t)⁻¹ := by group
          _ = l₂ t*(h₂ t*l₁ s)*(h₂ t)⁻¹*(l₂ t)⁻¹ := by rw [(hc₁₂ s t).eq]
          _ = (l₂ t*h₂ t)*l₁ s*(l₂ t*h₂ t)⁻¹ := by group
      _ = l₁ t*l₁ s*(l₁ t)⁻¹ := by rw [hf₁]; exact split_conjugation l₁ h₁ hc₁ s t

theorem nested_cut_difference (f l₁ h₁ l₂ h₂ : E →* H)
    (hf₁ : ∀ s, f s = l₁ s*h₁ s) (hf₂ : ∀ s, f s = l₂ s*h₂ s)
    (hc₁ : ∀ s t, Commute (l₁ s) (h₁ t))
    (hc₁₂ : ∀ s t, Commute (l₁ s) (h₂ t)) :
    ∃ d : E →* H, (∀ s, l₂ s = l₁ s*d s) ∧
      (∀ s t, Commute (l₁ s) (d t)) := by
  let hc := fun s t => (nested_cut_commute_ratio f l₁ h₁ l₂ h₂ hf₁ hf₂ hc₁ hc₁₂ s t).2
  refine ⟨differenceHom l₁ l₂ hc, ?_, hc⟩
  intro s
  simp

theorem ordered_differences_telescope (l : ℕ → H) (n : ℕ) :
    ((List.range n).map (fun i => (l i)⁻¹*l (i+1))).prod = (l 0)⁻¹*l n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp

theorem difference_commutes_with_prefix (earlier l g : E →* H)
    (h : ∀ s t, g t*earlier s*(g t)⁻¹ = l t*earlier s*(l t)⁻¹)
    (hc : ∀ s t, Commute (l s) ((l t)⁻¹*g t)) (s t : E) :
    Commute (earlier s) (differenceHom l g hc t) :=
  commute_ratio_of_conjugation (h s t)

end NestedCutCalculus

open scoped commutatorElement
section ConditionalControl
variable {E H : Type*} [Group E] [Group H]

theorem same_conj_iff (u v k : H) :
    u*k*u⁻¹ = v*k*v⁻¹ ↔ Commute (u⁻¹*v) k := by
  constructor
  · intro h
    apply commutatorElement_eq_one_iff_commute.mp
    rw [commutatorElement_def]
    calc
      _ = u⁻¹*(v*k*v⁻¹)*u*k⁻¹ := by group
      _ = u⁻¹*(u*k*u⁻¹)*u*k⁻¹ := by rw [← h]
      _ = 1 := by group
  · intro h
    have hc := h.eq
    calc
      u*k*u⁻¹ = u*(k*(u⁻¹*v))*v⁻¹ := by group
      _ = u*((u⁻¹*v)*k)*v⁻¹ := by rw [hc]
      _ = v*k*v⁻¹ := by group

theorem commute_of_conditional_move (u v k : H) (hv : Commute u v)
    (hk : Commute u (v*k*v⁻¹)) : Commute u k := by
  have h := (hv.inv_right.mul_right hk).mul_right hv
  simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using h

private theorem commutator_four (b c d e : H)
    (hcb : Commute c b) (hce : Commute c e) (hdb : Commute d b)
    (hcd : Commute c d) (hbe : Commute b e) :
    ⁅c*d,b*e⁆ = ⁅d,e⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    (hcb.mul_right hce).commutator_eq,mul_one,
    commutatorElement_mul_right_eq_mul_conj,hdb.commutator_eq,one_mul]
  have hb : Commute b ⁅d,e⁆ := by
    rw [commutatorElement_def]
    exact ((hdb.symm.mul_right hbe).mul_right hdb.symm.inv_right).mul_right hbe.inv_right
  have hc : Commute c ⁅d,e⁆ := by
    rw [commutatorElement_def]
    exact ((hcd.mul_right hce).mul_right hcd.inv_right).mul_right hce.inv_right
  calc
    _ = c* ⁅d,e⁆ *c⁻¹ := by rw [hb.eq]; group
    _ = ⁅d,e⁆ := by rw [hc.eq]; group

theorem four_factor_in_subgroup [Group.IsPerfect E]
    (b c d : E →* H) (C : Subgroup H)
    (hbc : ∀ s t, Commute (b s) (c t))
    (hbd : ∀ s t, Commute (b s) (d t))
    (hcd : ∀ s t, Commute (c s) (d t))
    (hJ : ∀ s, c s*d s ∈ C) (hK : ∀ s, b s*d s ∈ C) :
    d.range ≤ C := by
  have hh : ⁅d.range,d.range⁆ ≤ C := by
    apply Subgroup.commutator_le.mpr
    rintro _ ⟨s,rfl⟩ _ ⟨t,rfl⟩
    rw [← commutator_four (b t) (c s) (d s) (d t)
      (hbc t s).symm (hcd s t) (hbd t s).symm (hcd s s) (hbd t t)]
    exact C.mul_mem (C.mul_mem (C.mul_mem (hJ s) (hK t)) (C.inv_mem (hJ s)))
      (C.inv_mem (hK t))
  have he : (commutator E).map d = d.range := by
    rw [Group.IsPerfect.commutator_eq_top,← MonoidHom.range_eq_map]
  rw [← he,map_commutator_eq]
  exact hh

def SameActionOn (f g : E → H) (P : Subgroup H) : Prop :=
  ∀ s, ∀ k ∈ P, f s*k*(f s)⁻¹ = g s*k*(g s)⁻¹

theorem intersection_control [Group.IsPerfect E]
    (a b c d f : E →* H) (P : Subgroup H)
    (hbc : ∀ s t, Commute (b s) (c t))
    (hbd : ∀ s t, Commute (b s) (d t))
    (hcd : ∀ s t, Commute (c s) (d t))
    (hf : ∀ s, f s = a s*b s*c s*d s)
    (hJ : SameActionOn (fun s => a s*b s) f P)
    (hK : SameActionOn (fun s => a s*c s) f P) :
    SameActionOn a f P := by
  let C := Subgroup.centralizer (P : Set H)
  have hJ' (s : E) : c s*d s ∈ C := by
    intro k hk
    have he := (same_conj_iff _ _ _).mp (hJ s k hk)
    rw [hf] at he
    have hu : (a s*b s)⁻¹*(a s*b s*c s*d s) = c s*d s := by group
    rw [hu] at he
    exact he.eq.symm
  have hK' (s : E) : b s*d s ∈ C := by
    intro k hk
    have he := (same_conj_iff _ _ _).mp (hK s k hk)
    rw [hf] at he
    have hu : (a s*c s)⁻¹*(a s*b s*c s*d s) = b s*d s := by
      calc
        _ = (c s)⁻¹*b s*c s*d s := by group
        _ = (c s)⁻¹*c s*b s*d s := by
          simp only [mul_assoc]
          rw [← mul_assoc (b s) (c s) (d s), (hbc s s).eq, mul_assoc]
        _ = b s*d s := by group
    rw [hu] at he
    exact he.eq.symm
  have hd := four_factor_in_subgroup b c d C hbc hbd hcd hJ' hK'
  have hb (s : E) : b s ∈ C := by
    simpa using C.mul_mem (hK' s) (C.inv_mem (hd ⟨s,rfl⟩))
  have hc (s : E) : c s ∈ C := by
    simpa using C.mul_mem (hJ' s) (C.inv_mem (hd ⟨s,rfl⟩))
  intro s k hk
  apply (same_conj_iff _ _ _).mpr
  rw [hf]
  have hu : (a s)⁻¹*(a s*b s*c s*d s) = b s*c s*d s := by group
  rw [hu]
  exact (C.mul_mem (C.mul_mem (hb s) (hc s))
    (hd ⟨s,rfl⟩) k hk).symm

theorem conj_mul_of_commute (a b k : H) (h : Commute b k) :
    (a*b)*k*(a*b)⁻¹ = a*k*a⁻¹ := by
  calc
    _ = a*(b*k*b⁻¹)*a⁻¹ := by group
    _ = a*k*a⁻¹ := by rw [h.eq]; group

section NestedCuts
variable (f : E →* H) (l h : ℕ → E →* H)
    (hf : ∀ i s, f s = l i s*h i s)
    (hc : ∀ i j, i ≤ j → ∀ s t, Commute (l i s) (h j t))

def cutDifference (i : ℕ) : E →* H :=
  differenceHom (l i) (l (i+1)) (fun s t =>
    (nested_cut_commute_ratio f (l i) (h i) (l (i+1)) (h (i+1))
      (hf i) (hf (i+1)) (hc i i le_rfl) (hc i (i+1) (by omega)) s t).2)

theorem cutDifference_commute_prefix (i j : ℕ) (hij : j ≤ i) (s t : E) :
    Commute (cutDifference f l h hf hc i t) (l j s) := by
  change Commute ((l i t)⁻¹*l (i+1) t) (l j s)
  apply (same_conj_iff _ _ _).mp
  calc
    _ = f t*l j s*(f t)⁻¹ := by
      rw [hf i]
      exact (conj_mul_of_commute _ _ _ (hc j i hij s t).symm).symm
    _ = _ := by
      rw [hf (i+1)]
      exact conj_mul_of_commute _ _ _ (hc j (i+1) (by omega) s t).symm

theorem cutDifference_pairwise (i j : ℕ) (hij : i < j) (s t : E) :
    Commute (cutDifference f l h hf hc i s) (cutDifference f l h hf hc j t) := by
  change Commute ((l i s)⁻¹*l (i+1) s) (cutDifference f l h hf hc j t)
  exact ((cutDifference_commute_prefix f l h hf hc j i (by omega) s t).symm.inv_left).mul_left
    (cutDifference_commute_prefix f l h hf hc j (i+1) (by omega) s t).symm

theorem cutDifference_telescope (n : ℕ) (s : E) :
    ((List.range n).map (fun i => cutDifference f l h hf hc i s)).prod =
      (l 0 s)⁻¹*l n s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.prod_append,ih]
    simp only [List.map_singleton,List.prod_singleton]
    change (l 0 s)⁻¹*l n s*((l n s)⁻¹*l (n+1) s) = _
    group

end NestedCuts

end ConditionalControl

end SimpleAmenable
end
end

end OAI

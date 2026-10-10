import OAI.MathematicalPhysics.Heisenberg.ExchangeCycles

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical

open scoped BigOperators Classical
namespace Heisenberg.Exposure

section History
variable {V : Type*}

def trajectory (τ : ℕ → Equiv.Perm V) (c : ℕ → Bool) : ℕ → Equiv.Perm V
  | 0 => 1
  | n+1 => (if c n then τ n else 1) * trajectory τ c n

@[simp] lemma trajectory_zero (τ : ℕ → Equiv.Perm V) (c : ℕ → Bool) :
    trajectory τ c 0 = 1 := rfl

@[simp] lemma trajectory_succ (τ : ℕ → Equiv.Perm V) (c : ℕ → Bool) (n : ℕ) (a : V) :
    trajectory τ c (n+1) a = if c n then τ n (trajectory τ c n a) else trajectory τ c n a := by
  cases hc : c n <;> simp [trajectory, hc]

def SameHistory (τ : ℕ → Equiv.Perm V) (A : Set V) (b c : ℕ → Bool) (n : ℕ) : Prop :=
  ∀ t ≤ n, ∀ a ∈ A, trajectory τ b t a = trajectory τ c t a

def Revealed (τ : ℕ → Equiv.Perm V) (A : Set V) (b : ℕ → Bool) (i : ℕ) : Prop :=
  ∃ a ∈ A, τ i (trajectory τ b i a) ≠ trajectory τ b i a

theorem sameHistory_iff (τ : ℕ → Equiv.Perm V) (A : Set V) (b c : ℕ → Bool) (n : ℕ) :
    SameHistory τ A b c n ↔ ∀ i < n, Revealed τ A b i → c i = b i := by
  constructor
  · intro h i hi hr
    obtain ⟨a, ha, hne⟩ := hr
    have hpre := h i (by omega) a ha
    have hpost := h (i+1) (by omega) a ha
    rw [trajectory_succ, trajectory_succ, ← hpre] at hpost
    cases hb : b i <;> cases hc : c i
    · rfl
    · simp only [hb, hc, Bool.false_eq_true, ↓reduceIte] at hpost
      exact (hne hpost.symm).elim
    · simp only [hb, hc, Bool.false_eq_true, ↓reduceIte] at hpost
      exact (hne hpost).elim
    · rfl
  · intro h
    have ht : ∀ t, t ≤ n → ∀ a ∈ A, trajectory τ b t a = trajectory τ c t a := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        intro ht a ha
        have hp := ih (by omega) a ha
        rw [trajectory_succ, trajectory_succ, ← hp]
        by_cases hr : Revealed τ A b t
        · rw [h t (by omega) hr]
        · have he : τ t (trajectory τ b t a) = trajectory τ b t a := by
            by_contra hn
            exact hr ⟨a,ha,hn⟩
          rw [he]
          simp
    exact ht

theorem not_revealed_swap [DecidableEq V] (τ : ℕ → Equiv.Perm V) (A : Set V)
    (b : ℕ → Bool) (i : ℕ) (u v : V) (huv : u ≠ v) (hτ : τ i = Equiv.swap u v) :
    ¬Revealed τ A b i ↔
      (∀ a ∈ A, trajectory τ b i a ≠ u) ∧ (∀ a ∈ A, trajectory τ b i a ≠ v) := by
  constructor
  · intro h
    constructor <;> intro a ha he
    · apply h
      refine ⟨a,ha,?_⟩
      rw [hτ,he,Equiv.swap_apply_left]
      exact huv.symm
    · apply h
      refine ⟨a,ha,?_⟩
      rw [hτ,he,Equiv.swap_apply_right]
      exact huv
  · rintro ⟨hu,hv⟩ ⟨a,ha,hne⟩
    apply hne
    rw [hτ,Equiv.swap_apply_of_ne_of_ne (hu a ha) (hv a ha)]

end History

variable {I B : Type*} [Fintype I] [Fintype B]

def productWeight (w : I → B → ℝ) (c : I → B) : ℝ := ∏ i, w i (c i)

lemma productWeight_sum (w : I → B → ℝ) (hw : ∀ i, ∑ b, w i b = 1) :
    ∑ c, productWeight w c = 1 := by
  classical
  simp only [productWeight, ← Fintype.prod_sum, hw, Finset.prod_const_one]

omit [Fintype B] in
lemma productWeight_nonneg (w : I → B → ℝ) (hw : ∀ i b, 0 ≤ w i b) (c : I → B) :
    0 ≤ productWeight w c := Finset.prod_nonneg fun i _ => hw i (c i)

def merge (M : I → Prop) [DecidablePred M] (a : {i // M i} → B) (b : {i // ¬M i} → B) : I → B :=
  (Equiv.piEquivPiSubtypeProd M (fun _ => B)).symm (a,b)

omit [Fintype I] [Fintype B] in
lemma merge_left (M : I → Prop) [DecidablePred M] (a : {i // M i} → B)
    (b : {i // ¬M i} → B) (i : {i // M i}) : merge M a b i = a i := by
  simp [merge,Equiv.piEquivPiSubtypeProd,i.property]

omit [Fintype I] [Fintype B] in
lemma merge_right (M : I → Prop) [DecidablePred M] (a : {i // M i} → B)
    (b : {i // ¬M i} → B) (i : {i // ¬M i}) : merge M a b i = b i := by
  simp [merge,Equiv.piEquivPiSubtypeProd,i.property]

omit [Fintype B] in
lemma productWeight_merge (w : I → B → ℝ) (M : I → Prop) [DecidablePred M]
    (a : {i // M i} → B) (b : {i // ¬M i} → B) :
    productWeight w (merge M a b) =
      productWeight (fun i : {i // M i} => w i) a *
        productWeight (fun i : {i // ¬M i} => w i) b := by
  rw [productWeight, ← Fintype.prod_subtype_mul_prod_subtype M]
  simp only [merge_left,merge_right,productWeight]

theorem cylinder_disintegration (w : I → B → ℝ) (M : I → Prop) [DecidablePred M]
    (a : {i // M i} → B) (F : (I → B) → ℝ) :
    (∑ c : I → B, if (∀ i : {i // M i}, c i = a i) then productWeight w c * F c else 0) =
      productWeight (fun i : {i // M i} => w i) a *
        ∑ b : {i // ¬M i} → B, productWeight (fun i : {i // ¬M i} => w i) b * F (merge M a b) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd M (fun _ => B)
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  have hm (a' : {i // M i} → B) (b : {i // ¬M i} → B) :
      (∀ i : {i // M i}, (e.symm (a',b)) i = a i) ↔ a' = a := by
    change (∀ i : {i // M i}, merge M a' b i = a i) ↔ _
    simp only [merge_left,funext_iff]
  simp only [hm]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true]
    change (∑ b, productWeight w (merge M a b) * F (merge M a b)) = _
    simp_rw [productWeight_merge]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  · intro a' _ hne
    simp [hne]
  · simp

theorem cylinder_mass (w : I → B → ℝ) (hw : ∀ i, ∑ b, w i b = 1)
    (M : I → Prop) [DecidablePred M] (a : {i // M i} → B) :
    (∑ c : I → B, if (∀ i : {i // M i}, c i = a i) then productWeight w c else 0) =
      productWeight (fun i : {i // M i} => w i) a := by
  classical
  have h := cylinder_disintegration w M a (fun _ => 1)
  simp only [mul_one] at h
  simpa only [productWeight, ← Fintype.prod_sum, hw, Finset.prod_const_one, mul_one] using h


end Heisenberg.Exposure

open scoped Classical

namespace Heisenberg.LayeredExchange
variable {T V : Type*}
lemma wiring_update_swap [DecidableEq T] [DecidableEq V]
    (s : Equiv.Perm T) (σ : T → Equiv.Perm V) (t : T) (u v : V) :
    wiring s (Function.update σ t (Equiv.swap u v * σ t)) =
      Equiv.swap (s t,u) (s t,v) * wiring s σ := by
  have hc : Equiv.prodCongr s (Equiv.refl V) * Equiv.swap (t,u) (t,v) =
      Equiv.swap (s t,u) (s t,v) * Equiv.prodCongr s (Equiv.refl V) := by
    apply Equiv.ext
    intro z
    change (s (Equiv.swap (t,u) (t,v) z).1, (Equiv.swap (t,u) (t,v) z).2) =
      Equiv.swap (s t,u) (s t,v) (s z.1,z.2)
    by_cases hu : z = (t,u)
    · subst z; simp
    by_cases hv : z = (t,v)
    · subst z; simp
    have hu' : (s z.1,z.2) ≠ (s t,u) := by
      intro he; apply hu; exact Prod.ext (s.injective (congrArg Prod.fst he)) (by simpa using congrArg (fun w : T × V => w.2) he)
    have hv' : (s z.1,z.2) ≠ (s t,v) := by
      intro he; apply hv; exact Prod.ext (s.injective (congrArg Prod.fst he)) (by simpa using congrArg (fun w : T × V => w.2) he)
    rw [Equiv.swap_apply_of_ne_of_ne hu hv,Equiv.swap_apply_of_ne_of_ne hu' hv']
  unfold wiring
  rw [fibers_update,fibers_swap,← mul_assoc,hc,mul_assoc]

def transport (s : Equiv.Perm T) (σ : T → Equiv.Perm V) (t : T) : ℕ → Equiv.Perm V
  | 0 => 1
  | n+1 => σ ((s^n) t) * transport s σ t n

lemma wiring_pow (s : Equiv.Perm T) (σ : T → Equiv.Perm V) (t : T) (v : V) (n : ℕ) :
    (wiring s σ ^ n) (t,v) = ((s^n) t, transport s σ t n v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',Equiv.Perm.mul_apply,ih,wiring_apply,pow_succ',Equiv.Perm.mul_apply]
    rfl

lemma invariant_propagates {B : Type*} (s : Equiv.Perm T) (σ : T → Equiv.Perm V)
    (c : T × V → B) (hc : ∀ z, c (wiring s σ z) = c z) (t : T) (v : V) (n : ℕ) :
    c ((s^n) t,transport s σ t n v) = c (t,v) := by
  rw [← wiring_pow]
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,hc,ih]

lemma invariant_cut {B : Type*} (s : Equiv.Perm T) (σ : T → Equiv.Perm V)
    (c : T × V → B) (hc : ∀ z, c (wiring s σ z) = c z)
    (t : T) (n : ℕ) (hn : (s^n) t = t) :
    ∀ v, c (t,transport s σ t n v) = c (t,v) := by
  intro v
  simpa only [hn] using invariant_propagates s σ c hc t v n

end Heisenberg.LayeredExchange

namespace Heisenberg.Exposure
variable {T : Type*} [Fintype T]

lemma filtered_cylinder_disintegration (w : T → Bool → ℝ) (M : T → Prop) [DecidablePred M]
    (a : {t // M t} → Bool) (G E : (T → Bool) → Prop)
    (v F : (T → Bool) → ℝ) (q : ℝ)
    (hE : ∀ c, E c ↔ (∀ t : {t // M t}, c t = a t) ∧ G c)
    (hv : ∀ c, E c → v c = q) :
    (∑ c : T → Bool, if E c then productWeight w c * v c * F c else 0) =
      q * productWeight (fun t : {t // M t} => w t) a *
        ∑ c : {t // ¬M t} → Bool, if G (merge M a c) then
          productWeight (fun t : {t // ¬M t} => w t) c * F (merge M a c) else 0 := by
  classical
  let e := Equiv.piEquivPiSubtypeProd M (fun _ => Bool)
  rw [← e.symm.sum_comp,Fintype.sum_prod_type]
  have he (a' : {t // M t} → Bool) (c : {t // ¬M t} → Bool) :
      E (e.symm (a',c)) ↔ a' = a ∧ G (e.symm (a',c)) := by
    rw [hE]
    change (∀ t : {t // M t}, merge M a' c t = a t) ∧ _ ↔ _
    simp only [merge_left,funext_iff]
  rw [Finset.sum_eq_single a]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    change (if E (merge M a c) then productWeight w (merge M a c) * v (merge M a c) * F (merge M a c) else 0) = _
    have hh : E (merge M a c) ↔ G (merge M a c) := by
      simpa only [e,merge,eq_self_iff_true,true_and] using he a c
    by_cases hg : G (merge M a c)
    · rw [ite_eq_left (hh.mpr hg),ite_eq_left hg,hv _ (hh.mpr hg),productWeight_merge]
      ring
    · rw [ite_eq_right (hh.not.mpr hg),ite_eq_right hg,mul_zero]
  · intro a' _ hne
    apply Finset.sum_eq_zero
    intro c _
    exact ite_eq_right (fun h => hne ((he a' c).mp h).1)
  · simp

end Heisenberg.Exposure
end

end OAI

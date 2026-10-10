import OAI.Probability.ClassicalON.FamilyLower

namespace OAI

universe uE uI uV

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace ClassicalON.SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

omit [Fintype I] in
def complexSecondBilin (S : SpinSystem 3 V E) : (E → ℂ) →ₗ[ℂ] (E → ℂ) →ₗ[ℂ] ℂ where
  toFun u := {
    toFun := S.complexSecondResponse u
    map_add' := S.complexSecondResponse_add_right u
    map_smul' := fun r v => by simpa only [smul_eq_mul, RingHom.id_apply] using S.complexSecondResponse_smul_right u v r }
  map_add' u v := by ext w; exact S.complexSecondResponse_add_left u v w
  map_smul' r u := by
    ext v
    change S.complexSecondResponse (r • u) v = r * S.complexSecondResponse u v
    exact S.complexSecondResponse_smul_left u v r

omit [Fintype I] in
@[simp] theorem complexSecondResponse_neg_neg (S : SpinSystem 3 V E) (u v : E → ℂ) :
    S.complexSecondResponse (-u) (-v) = S.complexSecondResponse u v := by
  change S.complexSecondBilin (-u) (-v) = S.complexSecondBilin u v
  simp

omit [Fintype V] [Fintype E] [Fintype I] in
theorem commutatorForm_antisymm (S : SpinSystem 3 V E) (f g : V → ℂ) :
    S.commutatorForm g f = -S.commutatorForm f g := by
  ext e
  simp only [commutatorForm, complexCross, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype V] [Fintype E] [Fintype I] in
theorem commutatorForm_conj (S : SpinSystem 3 V E) (f g : V → ℂ) :
    S.commutatorForm (fun x => conj (f x)) (fun x => conj (g x)) =
      (fun e => conj (S.commutatorForm f g e)) := by
  ext e
  simp only [commutatorForm, complexCross, Pi.smul_apply, smul_eq_mul,
    map_mul, map_sub, map_div₀, map_one, map_ofNat]

omit [Fintype I] in
theorem commutatorForm_bound_right (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f g : V → ℂ) (hP : ∀ x s, S.pin x = some s → g x = 0) :
    -(S.complexSecondResponse (S.commutatorForm f g)
      (fun e => conj (S.commutatorForm f g e))).re ≤
        β*(‖g‖^2*∑ e, ‖S.differential f e‖^2) := by
  have h := S.commutatorForm_bound_left β hβ hb g f hP
  rw [S.commutatorForm_antisymm] at h
  have hc : (fun e => conj ((-S.commutatorForm f g) e)) =
      -(fun e => conj (S.commutatorForm f g e)) := by
    ext e; simp only [Pi.neg_apply, map_neg]
  rw [hc, S.complexSecondResponse_neg_neg] at h
  exact h

omit [Fintype I] in
theorem commutatorForm_bound (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f g : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0)
    (hQ : ∀ x s, S.pin x = some s → g x = 0) :
    -(S.complexSecondResponse (S.commutatorForm f g)
      (fun e => conj (S.commutatorForm f g e))).re ≤
        β*min (‖f‖^2*∑ e, ‖S.differential g e‖^2) (‖g‖^2*∑ e, ‖S.differential f e‖^2) := by
  rw [mul_min_of_nonneg _ _ hβ]
  exact le_min (S.commutatorForm_bound_left β hβ hb f g hP)
    (S.commutatorForm_bound_right β hβ hb f g hQ)

omit [Fintype I] in
theorem complexMixedResponse_commutator (S : SpinSystem 3 V E) (f g h k : V → ℂ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    S.complexMixedResponse (S.differential f) (S.differential g)
      (S.differential h) (S.differential k) =
      S.complexSecondResponse (S.commutatorForm f g) (S.commutatorForm h k) +
        S.complexSecondResponse (S.commutatorForm f k) (S.commutatorForm h g) := by
  have hw := S.complexMixedResponse_ward f g h k hf hg hh hk
  simp only [commutatorForm, S.complexSecondResponse_smul_left, S.complexSecondResponse_smul_right]
  linear_combination (1/4 : ℂ) * hw

omit [Fintype I] in
theorem complexMixedResponse_paired (S : SpinSystem 3 V E) (f g : V → ℂ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    S.complexMixedResponse (S.differential f) (fun e => conj (S.differential f e))
      (fun e => conj (S.differential g e)) (S.differential g) =
      S.complexSecondResponse (S.commutatorForm f (fun x => conj (f x)))
        (fun e => conj (S.commutatorForm g (fun x => conj (g x)) e)) -
      S.complexSecondResponse (S.commutatorForm f g) (fun e => conj (S.commutatorForm f g e)) := by
  have hfc : ∀ x s, S.pin x = some s → conj (f x) = 0 := by
    intro x s hs; rw [hf x s hs, map_zero]
  have hgc : ∀ x s, S.pin x = some s → conj (g x) = 0 := by
    intro x s hs; rw [hg x s hs, map_zero]
  have h := S.complexMixedResponse_commutator f (fun x => conj (f x))
    (fun x => conj (g x)) g hf hfc hgc hg
  have df (a : V → ℂ) : S.differential (fun x => conj (a x)) =
      fun e => conj (S.differential a e) := by ext e; simp only [differential, map_sub]
  have cc : S.commutatorForm (fun x => conj (g x)) g =
      (fun e => conj (S.commutatorForm g (fun x => conj (g x)) e)) := by
    simpa only [starRingEnd_self_apply] using S.commutatorForm_conj g (fun x => conj (g x))
  have cd : S.commutatorForm (fun x => conj (g x)) (fun x => conj (f x)) =
      -(fun e => conj (S.commutatorForm f g e)) := by
    rw [S.commutatorForm_antisymm, S.commutatorForm_conj]
  rw [df f, df g, cc, cd] at h
  change S.complexMixedResponse _ _ _ _ = S.complexSecondBilin _ _ + S.complexSecondBilin _ (-_) at h
  simpa only [map_neg, sub_eq_add_neg, complexSecondBilin, LinearMap.coe_mk, AddHom.coe_mk] using h

theorem rotation_family_bound (S : SpinSystem 3 V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, 0 ≤ S.strength e ∧ S.strength e ≤ β)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) :
    -(S.complexSecondResponse (∑ i, S.commutatorForm (f i) (fun x => conj (f i x)))
      (fun e => conj ((∑ i, S.commutatorForm (f i) (fun x => conj (f i x))) e))).re ≤
      (6*β^2+4*β*Real.sqrt β+β) * familyHSSquare (fun i => S.differential (f i)) +
        β*∑ i, ∑ j, min (‖f i‖^2*∑ e, ‖S.differential (f j) e‖^2)
          (‖f j‖^2*∑ e, ‖S.differential (f i) e‖^2) := by
  let Q := ∑ i, S.commutatorForm (f i) (fun x => conj (f i x))
  have hsum : S.complexSecondResponse Q (fun e => conj (Q e)) =
      ∑ i, ∑ j, S.complexSecondResponse (S.commutatorForm (f i) (fun x => conj (f i x)))
        (fun e => conj (S.commutatorForm (f j) (fun x => conj (f j x)) e)) := by
    have hq : (fun e => conj (Q e)) = ∑ i, (fun e => conj (S.commutatorForm (f i) (fun x => conj (f i x)) e)) := by
      ext e; simp only [Q, Finset.sum_apply, map_sum]
    rw [hq]
    change S.complexSecondBilin (∑ i, _) (∑ j, _) = _
    simp only [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    rfl
  have hid : (∑ i, ∑ j, S.complexMixedResponse (S.differential (f i))
      (fun e => conj (S.differential (f i) e)) (fun e => conj (S.differential (f j) e))
        (S.differential (f j))) = S.complexSecondResponse Q (fun e => conj (Q e)) -
      ∑ i, ∑ j, S.complexSecondResponse (S.commutatorForm (f i) (f j))
        (fun e => conj (S.commutatorForm (f i) (f j) e)) := by
    simp only [S.complexMixedResponse_paired _ _ (hP _) (hP _),
      Finset.sum_sub_distrib, hsum]
  have hl := S.fourth_family_lower β hβ hb f hP
  simp only [map_sum] at hl
  have hu : ∑ i, ∑ j, -(S.complexSecondResponse (S.commutatorForm (f i) (f j))
        (fun e => conj (S.commutatorForm (f i) (f j) e))).re ≤
      β*∑ i, ∑ j, min (‖f i‖^2*∑ e, ‖S.differential (f j) e‖^2)
        (‖f j‖^2*∑ e, ‖S.differential (f i) e‖^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      S.commutatorForm_bound β hβ hb (f i) (f j) (hP i) (hP j)
  have hir := congrArg Complex.re hid
  simp only [Complex.sub_re, complexMixedResponse] at hir
  simp only [Complex.re_sum, Finset.sum_neg_distrib] at hir hl hu
  change -(S.complexSecondResponse Q (fun e => conj (Q e))).re ≤ _
  linarith

end ClassicalON.SpinSystem

end

end OAI

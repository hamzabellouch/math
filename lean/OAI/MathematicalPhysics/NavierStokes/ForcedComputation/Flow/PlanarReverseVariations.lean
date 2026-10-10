import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarTransition

namespace OAI

/-! The same variational input controls reverse transitions. No separate
regularity hypothesis for an inverse map is needed. -/

noncomputable section
namespace ForcedComputation
open ShearFlows

theorem second_fderiv_fun_neg (f : Plane → Plane) (x : Plane) :
    fderiv ℝ (fderiv ℝ (fun y => -f y)) x = -(fderiv ℝ (fderiv ℝ f) x) := by
  have he : fderiv ℝ (fun y => -f y) = fun y => -(fderiv ℝ f y) := by
    funext y
    exact fderiv_fun_neg
  rw [he]
  exact fderiv_fun_neg

theorem PlanarVariations.reverse {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ) :
    PlanarVariations (fun s x => -V (-s) x) (fun a t => Ψ (-a) (-t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    simpa only [neg_zero] using hv.initial (-a)
  · intro a t
    exact hv.smooth (-a) (-t)
  · intro a x v t
    have hd := (hv.first (-a) x v (-t)).scomp t (hasDerivAt_id t).neg
    simpa only [Function.comp_def, neg_one_smul, fderiv_fun_neg, fderiv_neg,
      Pi.neg_apply, neg_apply, neg_add] using hd
  · intro a x v w t
    have hd := (hv.second (-a) x v w (-t)).scomp t (hasDerivAt_id t).neg
    simpa only [Function.comp_def, neg_one_smul, second_fderiv_fun_neg, fderiv_fun_neg, fderiv_neg,
      Pi.neg_apply, neg_apply, neg_add] using hd

theorem planar_first_variation_reverse {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ)
    {K : ℝ} (hb : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (a : ℝ) (x : Plane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ a (-t)) x‖ ≤ Real.exp (K * t) := by
  have h := planar_first_variation_operator hv.reverse
    (fun s y => by simpa only [fderiv_fun_neg, norm_neg] using hb (-s) y) (-a) x ht
  simpa only [neg_neg] using h

theorem planar_second_variation_reverse {V : ℝ → Plane → Plane}
    {Ψ : ℝ → ℝ → Plane → Plane} (hv : PlanarVariations V Ψ)
    {K : ℝ} (hK : 0 < K)
    (hb₁ : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (hb₂ : ∀ a x, ‖fderiv ℝ (fderiv ℝ (V a)) x‖ ≤ K)
    (a : ℝ) (x : Plane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (Ψ a (-t))) x‖ ≤
      Real.exp (4 * K * t) - Real.exp (2 * K * t) := by
  have hb₂' (s : ℝ) (y : Plane) :
      ‖fderiv ℝ (fderiv ℝ (fun x => -V (-s) x)) y‖ ≤ K := by
    have he := second_fderiv_fun_neg (V (-s)) y
    have hn := norm_neg (fderiv ℝ (fderiv ℝ (V (-s))) y)
    exact (congrArg norm he).le.trans (hn.le.trans (hb₂ (-s) y))
  have h := planar_second_variation_operator hv.reverse hK
    (fun s y => by simpa only [fderiv_fun_neg, norm_neg] using hb₁ (-s) y)
    hb₂' (-a) x ht
  simpa only [neg_neg] using h

theorem planar_inverse_estimates {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {Ψ : ℝ → ℝ → Plane → Plane}
    (hv : PlanarVariations (planarSlice H) Ψ) (a : ℝ) (x : Plane) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ (a + t) (-t)) x‖ ≤ Real.exp ((planarFlowBound H : ℝ) * t) ∧
      ‖fderiv ℝ (fderiv ℝ (Ψ (a + t) (-t))) x‖ ≤
        Real.exp (2 * (planarFlowBound H : ℝ) * t) -
          Real.exp ((planarFlowBound H : ℝ) * t) := by
  have hK : (0 : ℝ) < planarVariationCoefficient H := by
    exact_mod_cast planarVariationCoefficient_pos H
  have hb₁ := fun s y => (planar_derivative_bounds hH hT s y).1
  have hb₂ := fun s y => (planar_derivative_bounds hH hT s y).2
  constructor
  · apply (planar_first_variation_reverse hv hb₁ (a + t) x ht).trans
    apply Real.exp_le_exp.mpr
    simp only [planarFlowBound, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  · have h := planar_second_variation_reverse hv hK hb₁ hb₂ (a + t) x ht
    simp only [planarFlowBound, Nat.cast_mul, Nat.cast_ofNat]
    rw [show 2 * (2 * (planarVariationCoefficient H : ℝ)) * t =
      4 * (planarVariationCoefficient H : ℝ) * t by ring]
    exact h

end ForcedComputation

end

end OAI

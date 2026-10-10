import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.EuclideanVariations

namespace OAI

/-! The same variational input controls reverse transitions. No separate
regularity hypothesis for an inverse map is needed. -/

noncomputable section
namespace ForcedComputation
open ShearFlows

theorem euclidean_second_fderiv_fun_neg (f : EuclideanPlane → EuclideanPlane) (x : EuclideanPlane) :
    fderiv ℝ (fderiv ℝ (fun y => -f y)) x = -(fderiv ℝ (fderiv ℝ f) x) := by
  have he : fderiv ℝ (fun y => -f y) = fun y => -(fderiv ℝ f y) := by
    funext y
    exact fderiv_fun_neg
  rw [he]
  exact fderiv_fun_neg

theorem EuclideanVariations.reverse {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ) :
    EuclideanVariations (fun s x => -V (-s) x) (fun a t => Ψ (-a) (-t)) := by
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
    simpa only [Function.comp_def, neg_one_smul, euclidean_second_fderiv_fun_neg, fderiv_fun_neg, fderiv_neg,
      Pi.neg_apply, neg_apply, neg_add] using hd

theorem euclidean_first_variation_reverse {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ)
    {K : ℝ} (hb : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (a : ℝ) (x : EuclideanPlane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ a (-t)) x‖ ≤ Real.exp (K * t) := by
  have h := euclidean_first_variation_operator hv.reverse
    (fun s y => by simpa only [fderiv_fun_neg, norm_neg] using hb (-s) y) (-a) x ht
  simpa only [neg_neg] using h

theorem euclidean_second_variation_reverse {V : ℝ → EuclideanPlane → EuclideanPlane}
    {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane} (hv : EuclideanVariations V Ψ)
    {K : ℝ} (hK : 0 < K)
    (hb₁ : ∀ a x, ‖fderiv ℝ (V a) x‖ ≤ K)
    (hb₂ : ∀ a x, ‖fderiv ℝ (fderiv ℝ (V a)) x‖ ≤ K)
    (a : ℝ) (x : EuclideanPlane) {t : ℝ} (ht : 0 ≤ t) :
    ‖fderiv ℝ (fderiv ℝ (Ψ a (-t))) x‖ ≤
      Real.exp (4 * K * t) - Real.exp (2 * K * t) := by
  have hb₂' (s : ℝ) (y : EuclideanPlane) :
      ‖fderiv ℝ (fderiv ℝ (fun x => -V (-s) x)) y‖ ≤ K := by
    have he := euclidean_second_fderiv_fun_neg (V (-s)) y
    have hn := norm_neg (fderiv ℝ (fderiv ℝ (V (-s))) y)
    exact (congrArg norm he).le.trans (hn.le.trans (hb₂ (-s) y))
  have h := euclidean_second_variation_operator hv.reverse hK
    (fun s y => by simpa only [fderiv_fun_neg, norm_neg] using hb₁ (-s) y)
    hb₂' (-a) x ht
  simpa only [neg_neg] using h

theorem euclidean_inverse_estimates {H : FieldExpr} (hH : H.Valid)
    (hT : SpatialExpression.NoTime H) {Ψ : ℝ → ℝ → EuclideanPlane → EuclideanPlane}
    (hv : EuclideanVariations (fun s => euclideanMap (planarSlice H s)) Ψ) (a : ℝ) (x : EuclideanPlane) {t : ℝ}
    (ht : 0 ≤ t) :
    ‖fderiv ℝ (Ψ (a + t) (-t)) x‖ ≤ Real.exp ((euclideanFlowBound H : ℝ) * t) ∧
      ‖fderiv ℝ (fderiv ℝ (Ψ (a + t) (-t))) x‖ ≤
        Real.exp (2 * (euclideanFlowBound H : ℝ) * t) -
          Real.exp ((euclideanFlowBound H : ℝ) * t) := by
  have hK : (0 : ℝ) < euclideanVariationCoefficient H := by
    have hp := planarVariationCoefficient_pos H
    unfold euclideanVariationCoefficient
    exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hp
  have hb₁ := fun s y => (planar_euclidean_derivative_bounds hH hT s y).1
  have hb₂ := fun s y => (planar_euclidean_derivative_bounds hH hT s y).2
  constructor
  · apply (euclidean_first_variation_reverse hv hb₁ (a + t) x ht).trans
    apply Real.exp_le_exp.mpr
    simp only [euclideanFlowBound, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  · have h := euclidean_second_variation_reverse hv hK hb₁ hb₂ (a + t) x ht
    simp only [euclideanFlowBound, Nat.cast_mul, Nat.cast_ofNat]
    rw [show 2 * (2 * (euclideanVariationCoefficient H : ℝ)) * t =
      4 * (euclideanVariationCoefficient H : ℝ) * t by ring]
    exact h

end ForcedComputation

end

end OAI

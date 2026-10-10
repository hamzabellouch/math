import OAI.Analysis.CircleDomains.Modulus.WeightedInversePieceCurve
import OAI.Analysis.CircleDomains.Sobolev.ComplexCoareaJacobian

namespace OAI

/-! The exact inverse Jacobian on a measurable scalar level-coordinate piece. -/
open Set Function Filter MeasureTheory
open scoped Topology NNReal ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma inverse_piece_jacobian {F : ℂ → ℂ} {f : ℂ → ℝ} {S : Set ℂ}
    (he : ∀ z, (F z).re = f z) (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    {y : ℂ} (hy : y ∈ F '' S) :
    ‖fderiv ℝ f (invFunOn F S y)‖ * |((fderiv ℝ F (invFunOn F S y)).inverse).det| =
      ‖(fderiv ℝ F (invFunOn F S y)).inverse Complex.I‖ := by
  let x := invFunOn F S y
  have hx : x ∈ S := invFunOn_mem hy
  have hf : HasFDerivAt f (Complex.reCLM.comp (fderiv ℝ F x)) x :=
    (Complex.reCLM.hasFDerivAt.comp x (hd x hx).hasFDerivAt).congr_of_eventuallyEq
      (Eventually.of_forall fun z => (he z).symm)
  have hdf : fderiv ℝ f x = Complex.reCLM.comp (fderiv ℝ F x) := hf.fderiv
  apply coarea_covector_jacobian
  · rw [hdf, ContinuousLinearMap.comp_apply, (hi x hx).self_apply_inverse]
    simp
  · rw [hdf, ContinuousLinearMap.comp_apply, (hi x hx).self_apply_inverse]
    simp

 def inversePieceWeight (F : ℂ → ℂ) (S T : Set ℂ) (q : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  T.indicator (fun y => q (invFunOn F S y) *
    ENNReal.ofReal ‖(fderiv ℝ F (invFunOn F S y)).inverse Complex.I‖)

lemma measurable_inversePieceWeight {F : ℂ → ℂ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (hT : MeasurableSet T) (hTS : T ⊆ F '' S)
    {q : ℂ → ℝ≥0∞} (hq : Measurable q) : Measurable (inversePieceWeight F S T q) := by
  have hm := ((hq.comp (measurable_inverseOnPiece hF hT hTS)).mul
    (((ContinuousLinearMap.measurable_apply Complex.I).comp
      (measurable_inversePieceDifferential hF hT hTS)).norm.ennreal_ofReal)).indicator hT
  convert hm using 1
  funext y
  by_cases hy : y ∈ T
  · simp only [inversePieceWeight, indicator_of_mem hy, Pi.mul_apply, Function.comp_def, inverseOnPiece_eq hy]
  · simp only [inversePieceWeight, indicator_of_notMem hy]

lemma inverse_piece_energy_eq {F : ℂ → ℂ} {f : ℂ → ℝ} {S T : Set ℂ} {K : ℝ≥0}
    (hF : AntilipschitzWith K (S.domRestrict F)) (he : ∀ z, (F z).re = f z)
    (hd : ∀ x ∈ S, DifferentiableAt ℝ F x)
    (hi : ∀ x ∈ S, (fderiv ℝ F x).IsInvertible)
    (hT : MeasurableSet T) (hTS : T ⊆ F '' S) (q : ℂ → ℝ≥0∞) :
    (∫⁻ z in (invFunOn F S) '' T, q z*ENNReal.ofReal ‖fderiv ℝ f z‖) =
      ∫⁻ y, inversePieceWeight F S T q y := by
  have hder : ∀ y ∈ T, HasFDerivWithinAt (invFunOn F S)
      (fderiv ℝ F (invFunOn F S y)).inverse T y :=
    fun y hy => (inverseOn_derivative_field hF hd hi (hTS hy)).mono hTS
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hT hder (inverseOn_injOn.mono hTS),
    inversePieceWeight, lintegral_indicator hT]
  apply setLIntegral_congr_fun hT
  intro y hy
  dsimp only
  calc
    ENNReal.ofReal |((fderiv ℝ F (invFunOn F S y)).inverse).det| *
        (q (invFunOn F S y)*ENNReal.ofReal ‖fderiv ℝ f (invFunOn F S y)‖) =
      q (invFunOn F S y)*ENNReal.ofReal
        (‖fderiv ℝ f (invFunOn F S y)‖*|((fderiv ℝ F (invFunOn F S y)).inverse).det|) := by
          rw [ENNReal.ofReal_mul (norm_nonneg _)]
          ac_rfl
    _ = _ := by rw [inverse_piece_jacobian he hd hi (hTS hy)]

end CircleDomainRigidity

end

end OAI

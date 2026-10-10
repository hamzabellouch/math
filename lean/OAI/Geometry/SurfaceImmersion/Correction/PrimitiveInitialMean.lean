import OAI.Geometry.SurfaceImmersion.Correction.PolynomialValueBounds
import OAI.Geometry.SurfaceImmersion.Correction.PrimitiveMeanStep
import OAI.Geometry.Immersion.ClosedSurface.MetricTensors

namespace OAI

/-! The actual scalar contraction starts the primitive mean iteration.
Its normalized defect is only the polynomial perturbation divided by δ². -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.PrimitiveRealization
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PhaseMean

def primitiveSeed (δ : ℝ) (F : JetPolynomial.Base → JetPolynomial.Space) :
    JetPolynomial.Base → JetPolynomial.Space := fun x => Real.sqrt (1-δ^2) • F x

lemma primitiveSeed_smooth (δ : ℝ) {F : JetPolynomial.Base → JetPolynomial.Space}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (primitiveSeed δ F) := hF.const_smul _

lemma realMetricTensor_const_smul {F : RealModes.RField 4}
    (hF : ContDiff ℝ ∞ F) (a : ℝ) :
    RealModes.realMetricTensor (fun x => a • F x) =
      fun x => a^2 • RealModes.realMetricTensor F x := by
  have hd (p v : SmallModes.Base) : SmallModes.coordDeriv v (fun x => a • F x) p =
      a • SmallModes.coordDeriv v F p := by
    change (fderiv ℝ (fun x => a • F x) p) v = a • (fderiv ℝ F p) v
    rw [fderiv_fun_const_smul (hF.differentiable (by simp) p),smul_apply]
  ext x k
  simp only [RealModes.realMetricTensor_apply,RealModes.realMetric,hd,Pi.smul_apply,
    smul_dotProduct,dotProduct_smul,smul_eq_mul]
  ring

lemma primitiveSeed_metric {F : JetPolynomial.Base → JetPolynomial.Space}
    (hF : ContDiff ℝ ∞ F) {δ : ℝ} (hδ : δ^2 ≤ 1) :
    RealModes.realMetricTensor (primitiveSeed δ F ∘ planeCoordinateIsometry.symm) =
      fun x => (1-δ^2) • RealModes.realMetricTensor (F ∘ planeCoordinateIsometry.symm) x := by
  have hh := realMetricTensor_const_smul (hF.comp planeCoordinateIsometry.symm.contDiff)
    (Real.sqrt (1-δ^2))
  rw [Real.sq_sqrt (sub_nonneg.mpr hδ)] at hh
  exact hh

lemma primitiveSeed_defect {n : ℕ} (P : Fin 3 → Fin n → Expression) (ε : ℝ)
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    {δ : ℝ} (hδ : δ ≠ 0) (hδ1 : δ^2 ≤ 1) :
    normalizedMeanDefect δ (RealModes.realMetricTensor (F ∘ planeCoordinateIsometry.symm))
      (coordinateMetricMap P ε (primitiveSeed δ F)) =
        fun x => (-(δ^2)⁻¹) • coordinatePolynomialValue P ε (primitiveSeed δ F) 0 x := by
  ext x k
  simp only [normalizedMeanDefect,coordinateMetricMap,primitiveSeed_metric hF hδ1,
    Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  field_simp
  ring

theorem primitiveSeed_defect_bound {n : ℕ} {Q : Set LowJet} (hQ : IsCompact Q)
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    (m : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set JetPolynomial.Base), IsOpen U →
      ∀ {F : JetPolynomial.Base → JetPolynomial.Space}, ContDiff ℝ ∞ F →
      ∀ (δ ε : ℝ), δ ≠ 0 → δ^2 ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      Set.MapsTo (lowJet (primitiveSeed δ F)) U Q →
      WeightedBound U 1 (m + tensorOrder P) B (lowJet (primitiveSeed δ F)) →
      WeightedBound (planeCoordinateIsometry.symm ⁻¹' U) 1 m (C*ε/δ^2)
        (normalizedMeanDefect δ (RealModes.realMetricTensor (F ∘ planeCoordinateIsometry.symm))
          (coordinateMetricMap P ε (primitiveSeed δ F))) := by
  obtain ⟨C,hC,hb⟩ := coordinatePolynomialValue_bound hQ P hP m B hB
  refine ⟨C,hC,?_⟩
  intro U hU F hF δ ε hδ hδ1 hε hε1 hGQ hGb
  have hSeed := primitiveSeed_smooth δ hF
  have hvalue := hb U hU hSeed hGQ 1 ε zero_lt_one le_rfl hε hε1 hGb
  have hvalueS := coordinatePolynomialValue_smooth hP hSeed ε
  have hscaled := hvalue.const_smul (hU.preimage planeCoordinateIsometry.symm.continuous).uniqueDiffOn
    hvalueS.contDiffOn (-(δ^2)⁻¹)
  have hc : |-(δ^2)⁻¹| * (C*ε/1^tensorLoss P) = C*ε/δ^2 := by
    rw [abs_neg,abs_of_pos (inv_pos.mpr (sq_pos_of_ne_zero hδ))]
    simp only [one_pow,div_one]
    ring
  rw [hc]
    at hscaled
  exact hscaled.congr (fun x _ => congrFun (primitiveSeed_defect P ε hF hδ hδ1) x)

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI

import OAI.Analysis.StrictMeans.AreaTransport

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

def AffineProbabilityLaw (μ : ProbabilityMeasure DiskFamily) (β : ℝ) : Prop :=
  ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
    (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily)

def spatialWeight (β : ℝ) (f : DiskFamily) (z : UpperHalfPlane) : ℝ≥0∞ :=
  ENNReal.ofReal (z.im^(β-1) * ‖halfPlaneQ f z‖)

lemma continuous_spatialWeight (β : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => spatialWeight β p.1 p.2) := by
  exact ENNReal.continuous_ofReal.comp
    (((UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const
      (fun p => Or.inl p.2.im_ne_zero)).mul continuous_halfPlaneQ.norm)

lemma spatialWeight_eq (β : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    spatialWeight β f z = ENNReal.ofReal (z.im^(β-1)) * (‖halfPlaneQ f z‖₊ : ℝ≥0∞) := by
  rw [spatialWeight,ENNReal.ofReal_mul (Real.rpow_nonneg z.im_pos.le _)]
  simp [enorm_eq_nnnorm]

lemma law_spatialWeight (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : AffineProbabilityLaw μ β) (z : UpperHalfPlane)
    {φ : DiskFamily → ℝ≥0∞} (hφ : Measurable φ) :
    (∫⁻ f, spatialWeight β f z * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (z.im⁻¹) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily) := by
  simp only [spatialWeight_eq,mul_assoc]
  have hm : Measurable (fun f => (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z)) :=
    (measurable_Qnorm_fixed z).coe_nnreal_ennreal.mul (hφ.comp (measurable_rebase_fixed z))
  rw [lintegral_const_mul (μ := (μ : Measure DiskFamily)) (ENNReal.ofReal (z.im^(β-1))) hm,
    hlaw z φ hφ,← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg z.im_pos.le _),← Real.rpow_add z.im_pos]
  congr 1
  rw [show β-1+-β = -(1:ℝ) by ring,Real.rpow_neg_one]

lemma spatialWeight_jacobianPart (β k : ℝ) (f : DiskFamily) (positive : Bool) (z : UpperHalfPlane) :
    spatialWeight β f z * ENNReal.ofReal (jacobianPart k f positive z) =
      sourceMassDensity β k f positive z := by
  rw [spatialWeight,sourceMassDensity,
    ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg z.im_pos.le _) (norm_nonneg _))]

lemma jacobianPart_rebase (k : ℝ) (f : DiskFamily) (t w : UpperHalfPlane) (positive : Bool) :
    jacobianPart k (rebase f t) positive w = jacobianPart k f positive (affineProduct t w) := by
  simp only [jacobianPart,jacobianExpression_rebase,coe_affineProduct]

@[simp] lemma affineProduct_I (z : UpperHalfPlane) : affineProduct z UpperHalfPlane.I = z := by
  apply UpperHalfPlane.ext
  simp only [coe_affineProduct,UpperHalfPlane.coe_I,affineAt]
  exact z.1.re_add_im

lemma law_sourceMassDensity (μ : ProbabilityMeasure DiskFamily) (β k : ℝ)
    (hlaw : AffineProbabilityLaw μ β) (positive : Bool)
    {H : DiskFamily × UpperHalfPlane → ℝ≥0∞} (hH : Measurable H)
    (hcov : ∀ f z, H (f,z) = H (rebase f z,UpperHalfPlane.I)) (z : UpperHalfPlane) :
    (∫⁻ f, sourceMassDensity β k f positive z * H (f,z) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (z.im⁻¹) * ∫⁻ f,
        ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) * H (f,UpperHalfPlane.I)
        ∂(μ : Measure DiskFamily) := by
  let φ : DiskFamily → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) * H (f,UpperHalfPlane.I)
  have hφ : Measurable φ :=
    ((continuous_jacobianPart k positive).measurable.comp
      (measurable_id.prodMk measurable_const)).ennreal_ofReal.mul
      (hH.comp (measurable_id.prodMk measurable_const))
  have he (f : DiskFamily) : sourceMassDensity β k f positive z * H (f,z) =
      spatialWeight β f z * φ (rebase f z) := by
    rw [← spatialWeight_jacobianPart,hcov]
    simp only [φ,jacobianPart_rebase,affineProduct_I,mul_assoc]
  simp_rw [he]
  exact law_spatialWeight μ β hlaw z hφ

end
end StrictInverseFirstPower

end

end OAI

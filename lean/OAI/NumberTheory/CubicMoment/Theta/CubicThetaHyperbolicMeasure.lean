import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHyperbolicIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFundamentalDomain
import Mathlib.MeasureTheory.Measure.WithDensity

namespace OAI

/-! The actual invariant hyperbolic measure on positive-height points.
Its density is v^-3, and arithmetic invariance follows from the proved
Jacobian, not from an assumed invariant measure. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ENNReal
namespace CubicFirstMoment

local instance cubicThetaHyperbolicMeasure_volumeHaar :
    (volume : Measure (ℂ × ℝ)).IsAddHaarMeasure := by
  change ((volume : Measure ℂ).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

def cubicThetaHyperbolicDensity (p : ℂ × ℝ) : ℝ≥0∞ := ENNReal.ofReal ((p.2^3)⁻¹)

def cubicThetaHyperbolicMeasure : Measure (ℂ × ℝ) :=
  volume.withDensity cubicThetaHyperbolicDensity

lemma cubicThetaHyperbolicDensity_transform (g : SL(2,ℂ)) {p : ℂ × ℝ} (hp : 0<p.2) :
    ENNReal.ofReal |(fderiv ℝ (cubicThetaMobius g) p).toLinearMap.det| *
      cubicThetaHyperbolicDensity (cubicThetaMobius g p)=cubicThetaHyperbolicDensity p := by
  unfold cubicThetaHyperbolicDensity
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  apply congrArg ENNReal.ofReal
  simpa only [div_eq_mul_inv,one_mul] using cubicThetaMobius_volume_density g hp

lemma cubicThetaHyperbolic_lintegral_change (g : SL(2,ℂ)) {S : Set (ℂ × ℝ)}
    (hS : MeasurableSet S) (hpos : ∀ p∈S,0<p.2) (F : ℂ × ℝ → ℝ≥0∞) :
    (∫⁻ p in cubicThetaMobius g '' S, cubicThetaHyperbolicDensity p*F p)=
      ∫⁻ p in S, cubicThetaHyperbolicDensity p*F (cubicThetaMobius g p) := by
  have hD : ∀ p∈S, HasFDerivWithinAt (cubicThetaMobius g)
      (fderiv ℝ (cubicThetaMobius g) p) S p := by
    intro p hp
    exact ((cubicThetaMobius_contDiffAt g (hpos p hp)).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hD
    ((cubicThetaMobius_injOn g).mono hpos)]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hS] with p hp
  rw [← mul_assoc,cubicThetaHyperbolicDensity_transform g (hpos p hp)]

lemma cubicThetaHyperbolicMeasure_image (g : SL(2,ℂ)) {S : Set (ℂ × ℝ)}
    (hS : MeasurableSet S) (hpos : ∀ p∈S,0<p.2) :
    cubicThetaHyperbolicMeasure (cubicThetaMobius g '' S)=cubicThetaHyperbolicMeasure S := by
  unfold cubicThetaHyperbolicMeasure
  rw [withDensity_apply',withDensity_apply']
  simpa only [mul_one] using cubicThetaHyperbolic_lintegral_change g hS hpos (fun _ => 1)

def cubicThetaPointCoordinates (p : CubicThetaPoint) : ℂ × ℝ := p.val

lemma cubicThetaPointInclusion_measurableEmbedding :
    MeasurableEmbedding cubicThetaPointCoordinates := by
  apply Topology.IsOpenEmbedding.measurableEmbedding
  change Topology.IsOpenEmbedding (Subtype.val : {p : ℂ × ℝ // 0<p.2} → ℂ × ℝ)
  exact (isOpen_lt continuous_const continuous_snd).isOpenEmbedding_subtypeVal

def cubicThetaPointMeasure : Measure CubicThetaPoint :=
  cubicThetaHyperbolicMeasure.comap cubicThetaPointCoordinates

lemma cubicThetaPointMeasure_apply {S : Set CubicThetaPoint} (hS : MeasurableSet S) :
    cubicThetaPointMeasure S=cubicThetaHyperbolicMeasure (cubicThetaPointCoordinates '' S) :=
  Measure.comap_apply _ cubicThetaPointInclusion_measurableEmbedding.injective
    (fun _ hs => cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hs) _ hS

lemma cubicThetaPointMeasure_image (g : SL(2,Eisenstein)) {S : Set CubicThetaPoint}
    (hS : MeasurableSet S) :
    cubicThetaPointMeasure ((fun p => g • p) '' S)=cubicThetaPointMeasure S := by
  have hI : MeasurableSet ((fun p : CubicThetaPoint => g • p) '' S) :=
    (Homeomorph.smul g).measurableEmbedding.measurableSet_image' hS
  rw [cubicThetaPointMeasure_apply hI,cubicThetaPointMeasure_apply hS]
  have he : cubicThetaPointCoordinates '' ((fun p : CubicThetaPoint => g • p) '' S)=
      cubicThetaMobius (cubicThetaFullComplex g) '' (cubicThetaPointCoordinates '' S) := by
    rw [image_image,image_image]
    rfl
  rw [he]
  apply cubicThetaHyperbolicMeasure_image _
    (cubicThetaPointInclusion_measurableEmbedding.measurableSet_image' hS)
  rintro p ⟨q,_,rfl⟩
  exact q.property

instance cubicThetaPointMeasure_invariant :
    SMulInvariantMeasure SL(2,Eisenstein) CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g S hS := by
    have he : (fun p : CubicThetaPoint => g • p) ⁻¹' S=(fun p => g⁻¹ • p) '' S := by
      ext p
      constructor
      · intro hp
        exact ⟨g • p,hp,inv_smul_smul g p⟩
      · rintro ⟨q,hq,rfl⟩
        change g • (g⁻¹ • q)∈S
        rwa [smul_inv_smul]
    rw [he]
    exact cubicThetaPointMeasure_image g⁻¹ hS

def cubicThetaQuotientMeasure : Measure CubicThetaQuotient :=
  (cubicThetaPointMeasure.restrict cubicThetaFundamentalDomain).map cubicThetaQuotientMap

end CubicFirstMoment

end

end OAI

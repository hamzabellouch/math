import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticCuspMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspNeighborhoodCover
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalL2

namespace OAI

/-! The cusp estimates and finite arithmetic core cover put the literal
Eisenstein remainder in the actual global L2 space. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaCuspNeighborhood_integrable_iff
    (δ : SL(2,Eisenstein)) {H : ℝ} (hH : 1≤H)
    {f : CubicThetaQuotient → ℝ} (hf : Continuous f) :
    IntegrableOn f (cubicThetaCuspNeighborhood δ H) cubicThetaQuotientMeasure ↔
      IntegrableOn (fun p => f (cubicThetaQuotientMap (δ • p)))
        (cubicThetaCuspStrip H) cubicThetaPointMeasure := by
  unfold cubicThetaCuspNeighborhood IntegrableOn
  rw [← cubicThetaInjective_map_restrict (cubicThetaTranslatedCuspStrip_measurable δ H)
    (cubicThetaTranslatedCuspStrip_injective δ hH)]
  rw [integrable_map_measure hf.aestronglyMeasurable
    cubicThetaQuotientMap_open.continuous.measurable.aemeasurable]
  change Integrable (fun p => f (cubicThetaQuotientMap p))
    (cubicThetaPointMeasure.restrict ((fun p : CubicThetaPoint => δ • p) '' cubicThetaCuspStrip H)) ↔ _
  rw [← cubicThetaSmul_map_restrict δ (cubicThetaCuspStrip_measurable H)]
  exact integrable_map_measure
    (hf.comp cubicThetaQuotientMap_open.continuous).aestronglyMeasurable
    (measurable_const_smul δ).aemeasurable

lemma cubicThetaArithmeticSection_cusp_mass_integrable
    (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3<s.re) :
    IntegrableOn (fun q => cubicThetaSectionNorm (cubicThetaArithmeticSection s (by linarith)) q^2)
      (cubicThetaCuspNeighborhood δ 2) cubicThetaQuotientMeasure := by
  have hf : Continuous (fun q =>
      cubicThetaSectionNorm (cubicThetaArithmeticSection s (by linarith)) q^2) :=
    (cubicThetaSectionNorm_continuous _).pow 2
  apply (cubicThetaCuspNeighborhood_integrable_iff δ (by norm_num) hf).mpr
  have h := cubicThetaArithmeticRemainder_cusp_mass_integrable δ hs
  rw [← cubicThetaCuspStrip_coordinates (by norm_num : (0:ℝ)≤2),
    ← cubicThetaPointIntegrable_density (cubicThetaCuspStrip_measurable 2)] at h
  simpa only [cubicThetaArithmeticSection_norm,cubicThetaFullPointAction_apply,cubicThetaPointCoordinates] using h

theorem cubicThetaArithmeticSection_mass_integrable {s : ℂ} (hs : 3<s.re) :
    Integrable (fun q => cubicThetaSectionNorm (cubicThetaArithmeticSection s (by linarith)) q^2)
      cubicThetaQuotientMeasure := by
  obtain ⟨S,hS⟩ := cubicThetaCuspNeighborhood_cover
  have hf : Continuous (fun q =>
      cubicThetaSectionNorm (cubicThetaArithmeticSection s (by linarith)) q^2) :=
    (cubicThetaSectionNorm_continuous _).pow 2
  have hc := hf.continuousOn.integrableOn_compact (μ:=cubicThetaQuotientMeasure) (cubicThetaQuotientCore_compact S 2)
  have hu : IntegrableOn
      (fun q => cubicThetaSectionNorm (cubicThetaArithmeticSection s (by linarith)) q^2)
      (⋃ δ∈S,cubicThetaCuspNeighborhood δ⁻¹ 2) cubicThetaQuotientMeasure :=
    integrableOn_finset_iUnion.mpr (fun δ _ => cubicThetaArithmeticSection_cusp_mass_integrable δ⁻¹ hs)
  have h := hc.union hu
  rwa [hS 2,integrableOn_univ] at h

lemma cubicThetaArithmeticSection_memLp {s : ℂ} (hs : 3<s.re) :
    MemLp (cubicThetaSectionRepresentative (cubicThetaArithmeticSection s (by linarith)))
      2 cubicThetaQuotientMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (cubicThetaSectionRepresentative_measurable _).aestronglyMeasurable).mpr
  simpa only [cubicThetaSectionRepresentative_norm] using cubicThetaArithmeticSection_mass_integrable hs

def cubicThetaArithmeticL2 (s : ℂ) (hs : 3<s.re) : CubicThetaGlobalL2 :=
  (cubicThetaArithmeticSection_memLp hs).toLp _

lemma cubicThetaArithmeticL2_coe (s : ℂ) (hs : 3<s.re) :
    cubicThetaArithmeticL2 s hs =ᵐ[cubicThetaQuotientMeasure]
      cubicThetaSectionRepresentative (cubicThetaArithmeticSection s (by linarith)) :=
  (cubicThetaArithmeticSection_memLp hs).coeFn_toLp

end CubicFirstMoment

end

end OAI

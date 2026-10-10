import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarHeightSeed
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaModelRankinLimit

namespace OAI

/-! Exact periodization of the positive sharp-height seed times section energy. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaScalarHeightWeight_measurable (s : ℝ) :
    Measurable (cubicThetaScalarHeightWeight s) := by
  unfold cubicThetaScalarHeightWeight
  apply Measurable.ite (measurableSet_le measurable_id measurable_const)
  · fun_prop
  · exact measurable_const

lemma cubicThetaScalarHeightSeed_measurable (s : ℝ) :
    Measurable (cubicThetaScalarHeightSeed s) := by
  apply Measurable.ite (cubicThetaHorizontalCell_measurable.preimage
    (measurable_fst.comp cubicThetaPointInclusion_measurableEmbedding.measurable))
  · exact (cubicThetaScalarHeightWeight_measurable s).comp
      (measurable_snd.comp cubicThetaPointInclusion_measurableEmbedding.measurable)
  · exact measurable_const

lemma cubicThetaSection_norm_invariant (F : CubicThetaSection)
    (γ : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    ‖F.val (γ • p)‖=‖F.val p‖ := by
  rw [F.property]
  rw [norm_mul,cubicThetaKubotaValue_norm,one_mul]

lemma cubicThetaScalarRankinKernel_apply (σ : ℝ) (p : CubicThetaPoint) :
    cubicThetaScalarRankinKernel σ (cubicThetaQuotientMap p)=
      cubicThetaScalarHeightCutoff p.val (2+2*σ) := by
  have he := cubicThetaBorelSection_rightInverse (cubicThetaQuotientMap p)
  obtain ⟨γ,hγ⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaScalarRankinKernel
  rw [←hγ]
  exact cubicThetaScalarHeightCutoff_invariant γ p.property _

def cubicThetaScalarEnergySeed (F : CubicThetaSection) (σ : ℝ) (p : CubicThetaPoint) : ℝ :=
  cubicThetaScalarHeightSeed (2+2*σ) p*‖F.val p‖^2

def cubicThetaScalarEnergyDensity (F : CubicThetaSection) (σ : ℝ)
    (q : CubicThetaQuotient) : ℝ :=
  cubicThetaScalarRankinKernel σ q*‖cubicThetaSectionRepresentative F q‖^2

lemma cubicThetaScalarEnergySeed_nonneg (F : CubicThetaSection) (σ : ℝ)
    (p : CubicThetaPoint) : 0≤cubicThetaScalarEnergySeed F σ p :=
  mul_nonneg (cubicThetaScalarHeightSeed_nonneg _ p) (sq_nonneg _)

lemma cubicThetaScalarEnergyDensity_nonneg (F : CubicThetaSection) (σ : ℝ)
    (q : CubicThetaQuotient) : 0≤cubicThetaScalarEnergyDensity F σ q :=
  mul_nonneg (cubicThetaScalarRankinKernel_nonneg σ q) (sq_nonneg _)

lemma cubicThetaScalarEnergySeed_measurable (F : CubicThetaSection) (σ : ℝ) :
    Measurable (cubicThetaScalarEnergySeed F σ) :=
  (cubicThetaScalarHeightSeed_measurable _).mul (F.val.continuous.norm.pow 2).measurable

lemma cubicThetaScalarEnergyDensity_measurable (F : CubicThetaSection) (σ : ℝ) :
    Measurable (cubicThetaScalarEnergyDensity F σ) :=
  (cubicThetaScalarRankinKernel_measurable σ).mul
    ((cubicThetaSectionRepresentative_measurable F).norm.pow_const 2)

lemma cubicThetaScalarEnergySeed_group_summable (F : CubicThetaSection)
    {σ : ℝ} (hσ : 0<σ) (p : CubicThetaPoint) :
    Summable (fun γ : cubicThetaPrincipalGroup => cubicThetaScalarEnergySeed F σ (γ • p)) := by
  simp only [cubicThetaScalarEnergySeed,cubicThetaSection_norm_invariant]
  exact (cubicThetaScalarHeightSeed_group_summable (by linarith) p).mul_right _

lemma cubicThetaScalarEnergySeed_group_sum (F : CubicThetaSection)
    {σ : ℝ} (hσ : 0<σ) (p : CubicThetaPoint) :
    (∑' γ : cubicThetaPrincipalGroup,cubicThetaScalarEnergySeed F σ (γ • p))=
      cubicThetaScalarEnergyDensity F σ (cubicThetaQuotientMap p) := by
  simp only [cubicThetaScalarEnergySeed,cubicThetaSection_norm_invariant]
  rw [tsum_mul_right,cubicThetaScalarHeightSeed_group_sum (by linarith)]
  unfold cubicThetaScalarEnergyDensity
  rw [cubicThetaScalarRankinKernel_apply]
  congr 1
  have he := cubicThetaBorelSection_rightInverse (cubicThetaQuotientMap p)
  obtain ⟨γ,hγ⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  change ‖F.val p‖^2=‖F.val (cubicThetaBorelSection (cubicThetaQuotientMap p))‖^2
  rw [←hγ,cubicThetaSection_norm_invariant]


end CubicFirstMoment

end

end OAI

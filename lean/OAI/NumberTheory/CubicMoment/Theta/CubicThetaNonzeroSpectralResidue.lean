import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScatteringResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaZeroRadialPositive

namespace OAI

/-! The explicit arithmetic constant term forces a nonzero residue of
the actual global meromorphic family at s=4/3. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaScatteringResidue_ne_zero : cubicThetaScatteringResidue≠0 := by
  apply div_ne_zero
  · exact div_ne_zero principalThetaConstant_ne_zero
      (Complex.ofReal_ne_zero.mpr (residueHeckeScale_pos (q:=1) one_ne_zero).ne')
  · exact mul_ne_zero (by norm_num) cubicTheta_principalZeta_two_ne_zero

lemma cubicThetaSpectralResidue_constant_ne_zero :
    inner ℂ (cubicThetaCuspFourierTest 0 cubicThetaRadialTestWeight)
      (cubicThetaCuspRestriction (cubicThetaArithmeticResidueEnergy (4/3)))≠0 := by
  rw [cubicThetaSpectralResidue_constant_observation]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by norm_num)
    · exact cubicThetaScatteringResidue_ne_zero
  · intro hz
    have hp := cubicThetaZeroRadialTest_real_pos (4/3)
    have hc : ((4/3:ℝ):ℂ)=(4/3:ℂ) := by norm_num
    rw [hc,hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp

theorem cubicThetaArithmeticResidueEnergy_ne_zero :
    cubicThetaArithmeticResidueEnergy (4/3)≠0 := by
  intro hz
  apply cubicThetaSpectralResidue_constant_ne_zero
  rw [hz,map_zero,inner_zero_right]

lemma cubicThetaCuspRestriction_value_bound (u : cubicThetaGlobalEnergySpace) :
    ‖cubicThetaCuspRestriction u‖≤‖cubicThetaGlobalInclusion u‖ := by
  have hc : IsClosed {v : cubicThetaGlobalEnergySpace |
      ‖cubicThetaCuspRestriction v‖≤‖cubicThetaGlobalInclusion v‖} :=
    isClosed_le (continuous_norm.comp cubicThetaCuspRestriction.continuous)
      (continuous_norm.comp cubicThetaGlobalInclusion.continuous)
  have hs : range cubicThetaFiniteEnergyEmbedding⊆
      {v : cubicThetaGlobalEnergySpace | ‖cubicThetaCuspRestriction v‖≤‖cubicThetaGlobalInclusion v‖} := by
    rintro v ⟨F,rfl⟩
    change ‖cubicThetaCuspRestriction (cubicThetaFiniteEnergyEmbedding F)‖≤
      ‖cubicThetaGlobalInclusion (cubicThetaFiniteEnergyEmbedding F)‖
    rw [cubicThetaCuspRestriction_finiteEnergy,cubicThetaFiniteEnergyEmbedding_value]
    exact cubicThetaFiniteCuspRestriction_bound F
  have hm : u∈closure (range cubicThetaFiniteEnergyEmbedding) := by
    rw [cubicThetaFiniteEnergyEmbedding_dense.closure_range]
    trivial
  exact (closure_minimal hs hc) hm

theorem cubicThetaArithmeticResidueValue_ne_zero :
    cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))≠0 := by
  intro hz
  have hb := cubicThetaCuspRestriction_value_bound (cubicThetaArithmeticResidueEnergy (4/3))
  rw [hz,norm_zero] at hb
  have hc := norm_eq_zero.mp (le_antisymm hb (_root_.norm_nonneg _))
  apply cubicThetaSpectralResidue_constant_ne_zero
  rw [hc,inner_zero_right]

end CubicFirstMoment

end

end OAI

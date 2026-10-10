import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteEnergyClosure
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticGradientL2

namespace OAI

/-! The literal arithmetic Eisenstein remainder belongs to the completed
energy graph, with its actual value and differentiated coordinates. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaArithmeticEnergy (s : ℂ) (hs : 3<s.re) : cubicThetaGlobalEnergySpace :=
  ⟨WithLp.toLp 2 (cubicThetaArithmeticL2 s hs,cubicThetaArithmeticGradientL2 s hs),
    cubicThetaFiniteEnergy_mem_graph (cubicThetaArithmeticSection s (by linarith))
      (cubicThetaArithmeticSectionFunction_contDiffOn_one (by linarith))
      (cubicThetaArithmeticSection_memLp hs) (cubicThetaArithmeticGradientRepresentative_memLp hs)⟩

lemma cubicThetaArithmeticEnergy_value (s : ℂ) (hs : 3<s.re) :
    cubicThetaGlobalInclusion (cubicThetaArithmeticEnergy s hs)=cubicThetaArithmeticL2 s hs := rfl

lemma cubicThetaArithmeticEnergy_gradient (s : ℂ) (hs : 3<s.re) :
    cubicThetaGlobalEnergyGradient (cubicThetaArithmeticEnergy s hs)=cubicThetaArithmeticGradientL2 s hs := rfl

end CubicFirstMoment

end

end OAI

import OAI.Analysis.LipschitzHilbert.Estimates.CoefficientPolarization

namespace OAI

/-! Exact polarization of the actual finite analyzing/synthesizing sum. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω] [Fintype σ]

def addScaledPacket (f h : σ → κ → Ω → ℂ) (c : ℂ) : σ → κ → Ω → ℂ :=
  fun s k z => f s k z+c*h s k z

def selfPacketSynthesis (μ : Measure Ω) (area : σ → ℝ)
    (f : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ) (z : Ω) : EuclideanSpace ℂ κ :=
  diagonalSynthesis f (fun s => analyzingCoefficient μ area f g s) z

theorem synthesis_cross_polarization (μ : Measure Ω) (area : σ → ℝ)
    (f h : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ)
    (hf : ∀ s k, Integrable (fun z => g z k*conj (f s k z)) μ)
    (hh : ∀ s k, Integrable (fun z => g z k*conj (h s k z)) μ) (z : Ω) :
    (4:ℂ) • diagonalSynthesis h (fun s => analyzingCoefficient μ area f g s) z =
      selfPacketSynthesis μ area (addScaledPacket f h 1) g z -
      selfPacketSynthesis μ area (addScaledPacket f h (-1)) g z -
      Complex.I • selfPacketSynthesis μ area (addScaledPacket f h Complex.I) g z +
      Complex.I • selfPacketSynthesis μ area (addScaledPacket f h (-Complex.I)) g z := by
  have hc (c : ℂ) : (fun s => analyzingCoefficient μ area (addScaledPacket f h c) g s) =
      (fun s => analyzingCoefficient μ area f g s +
        conj c • analyzingCoefficient μ area h g s) := by
    funext s
    exact analyzingCoefficient_add_smul μ area f h g c hf hh s
  simp only [selfPacketSynthesis,hc]
  ext k
  change (4:ℂ)*(∑ s, analyzingCoefficient μ area f g s k*h s k z) =
    (∑ s, (analyzingCoefficient μ area f g s k+conj (1:ℂ)*analyzingCoefficient μ area h g s k)*
      (f s k z+1*h s k z)) -
    (∑ s, (analyzingCoefficient μ area f g s k+conj (-1:ℂ)*analyzingCoefficient μ area h g s k)*
      (f s k z+(-1)*h s k z)) -
    Complex.I*(∑ s, (analyzingCoefficient μ area f g s k+
      conj Complex.I*analyzingCoefficient μ area h g s k)*(f s k z+Complex.I*h s k z)) +
    Complex.I*(∑ s, (analyzingCoefficient μ area f g s k+
      conj (-Complex.I)*analyzingCoefficient μ area h g s k)*(f s k z+(-Complex.I)*h s k z))
  simp only [map_one,map_neg,Complex.conj_I,one_mul,neg_mul,neg_neg,sub_eq_add_neg]
  simp only [Finset.mul_sum,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have hp := packet_cross_polarization
    (analyzingCoefficient μ area f g s k) (analyzingCoefficient μ area h g s k) (f s k z) (h s k z)
  linear_combination -hp

end LipschitzHilbert

end

end OAI

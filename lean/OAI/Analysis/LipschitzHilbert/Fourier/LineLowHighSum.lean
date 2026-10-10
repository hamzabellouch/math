import OAI.Analysis.LipschitzHilbert.Fourier.LineLowHighSpectrum
import OAI.Analysis.LipschitzHilbert.Fourier.LineAnnularSum
import OAI.Analysis.LipschitzHilbert.Trees.DyadicLineGrid

namespace OAI

/-! The complete low/high commutator sum has a bound independent of
both the number and the location of the retained dyadic frequencies. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

def lowHighPiece (m b h : SchwartzMap ℝ ℂ) (k : ℤ) : SchwartzMap ℝ ℂ :=
  lineSchwartzCommutator m
    (lineSchwartzProjection reassemblyLow (16*scale k) (by have := scale_pos k; positivity) b)
    (schwartzDerivative 1 (lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' h))

theorem lowHighSum_energy (I : Finset ℤ) (m b h : SchwartzMap ℝ ℂ) (A L : ℝ) (hA : 0≤A)
    (hm : ∀ r≤3, ∀ eta, |eta|^r*‖iteratedDeriv r m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    (∫ x, ‖(∑ k∈I, lowHighPiece m b h k) x‖^2)≤
      36*(L*(∫ t, ‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖)*A*
        localizedKernelFirstMomentConstant dyadicCommutatorCutoff*(26*Real.pi/9))^2*
        (∫ x, ‖h x‖^2) := by
  let C := L*(∫ t, ‖(𝓕⁻ reassemblyLow : SchwartzMap ℝ ℂ) t‖)*A*
    localizedKernelFirstMomentConstant dyadicCommutatorCutoff*(26*Real.pi/9)
  let H := fun k => lineSchwartzProjection dyadicDifference (scale k) (scale_pos k).ne' h
  have hpiece (k : ℤ) : (∫ x, ‖lowHighPiece m b h k x‖^2)≤C^2*(∫ x, ‖H k x‖^2) :=
    lowHighCommutator_energy m b h (scale k) A L (scale_pos k) hA hm hLip
  have hsum := line_annular_sum_energy I (lowHighPiece m b h) (by
    intro k _ eta heta
    have hb := lowHighCommutator_frequency m b h (scale k) (scale_pos k) eta heta
    have hlo := (div_le_iff₀ (scale_pos k)).mp hb.1
    have hhi := (le_div_iff₀ (scale_pos k)).mp hb.2
    exact ⟨by simpa only [scale,mul_comm] using hlo,by simpa only [scale,mul_comm] using hhi⟩)
  have hframe : (∑ k∈I, ∫ x, ‖H k x‖^2)≤12*(∫ x, ‖h x‖^2) :=
    lineSchwartzProjection_frame I (fun _ => dyadicDifference) scale (fun k => (scale_pos k).ne')
      12 (fun eta => dyadicDifference_square_sum I eta) h
  calc
    _ ≤ 3*∑ k∈I, ∫ x, ‖lowHighPiece m b h k x‖^2 := hsum
    _ ≤ 3*∑ k∈I, C^2*(∫ x, ‖H k x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hpiece k) (by norm_num)
    _ = 3*C^2*(∑ k∈I, ∫ x, ‖H k x‖^2) := by rw [←Finset.mul_sum]; ring
    _ ≤ 3*C^2*(12*(∫ x, ‖h x‖^2)) := mul_le_mul_of_nonneg_left hframe (by positivity)
    _ = _ := by dsimp [C]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI

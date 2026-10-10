import OAI.Analysis.LipschitzHilbert.Packets.AnalyzingCoefficients
import OAI.Analysis.LipschitzHilbert.Packets.PacketPolarization

namespace OAI

/-! Antilinearity of the actual analyzing integral supplies the
coefficients in the four-term packet polarization identity. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert
variable {Ω σ κ : Type*} [MeasurableSpace Ω]

theorem analyzingCoefficient_add_smul (μ : Measure Ω) (area : σ → ℝ)
    (f h : σ → κ → Ω → ℂ) (g : Ω → EuclideanSpace ℂ κ) (c : ℂ)
    (hf : ∀ s k, Integrable (fun z => g z k*conj (f s k z)) μ)
    (hh : ∀ s k, Integrable (fun z => g z k*conj (h s k z)) μ) (s : σ) :
    analyzingCoefficient μ area (fun s k z => f s k z+c*h s k z) g s =
      analyzingCoefficient μ area f g s + conj c • analyzingCoefficient μ area h g s := by
  ext k
  change ((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (f s k z+c*h s k z) ∂μ) =
    ((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (f s k z) ∂μ) +
      conj c*(((↑(area s) : ℂ)⁻¹)*(∫ z, g z k*conj (h s k z) ∂μ))
  have heq : (fun z => g z k*conj (f s k z+c*h s k z)) =
      (fun z => g z k*conj (f s k z)+conj c*(g z k*conj (h s k z))) := by
    funext z
    simp only [map_add,map_mul]
    ring
  rw [heq,integral_add (hf s k) ((hh s k).const_mul (conj c)),integral_const_mul]
  ring

end LipschitzHilbert

end

end OAI

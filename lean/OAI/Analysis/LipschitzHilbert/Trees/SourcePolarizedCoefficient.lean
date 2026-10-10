import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticePolarizationSpectrum
import OAI.Analysis.LipschitzHilbert.Trees.SourceCoefficientIntegrability
import OAI.Analysis.LipschitzHilbert.Estimates.SynthesisPolarization

namespace OAI

/-! The four polarized source families carry the exact linear
combinations of the original physical analyzing coefficients. -/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2*P.order) ≤ P.profileBound)

theorem polarize_physicalSelectedWave (c : ℂ) (hc : ‖c‖ = 1)
    (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) :
    (P.polarize alt hAlt c hc).physicalSelectedWave t d v =
      addScaledPacket (P.physicalSelectedWave t d v)
        ((P.withProfile alt hAlt).physicalSelectedWave t d v) c := by
  funext q k z
  unfold physicalSelectedWave addScaledPacket
  by_cases hv : v z ≤ d q.1
  · simp only [ite_eq_left hv]
    exact congrArg (fun F : SchwartzMap (ℝ × ℝ) ℂ => F z)
      (P.polarize_physicalPacket alt hAlt c hc t q.1 q.2 k)
  · simp only [ite_eq_right hv,mul_zero,add_zero]

theorem polarize_physicalCoefficient (c : ℂ) (hc : ‖c‖ = 1)
    (t : ℝ) (d : Fin N → ℝ) (v : ℝ × ℝ → ℝ) (hv : Measurable v)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (hg : Measurable g) (hg1 : ∀ z, ‖g z‖ ≤ 1)
    (j : Fin N) (u : ι j) :
    (P.polarize alt hAlt c hc).physicalCoefficient t d v g j u =
      P.physicalCoefficient t d v g j u +
        conj c • (P.withProfile alt hAlt).physicalCoefficient t d v g j u := by
  unfold physicalCoefficient
  rw [P.polarize_physicalSelectedWave alt hAlt c hc t d v]
  exact analyzingCoefficient_add_smul (volume.prod volume)
    (fun q : Σ j, ι j => P.length q.1*P.width)
    (P.physicalSelectedWave t d v) ((P.withProfile alt hAlt).physicalSelectedWave t d v) g c
    (P.physical_analyzing_integrable t d v hv g hg hg1)
    ((P.withProfile alt hAlt).physical_analyzing_integrable t d v hv g hg hg1) ⟨j,u⟩

end LipschitzHilbert.SourceLatticePacket

end

end OAI

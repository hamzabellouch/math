import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.PacketFrame
import OAI.Analysis.CoulombRadii.FieldAnalysis.FrameImageDensity
import OAI.Analysis.CoulombRadii.Packets.ComplexWindow

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Filter
open scoped ENNReal NNReal FourierTransform SchwartzMap LineDeriv ComplexConjugate
open scoped LineDeriv
namespace Coulomb
noncomputable def spaceFourierL2 : Lp ℂ 2 (volume : Measure Space) →L[ℂ]
    Lp ℂ 2 (volume : Measure Space) :=
  (Lp.fourierTransformₗᵢ Space ℂ).toContinuousLinearEquiv.toContinuousLinearMap

lemma spaceFourierL2_apply (u : Lp ℂ 2 (volume : Measure Space)) :
    spaceFourierL2 u = 𝓕 u := rfl

lemma packetFrame_fourier_weighted_trace (g : 𝓢(Space,ℝ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (hp : MemLp (fun yp : Space × Space => yp.2) 2 μ) (a : Space) :
    let hv := packetState_toL2_memLp (complexWindow g) μ
    let b := compactSpectralBasis (packetFrame (complexWindow g) μ)
      (packetFrame_compact (complexWindow g) μ) (frameOperator_symmetric hv)
    (∀ i : Σ z, eigenspaceBasisSet (packetFrame (complexWindow g) μ) z,
      i.1.re ≠ 0 → Integrable (fun ξ : Space => (2*Real.pi*inner ℝ ξ a)^2 *
        ‖(𝓕 (b i) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2)) ∧
    HasSum (fun i : Σ z, eigenspaceBasisSet (packetFrame (complexWindow g) μ) z =>
      i.1.re * ∫ ξ : Space, (2*Real.pi*inner ℝ ξ a)^2 *
        ‖(𝓕 (b i) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2)
      (∫ yp : Space × Space, (2*Real.pi*inner ℝ a yp.2)^2 * (∫ x : Space, g x^2) +
        (∫ x : Space, (fderiv ℝ g x a)^2) ∂μ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  dsimp only
  have hV (yp : Space × Space) :
      spaceFourierL2 ((packetState (complexWindow g) yp.1 yp.2).toLp 2) =ᵐ[volume]
      fun ξ => (𝓕 (packetState (complexWindow g) yp.1 yp.2) : 𝓢(Space,ℂ)) ξ := by
    rw [spaceFourierL2_apply, SchwartzMap.toLp_fourier_eq]
    exact SchwartzMap.coeFn_toLp _ 2 volume
  have h := frameImage_weighted_trace (packetState_toL2_memLp (complexWindow g) μ)
    spaceFourierL2 (fun yp ξ => (𝓕 (packetState (complexWindow g) yp.1 yp.2) : 𝓢(Space,ℂ)) ξ)
    hV (packetState_fourier_joint_square_integrable (complexWindow g) μ)
    (fun ξ : Space => (2*Real.pi*inner ℝ ξ a)^2) (by fun_prop) (fun ξ => sq_nonneg _)
    (packetState_real_weighted_joint_integrable g μ hp a)
  constructor
  · exact h.1
  · convert h.2 using 1
    all_goals first | rfl | (simp only [packetState_real_kinetic_integral])

lemma packetFrame_positive_eigen_weakDerivative (g : 𝓢(Space,ℝ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ]
    (hp : MemLp (fun yp : Space × Space => yp.2) 2 μ) (a : Space)
    (i : Σ z, eigenspaceBasisSet (packetFrame (complexWindow g) μ) z) (hi : i.1.re ≠ 0) :
    let hv := packetState_toL2_memLp (complexWindow g) μ
    let b := compactSpectralBasis (packetFrame (complexWindow g) μ)
      (packetFrame_compact (complexWindow g) μ) (frameOperator_symmetric hv)
    ∃ d : Lp ℂ 2 (volume : Measure Space),
      (∀ φ : Space → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x : Space, (fderiv ℝ φ x a : ℂ) * b i x) =
          -(∫ x : Space, (φ x : ℂ) * d x)) ∧
      ‖d‖^2 = ∫ ξ : Space, (2*Real.pi*inner ℝ ξ a)^2 *
        ‖(𝓕 (b i) : Lp ℂ 2 (volume : Measure Space)) ξ‖^2 := by
  dsimp only
  exact l2_fourier_weighted_derivative _ a
    ((packetFrame_fourier_weighted_trace g μ hp a).1 i hi)
end Coulomb

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

end

end OAI

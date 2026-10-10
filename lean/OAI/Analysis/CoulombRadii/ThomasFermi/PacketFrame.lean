import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.HilbertBasisSumSqInner
import OAI.Analysis.CoulombRadii.FormDomain.PacketStateL2Norm

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
namespace Coulomb
noncomputable def packetFrame (g : 𝓢(Space,ℂ)) (μ : Measure (Space × Space)) :
    Lp ℂ 2 (volume : Measure Space) →L[ℂ] Lp ℂ 2 (volume : Measure Space) :=
  frameOperator μ (fun yp : Space × Space => (packetState g yp.1 yp.2).toLp 2 volume)

lemma packetFrame_schwartz_quadratic_le (g h : 𝓢(Space,ℂ))
    (hg : (∫ x : Space, ‖g x‖^2) = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume.prod volume) :
    (inner ℂ (h.toLp 2 volume) (packetFrame g μ (h.toLp 2 volume))).re ≤
      ‖h.toLp 2 volume‖^2 := by
  rw [packetFrame, frameOperator_quadratic (packetState_toL2_memLp g μ)]
  simp only [packetState_inner]
  calc
    _ ≤ ∫ yp : Space × Space, ‖packetAnalysis g h yp.1 yp.2‖^2 ∂volume.prod volume :=
      integral_mono_measure hμ (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (packetAnalysis_integrable g h)
    _ = ‖h.toLp 2 volume‖^2 := by
      rw [packetAnalysis_resolution, hg, one_mul, schwartz_toL2_norm_sq]

lemma packetFrame_quadratic_le (g : 𝓢(Space,ℂ))
    (hg : (∫ x : Space, ‖g x‖^2) = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume.prod volume)
    (u : Lp ℂ 2 (volume : Measure Space)) :
    (inner ℂ u (packetFrame g μ u)).re ≤ ‖u‖^2 := by
  refine DenseRange.induction_on
    (p := fun w : Lp ℂ 2 (volume : Measure Space) =>
      (inner ℂ w (packetFrame g μ w)).re ≤ ‖w‖^2)
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := Space)
      (p := 2) (μ := (volume : Measure Space)) (by simp)) u ?_ ?_
  · exact isClosed_le (Complex.continuous_re.comp
      (continuous_id.inner (packetFrame g μ).continuous)) (continuous_norm.pow 2)
  · intro h
    exact packetFrame_schwartz_quadratic_le g h hg μ hμ

lemma packetFrame_positive (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    (packetFrame g μ).toLinearMap.IsPositive :=
  frameOperator_positive (packetState_toL2_memLp g μ)

lemma packetFrame_complement_positive (g : 𝓢(Space,ℂ))
    (hg : (∫ x : Space, ‖g x‖^2) = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] (hμ : μ ≤ volume.prod volume) :
    (ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure Space)) - packetFrame g μ).toLinearMap.IsPositive := by
  apply id_sub_frameOperator_positive (packetState_toL2_memLp g μ)
  intro u
  rw [← frameOperator_quadratic (packetState_toL2_memLp g μ)]
  exact packetFrame_quadratic_le g hg μ hμ u

lemma packetFrame_compact (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] : IsCompactOperator (packetFrame g μ) :=
  frameOperator_compact (packetState_toL2_memLp g μ)

lemma packetFrame_spectral_trace (g : 𝓢(Space,ℂ))
    (hg : (∫ x : Space, ‖g x‖^2) = 1)
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    HasSum (fun i : Σ z, eigenspaceBasisSet (packetFrame g μ) z => i.1.re) (μ.real univ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have h := frameOperator_spectral_hasSum (packetState_toL2_memLp g μ)
  simpa only [packetFrame, packetState_toL2_norm, integral_const, smul_eq_mul, schwartz_toL2_norm_sq, hg, mul_one] using h
end Coulomb

end

end OAI

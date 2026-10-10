import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.PacketStateL2Norm
import OAI.Analysis.CoulombRadii.FieldAnalysis.FrameDensity

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
lemma packetState_joint_square_integrable (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    Integrable (fun z : (Space × Space) × Space => ‖packetState g z.1.1 z.1.2 z.2‖^2)
      (μ.prod volume) := by
  have hm : Continuous (fun z : (Space × Space) × Space => ‖packetState g z.1.1 z.1.2 z.2‖^2) := by
    simp only [packetState_norm]
    exact ((g.continuous.comp (continuous_snd.sub continuous_fst.fst)).norm.pow 2)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun yp => ?_), ?_⟩
  · exact ((packetState g yp.1 yp.2).memLp 2 volume).integrable_norm_pow (by norm_num)
  · simpa only [Real.norm_of_nonneg (sq_nonneg (_ : ℝ)), packetState_integral_norm_sq]
      using (integrable_const (∫ x : Space, ‖g x‖^2) : Integrable (fun _ : Space × Space => ∫ x : Space, ‖g x‖^2) μ)

lemma packetFrame_density (g : 𝓢(Space,ℂ))
    (μ : Measure (Space × Space)) [IsFiniteMeasure μ] :
    frameDensity (packetState_toL2_memLp g μ) =ᵐ[volume]
      (fun x : Space => ∫ yp : Space × Space, ‖g (x-yp.1)‖^2 ∂μ) := by
  have h := frameDensity_eq_ae (packetState_toL2_memLp g μ)
    (fun yp x => packetState g yp.1 yp.2 x)
    (fun yp => (packetState g yp.1 yp.2).coeFn_toLp 2 volume)
    (packetState_joint_square_integrable g μ)
  simpa only [packetState_norm] using h
end Coulomb

end

end OAI

import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediateUniformRegularity

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def UniformIntermediateC11 : Prop :=
   ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 → ∃ S : Finset M, ∃ r : M → ℝ, ∃ C : ℝ≥0,
     (∀ z ∈ S, 0 < r z ∧ Metric.ball (chartAt (Model n) z z) (r z) ⊆ (chartAt (Model n) z).target ∧
       ∀ u v : M → ℝ, IsDualPair u v → ∀ t ∈ Icc a b,
       LipschitzOnWith C (fderiv ℝ (fun X : Model n => hopfLax t u ((chartAt (Model n) z).symm X)))
         (Metric.ball (chartAt (Model n) z z) (r z))) ∧
     ∀ x : M, ∃ z ∈ S, x ∈ (chartAt (Model n) z).source ∧
       (chartAt (Model n) z) x ∈ Metric.ball (chartAt (Model n) z z) (r z)

 theorem intermediate_uniform_c11 (hMTW : HasWeakMTW (n := n) (M := M)) :
     UniformIntermediateC11 (n := n) (M := M) := by
   classical
   intro a b ha hab hb
   choose r C hr hT hbound using intermediate_uniform_coordinate_c11 hMTW ha hab hb
   let U (z : M) := (chartAt (Model n) z).source ∩
     (chartAt (Model n) z) ⁻¹' Metric.ball (chartAt (Model n) z z) (r z)
   have hU (z : M) : IsOpen (U z) :=
     (chartAt (Model n) z).continuousOn.isOpen_inter_preimage
       (chartAt (Model n) z).open_source Metric.isOpen_ball
   have hxU (z : M) : z ∈ U z := ⟨mem_chart_source (Model n) z,Metric.mem_ball_self (hr z)⟩
   obtain ⟨S,hS⟩ := (isCompact_univ : IsCompact (univ : Set M)).elim_finite_subcover U hU
     (fun x _ => mem_iUnion.mpr ⟨x,hxU x⟩)
   refine ⟨S,r,∑ z ∈ S, C z,?_,?_⟩
   · intro z hz
     refine ⟨hr z,hT z,?_⟩
     intro u v huv t ht
     exact (hbound z u v huv t ht).weaken (Finset.single_le_sum (fun i _ => (show (0 : ℝ≥0) ≤ C i from bot_le)) hz)
   · intro x
     obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp (hS (mem_univ x))
     exact ⟨z,hz,hxz⟩
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

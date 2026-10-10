import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediatePoleLipschitz
import OAI.Geometry.WeakMTW.Potentials.IntermediateMomentumLipschitz

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def UniformIntermediateLipschitz (hMTW : HasWeakMTW (n := n) (M := M)) : Prop :=
   ∃ S : Finset M, ∃ P : M → Set M,
     (∀ x ∈ S, IsCompact (P x) ∧ P x ⊆ (chartAt (Model n) x).source) ∧
     (∀ y : M, ∃ x ∈ S, y ∈ interior (P x)) ∧
     ∀ a b : ℝ, ∀ ha : 0 < a, a ≤ b → ∀ hb : b < 1, ∃ C : ℝ≥0,
       (∀ d : IntermediateDatum M a b, LipschitzWith C (fun z => (datumInverse hMTW ha hb d z).1)) ∧
       (∀ x ∈ S, ∀ d : IntermediateDatum M a b,
         LipschitzOnWith C (fun z => (stateChart x (datumInverse hMTW ha hb d z)).2)
           {z | (datumInverse hMTW ha hb d z).1 ∈ P x})

 theorem intermediate_uniform_lipschitz (hMTW : HasWeakMTW (n := n) (M := M)) :
     UniformIntermediateLipschitz hMTW := by
   classical
   choose P hP hxP hPS using (fun x : M =>
     exists_compact_subset (chartAt (Model n) x).open_source (mem_chart_source (Model n) x))
   obtain ⟨S,hS⟩ := (isCompact_univ : IsCompact (univ : Set M)).elim_finite_subcover
     (fun x => interior (P x)) (fun _ => isOpen_interior)
     (fun x _ => mem_iUnion.mpr ⟨x,hxP x⟩)
   refine ⟨S,P,fun x _ => ⟨hP x,hPS x⟩,?_,?_⟩
   · intro y
     obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp (hS (mem_univ y))
     exact ⟨x,hx,hy⟩
   · intro a b ha hab hb
     obtain ⟨A,hA⟩ := intermediate_uniform_pole_lipschitz hMTW ha hab hb
     choose B hB using (fun x => intermediate_uniform_momentum_patch hMTW ha hab hb x (hP x) (hPS x))
     refine ⟨A+∑ x ∈ S, B x,fun d => (hA d).weaken (le_add_of_nonneg_right bot_le),?_⟩
     intro x hx d
     exact (hB x d).weaken ((Finset.single_le_sum (fun z _ => (show (0 : ℝ≥0) ≤ B z from bot_le)) hx).trans
       (le_add_of_nonneg_left bot_le))
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixWeakEquation

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldLocalization Set
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]

lemma finite_joint_partition (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J) :
    ∃ A : FiniteCharts X,
      (∀ p : A.centers, tsupport (A.partition p) ⊆ (parametrixData J α hs ht p.val).source) ∧
      (∀ p : A.centers, tsupport (A.partition p) ⊆ (HodgeChart.data J α hs ht p.val).source) := by
  classical
  let O := fun p : X => (parametrixData J α hs ht p).source ∩ (HodgeChart.data J α hs ht p).source
  have hO (p : X) : IsOpen (O p) :=
    (parametrixData J α hs ht p).source_open.inter (HodgeChart.data J α hs ht p).source_open
  have hp (p : X) : p ∈ O p :=
    ⟨(parametrixData J α hs ht p).mem_source,(HodgeChart.data J α hs ht p).mem_source⟩
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun p _ => mem_iUnion_of_mem p (hp p))
  have hc : (univ : Set X) ⊆ ⋃ p : s, O p.val := by
    intro x hx
    obtain ⟨p,hps,hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hps⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => O p.val) (fun p => hO p.val) hc
  refine ⟨⟨s,ρ,fun p => (hρ p).trans (fun _ hx =>
    (parametrixData J α hs ht p.val).source_subset hx.1)⟩,?_,?_⟩
  · intro p x hx
    exact (hρ p hx).1
  · intro p x hx
    exact (hρ p hx).2

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI

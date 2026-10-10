import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeParametrixWeakEquation

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization Set
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X]

lemma finite_triple_partition
    (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J) :
    ∃ A : FiniteCharts X,
      (∀ p : A.centers, tsupport (A.partition p) ⊆ (parametrixData J α hs ht p.val).source) ∧
      (∀ p : A.centers, tsupport (A.partition p) ⊆ (HodgeChart.data J α hs ht p.val).source) ∧
      (∀ p : A.centers, tsupport (A.partition p) ⊆ (GeometricChart.data J α hs ht p.val).source) := by
  classical
  let U : X → Set X := fun p => (parametrixData J α hs ht p).source ∩
    (HodgeChart.data J α hs ht p).source ∩ (GeometricChart.data J α hs ht p).source
  have hU (p : X) : IsOpen (U p) :=
    ((parametrixData J α hs ht p).source_open.inter (HodgeChart.data J α hs ht p).source_open).inter
      (GeometricChart.data J α hs ht p).source_open
  have hp (p : X) : p ∈ U p :=
    ⟨⟨(parametrixData J α hs ht p).mem_source,(HodgeChart.data J α hs ht p).mem_source⟩,
      (GeometricChart.data J α hs ht p).mem_source⟩
  obtain ⟨s,hscover⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun p _ => mem_iUnion_of_mem p (hp p))
  have hc : (univ : Set X) ⊆ ⋃ p : s, U p.val := by
    intro x hx
    obtain ⟨p,hp',hxp⟩ := mem_iUnion₂.mp (hscover hx)
    exact mem_iUnion_of_mem ⟨p,hp'⟩ hxp
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun p : s => U p.val) (fun p => hU p.val) hc
  let A : FiniteCharts X := ⟨s,ρ,fun p => (hρ p).trans
    (inter_subset_left.trans (inter_subset_left.trans (parametrixData J α hs ht p.val).source_subset))⟩
  exact ⟨A,fun p => (hρ p).trans (inter_subset_left.trans inter_subset_left),
    fun p => (hρ p).trans (inter_subset_left.trans inter_subset_right),
    fun p => (hρ p).trans inter_subset_right⟩
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI

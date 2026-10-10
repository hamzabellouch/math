import OAI.Computability.DegreeRigidity.Syntax.CheckedHierarchySyntax
import OAI.Computability.DegreeRigidity.Constructibility.CollectionHierarchyInternal
import OAI.Computability.DegreeRigidity.Constructibility.RelativeDefCertificates
import OAI.Computability.DegreeRigidity.Constructibility.RelativeModelOrdinals

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem relative_internal_hierarchy_cover (M x : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (hx : x ∈ relativeModel M (groundReals M)) :
    ∃ d ∈ relativeModel M (groundReals M), ∃ f ∈ relativeModel M (groundReals M),
      x ∈ d ∧ HierarchyGraph (relativeModel M (groundReals M)) (seed (groundReals M))
        d (iterUnion 2 f) f := by
  have hR := groundReals_mem M hM hT
  exact internal_hierarchy_cover_collection _ _ x (ground_relative_context M hM hT)
    (relativeModel_sigma_replacement M _ hM hT hR)
    (relativeModel_sigma_collection M _ hM hT hR)
    ((mem_relativeModel M _ _ hM hT hR).mpr (parameter_in_relativeModel M _ hM hT)) hx

theorem relative_internal_ordinal_hierarchy (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) :
    ∃ d ∈ relativeModel M (groundReals M), ∃ f ∈ relativeModel M (groundReals M),
      o.toZFSet ∈ d ∧ CheckedHierarchyGraph (relativeModel M (groundReals M))
        ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) (seed (groundReals M))
        d (iterUnion 2 f) f := by
  obtain ⟨d,hd,f,hf,ho,hg⟩ := relative_internal_hierarchy_cover M o.toZFSet hM hT
    ((ground_relativeModel_ordinal_iff M hM hT o).mpr ho)
  exact ⟨d,hd,f,hf,ho,(checkedHierarchyGraph_of_context _ _ _ _ _
    (ground_relative_context M hM hT)).mpr hg⟩

end TuringRigidity.RelativeConstructible

end OAI

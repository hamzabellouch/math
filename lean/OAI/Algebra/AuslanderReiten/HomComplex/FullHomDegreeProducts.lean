import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProductLinear
import OAI.Algebra.AuslanderReiten.Complete.TateKoszul
import OAI.Algebra.AuslanderReiten.Resolutions.ResolutionProductCompatibility

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u v
variable {k : Type u} [Field k]
variable {C : Type v} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {n m l : ℤ}

theorem fullHomProduct_degree_mk (h : n+m=l)
    (x : Cocycle K L n) (y : Cocycle L M m) (z : Cocycle K M l)
    (hz : z.val=x.val.comp y.val h) :
    TateKoszul.degreeEquiv (k := k) (CohomologyClass K M) h
      (fullHomProduct (CohomologyClass.mk x) (CohomologyClass.mk y)) = CohomologyClass.mk z := by
  subst l
  change CohomologyClass.mk (cocycleProduct x y) = CohomologyClass.mk z
  congr 1
  exact Subtype.ext hz.symm

def fullHomIdentity (K : CochainComplex C ℤ) : CohomologyClass K K 0 :=
  CohomologyClass.mk (Cocycle.ofHom (𝟙 K))

theorem fullHomProduct_identity_right (x : CohomologyClass K L n) :
    TateKoszul.degreeEquiv (k := k) (CohomologyClass K L) (add_zero n)
      (fullHomProduct x (fullHomIdentity L)) = x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  apply fullHomProduct_degree_mk
  exact (Cochain.comp_id x.val).symm

theorem fullHomProduct_identity_left (x : CohomologyClass K L n) :
    TateKoszul.degreeEquiv (k := k) (CohomologyClass K L) (zero_add n)
      (fullHomProduct (fullHomIdentity K) x) = x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  apply fullHomProduct_degree_mk
  exact (Cochain.id_comp x.val).symm

end ArExplicit.CompleteComparison

end

end OAI

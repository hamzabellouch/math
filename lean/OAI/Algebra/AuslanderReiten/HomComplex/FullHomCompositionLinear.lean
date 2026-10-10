import OAI.Algebra.AuslanderReiten.HomComplex.FullHomMapLinear

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
namespace ArExplicit
universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} (n : ℤ)

def fullHomPostcompLinear (f : L ⟶ M) : CohomologyClass K L n →ₗ[k] CohomologyClass K M n where
  __ := fullHomPostcomp f n
  map_smul' a x := by
    change fullHomPostcomp f n (a • x) = a • fullHomPostcomp f n x
    obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
    rw [← CompleteComparison.fullHom_mk_smul, fullHomPostcomp_mk, fullHomPostcomp_mk,
      ← CompleteComparison.fullHom_mk_smul]
    congr 1
    apply Subtype.ext
    exact Cochain.smul_comp a x.val (Cochain.ofHom f) (add_zero n)

def fullHomPrecompLinear (f : K ⟶ L) : CohomologyClass L M n →ₗ[k] CohomologyClass K M n where
  __ := fullHomPrecomp f n
  map_smul' a x := by
    change fullHomPrecomp f n (a • x) = a • fullHomPrecomp f n x
    obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
    rw [← CompleteComparison.fullHom_mk_smul, fullHomPrecomp_mk, fullHomPrecomp_mk,
      ← CompleteComparison.fullHom_mk_smul]
    congr 1
    apply Subtype.ext
    exact Cochain.comp_smul (Cochain.ofHom f) a x.val (zero_add n)

end ArExplicit

end

end OAI

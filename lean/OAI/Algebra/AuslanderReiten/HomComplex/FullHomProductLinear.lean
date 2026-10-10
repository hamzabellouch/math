import OAI.Algebra.AuslanderReiten.HomComplex.FullHomLinear

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category* C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

theorem fullHomProduct_add_left (x x' : CohomologyClass K L n)
    (y : CohomologyClass L M m) :
    fullHomProduct (x+x') y = fullHomProduct x y + fullHomProduct x' y := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨x',rfl⟩ := CohomologyClass.mk_surjective x'
  obtain ⟨y,rfl⟩ := CohomologyClass.mk_surjective y
  rw [← CohomologyClass.mk_add, fullHomProduct_mk, fullHomProduct_mk, fullHomProduct_mk,
    ← CohomologyClass.mk_add]
  congr 1
  apply Subtype.ext
  exact Cochain.add_comp x.val x'.val y.val rfl

theorem fullHomProduct_add_right (x : CohomologyClass K L n)
    (y y' : CohomologyClass L M m) :
    fullHomProduct x (y+y') = fullHomProduct x y + fullHomProduct x y' := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y,rfl⟩ := CohomologyClass.mk_surjective y
  obtain ⟨y',rfl⟩ := CohomologyClass.mk_surjective y'
  rw [← CohomologyClass.mk_add, fullHomProduct_mk, fullHomProduct_mk, fullHomProduct_mk,
    ← CohomologyClass.mk_add]
  congr 1
  apply Subtype.ext
  exact Cochain.comp_add x.val y.val y'.val rfl

theorem fullHomProduct_smul_left (c : k) (x : CohomologyClass K L n)
    (y : CohomologyClass L M m) :
    fullHomProduct (c • x) y = c • fullHomProduct x y := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y,rfl⟩ := CohomologyClass.mk_surjective y
  rw [← fullHom_mk_smul, fullHomProduct_mk, fullHomProduct_mk, ← fullHom_mk_smul]
  congr 1
  apply Subtype.ext
  exact Cochain.smul_comp c x.val y.val rfl

theorem fullHomProduct_smul_right (c : k) (x : CohomologyClass K L n)
    (y : CohomologyClass L M m) :
    fullHomProduct x (c • y) = c • fullHomProduct x y := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y,rfl⟩ := CohomologyClass.mk_surjective y
  rw [← fullHom_mk_smul, fullHomProduct_mk, fullHomProduct_mk, ← fullHom_mk_smul]
  congr 1
  apply Subtype.ext
  exact Cochain.comp_smul x.val c y.val rfl

def fullHomRightMultiply (y : CohomologyClass L M m) :
    CohomologyClass K L n →ₗ[k] CohomologyClass K M (n+m) where
  toFun x := fullHomProduct x y
  map_add' x x' := fullHomProduct_add_left x x' y
  map_smul' c x := fullHomProduct_smul_left c x y

def fullHomLeftMultiply (x : CohomologyClass K L n) :
    CohomologyClass L M m →ₗ[k] CohomologyClass K M (n+m) where
  toFun y := fullHomProduct x y
  map_add' y y' := fullHomProduct_add_right x y y'
  map_smul' c y := fullHomProduct_smul_right c x y

end ArExplicit.CompleteComparison

end OAI

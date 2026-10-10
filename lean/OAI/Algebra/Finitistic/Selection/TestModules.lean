import OAI.Algebra.Finitistic.Selection.CharacterModule
import OAI.Algebra.Finitistic.Selection.SelectionCharacter
import OAI.Algebra.Finitistic.Selection.SelectionAlgebra

namespace OAI
namespace LittleFinitistic
open MonoidAlgebra

noncomputable abbrev TestModule (m : ℕ) [NeZero m] :=
  CharacterModule.eigenspace (quotientCentralEmbedding m) (selectionCharacter m)
    (quotientCentralEmbedding_central m)

noncomputable instance testModule_nontrivial (m : ℕ) [NeZero m] : Nontrivial (TestModule m) :=
  CharacterModule.eigenspace_nontrivial _ _ _ (quotientCentralEmbedding_injective m)

noncomputable instance testModule_finiteDimensional (m : ℕ) [NeZero m] :
    FiniteDimensional ℂ (TestModule m) :=
  CharacterModule.eigenspace_finiteDimensional _ _ _

noncomputable def testRingMap (m : ℕ) [NeZero m] :
    SelectionRing →ₐ[ℂ] MonoidAlgebra ℂ (FiniteQuotientGroup m) :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (finiteQuotientMap m)

noncomputable instance testModule_module (m : ℕ) [NeZero m] :
    Module SelectionRing (TestModule m) :=
  Module.compHom (TestModule m) (testRingMap m).toRingHom

@[simp] theorem testModule_smul_val (m : ℕ) [NeZero m]
    (r : SelectionRing) (x : TestModule m) :
    ((r • x : TestModule m) : MonoidAlgebra ℂ (FiniteQuotientGroup m)) = testRingMap m r * x := rfl

instance testModule_scalarTower (m : ℕ) [NeZero m] : IsScalarTower ℂ SelectionRing (TestModule m) where
  smul_assoc c r x := by
    apply Subtype.ext
    change testRingMap m (c • r) * x.val = c • (testRingMap m r * x.val)
    rw [map_smul,smul_mul_assoc]

@[simp] theorem testRingMap_algebraZ (m : ℕ) [NeZero m] (q : ℤ) :
    testRingMap m (algebraZ q) = single (finiteQuotientMap m (Presentation.z q)) 1 := by
  simp [testRingMap,algebraZ]

theorem testModule_basis_action (m : ℕ) [NeZero m] (i : Fin m) (x : TestModule m) :
    algebraZ i.val • x = (if i = lastIndex m then (-1 : ℂ) else 1) • x := by
  apply Subtype.ext
  change testRingMap m (algebraZ i.val) * x.val = _
  rw [testRingMap_algebraZ,← quotientCentralEmbedding_basis]
  have hx := x.property (Multiplicative.ofAdd (Pi.single i 1))
  rw [selectionCharacter_basis] at hx
  by_cases h : i = lastIndex m
  · simp only [h,ite_true,Units.val_neg,Units.val_one] at hx ⊢
    exact hx
  · simp only [h,ite_false,Units.val_one] at hx ⊢
    exact hx

/-- The first m−1 selecting idempotents act as identity; the next acts as zero. -/
theorem testModule_idempotent_action (m : ℕ) [NeZero m] (i : Fin m) (x : TestModule m) :
    selectionIdempotent i.val • x = if i = lastIndex m then 0 else x := by
  classical
  unfold selectionIdempotent
  rw [smul_assoc,add_smul,one_smul,testModule_basis_action]
  split_ifs
  · rw [show (-1 : ℂ) • x = -x from neg_one_smul ℂ x,add_neg_cancel,smul_zero]
  · rw [one_smul,← two_smul ℂ x,smul_smul]
    norm_num
end LittleFinitistic

end OAI

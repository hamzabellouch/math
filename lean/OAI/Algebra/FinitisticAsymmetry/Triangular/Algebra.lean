import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Transport.ScalarRestriction

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace TriangularConstruction
universe v
variable (C E U : Type v)

def OffDiagonal (_C _E U : Type v) := U

def offValue {C E U : Type v} (x : OffDiagonal C E U) : U := x

namespace OffDiagonal
variable [Ring C] [Ring E] [AddCommGroup U]

instance : AddCommGroup (OffDiagonal C E U) := inferInstanceAs (AddCommGroup U)

instance [Module E U] : Module (C × E) (OffDiagonal C E U) :=
  Module.compHom U (RingHom.snd C E)

instance [Module Cᵐᵒᵖ U] : Module (C × E)ᵐᵒᵖ (OffDiagonal C E U) :=
  Module.compHom U (RingHom.fst C E).op

instance [Module E U] [Module Cᵐᵒᵖ U] [SMulCommClass E Cᵐᵒᵖ U] :
    SMulCommClass (C × E) (C × E)ᵐᵒᵖ (OffDiagonal C E U) where
  smul_comm p q x := by
    change p.2 • (MulOpposite.op q.unop.1 • (offValue x)) =
      MulOpposite.op q.unop.1 • (p.2 • (offValue x))
    exact smul_comm _ _ _

variable (k : Type v) [Field k] [_root_.Algebra k C] [_root_.Algebra k E] [Module k U]

instance : Module k (OffDiagonal C E U) := inferInstanceAs (Module k U)

instance [Module E U] [IsScalarTower k E U] :
    IsScalarTower k (C × E) (OffDiagonal C E U) where
  smul_assoc r p x := by
    change (r • p.2) • (offValue x) = r • (p.2 • (offValue x))
    exact smul_assoc _ _ _

instance [Module Cᵐᵒᵖ U] [IsScalarTower k Cᵐᵒᵖ U] :
    IsScalarTower k (C × E)ᵐᵒᵖ (OffDiagonal C E U) where
  smul_assoc r p x := by
    change (r • MulOpposite.op p.unop.1) • (offValue x) =
      r • (MulOpposite.op p.unop.1 • (offValue x))
    exact smul_assoc _ _ _

instance [FiniteDimensional k U] : FiniteDimensional k (OffDiagonal C E U) :=
  inferInstanceAs (FiniteDimensional k U)

end OffDiagonal

abbrev Algebra := TrivSqZeroExt (C × E) (OffDiagonal C E U)

variable [Ring C] [Ring E] [AddCommGroup U] [Module E U] [Module Cᵐᵒᵖ U]
  [SMulCommClass E Cᵐᵒᵖ U]

omit [SMulCommClass E Cᵐᵒᵖ U] in
lemma mul_formula (x y : Algebra C E U) :
    x * y = ((x.fst.1 * y.fst.1, x.fst.2 * y.fst.2),
      x.fst.2 • (offValue y.snd) + MulOpposite.op y.fst.1 • (offValue x.snd)) := rfl

def toC : Algebra C E U →+* C where
  toFun x := x.fst.1
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

omit [SMulCommClass E Cᵐᵒᵖ U] in
lemma toC_surjective : Function.Surjective (toC C E U) :=
  fun c => ⟨((c, 0), 0), rfl⟩

def rightCornerSection :
    ((ModuleCat.restrictScalars (toC C E U).op).obj (ModuleCat.of Cᵐᵒᵖ Cᵐᵒᵖ)) →ₗ[
      (Algebra C E U)ᵐᵒᵖ] (Algebra C E U)ᵐᵒᵖ where
  toFun c := MulOpposite.op ((c.unop, 0), 0)
  map_add' c d := by
    apply MulOpposite.unop_injective
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · rfl
      · exact (zero_add (0 : E)).symm
    · exact (zero_add (0 : U)).symm
  map_smul' r c := by
    apply MulOpposite.unop_injective
    apply TrivSqZeroExt.ext
    · apply Prod.ext
      · rfl
      · exact (zero_mul _).symm
    · change 0 = (0 : E) • (offValue r.unop.snd) + MulOpposite.op r.unop.fst.1 • (0 : U)
      simp

lemma rightCorner_projective :
    Module.Projective (Algebra C E U)ᵐᵒᵖ
      ((ModuleCat.restrictScalars (toC C E U).op).obj (ModuleCat.of Cᵐᵒᵖ Cᵐᵒᵖ)) := by
  apply Module.Projective.of_split (rightCornerSection C E U)
    (Module.compHom.toLinearMap (toC C E U).op)
  ext x
  rfl

lemma right_little_lower_bound :
    littleFinitisticDimension Cᵐᵒᵖ ≤ littleFinitisticDimension (Algebra C E U)ᵐᵒᵖ := by
  let := rightCorner_projective C E U
  apply littleFinitisticDimension_le_restrictScalars (toC C E U).op
  intro c
  obtain ⟨t, ht⟩ := toC_surjective C E U c.unop
  exact ⟨MulOpposite.op t, congrArg MulOpposite.op ht⟩

lemma right_big_lower_bound :
    bigFinitisticDimension Cᵐᵒᵖ ≤ bigFinitisticDimension (Algebra C E U)ᵐᵒᵖ := by
  let := rightCorner_projective C E U
  apply bigFinitisticDimension_le_restrictScalars (toC C E U).op
  intro c
  obtain ⟨t, ht⟩ := toC_surjective C E U c.unop
  exact ⟨MulOpposite.op t, congrArg MulOpposite.op ht⟩

variable (k : Type v) [Field k] [_root_.Algebra k C] [_root_.Algebra k E] [Module k U]
  [IsScalarTower k E U] [IsScalarTower k Cᵐᵒᵖ U]
  [FiniteDimensional k C] [FiniteDimensional k E] [FiniteDimensional k U]

omit [Module E U] [Module Cᵐᵒᵖ U] [SMulCommClass E Cᵐᵒᵖ U]
  [IsScalarTower k E U] [IsScalarTower k Cᵐᵒᵖ U] in
lemma finiteDimensional : FiniteDimensional k (Algebra C E U) :=
  inferInstanceAs (FiniteDimensional k ((C × E) × OffDiagonal C E U))

end TriangularConstruction

end LittleFinitistic
end
end
end

end OAI

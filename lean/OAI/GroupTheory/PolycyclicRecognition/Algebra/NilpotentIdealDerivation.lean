import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentCodimensionOne
import Mathlib.Algebra.Lie.Derivation.Basic

namespace OAI

/-! # The nilpotent derivation in a codimension-one decomposition -/

noncomputable section
namespace PolycyclicRecognition.LieCodimensionOneData

open LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] (D : LieCodimensionOneData L)

def derivation : LieDerivation ℝ D.ideal D.ideal where
  toLinearMap := LieModule.toEnd ℝ L D.ideal D.unit
  leibniz' x y := by
    apply Subtype.ext
    change ⁅D.unit, ⁅(x : L), (y : L)⁆⁆ =
      ⁅(x : L), ⁅D.unit, (y : L)⁆⁆ - ⁅(y : L), ⁅D.unit, (x : L)⁆⁆
    rw [← lie_skew (y : L) ⁅D.unit, (x : L)⁆, sub_neg_eq_add, add_comm]
    exact leibniz_lie D.unit (x : L) (y : L)

theorem ideal_nilpotent_module [LieRing.IsNilpotent L] : LieModule.IsNilpotent L D.ideal := by
  have : LieModule.IsNilpotent L (⊤ : LieSubmodule ℝ L L) :=
    (LieModule.isNilpotent_of_top_iff' (R := ℝ) (L := L) (M := L)).mpr inferInstance
  exact LieModule.isNilpotent_of_le ℝ L L D.ideal ⊤ le_top

theorem ideal_nilpotent [LieRing.IsNilpotent L] : LieRing.IsNilpotent D.ideal := by
  have := D.ideal_nilpotent_module
  infer_instance

theorem derivation_nilpotent [LieRing.IsNilpotent L] : IsNilpotent D.derivation.toLinearMap := by
  have := D.ideal_nilpotent_module
  exact LieModule.isNilpotent_toEnd_of_isNilpotent ℝ L D.ideal D.unit

/-- In the split coordinates the bracket is the semidirect-product bracket. -/
theorem split_lie (x y : D.ideal) (s t : ℝ) :
    ⁅D.split (x, s), D.split (y, t)⁆ =
      D.split (⁅x, y⁆ + s • D.derivation y - t • D.derivation x, 0) := by
  change ⁅(x : L) + s • D.unit, (y : L) + t • D.unit⁆ =
    (⁅(x : L), (y : L)⁆ + s • ⁅D.unit, (y : L)⁆ - t • ⁅D.unit, (x : L)⁆) +
      (0 : ℝ) • D.unit
  simp only [add_lie, lie_add, smul_lie, lie_smul, lie_self, smul_zero, zero_smul,
    add_zero]
  rw [← lie_skew (x : L) D.unit, smul_neg]
  abel

end PolycyclicRecognition.LieCodimensionOneData

end

end OAI

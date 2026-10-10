import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealNormedLieAlgebra
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.RingTheory.Nilpotent.Basic

namespace OAI

/-! # One-parameter Lie automorphisms from a nilpotent derivation -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

local instance : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

def nilpotentDerivationFlow (t : ℝ) : L ≃ₗ⁅ℝ⁆ L :=
  (t • D).exp (by
    change IsNilpotent (t • D.toLinearMap)
    exact hD.smul t)

theorem nilpotentDerivationFlow_zero (x : L) : nilpotentDerivationFlow D hD 0 x = x := by
  change IsNilpotent.exp (0 • D.toLinearMap) x = x
  rw [zero_smul, IsNilpotent.exp_zero]
  rfl

theorem nilpotentDerivationFlow_add (s t : ℝ) (x : L) :
    nilpotentDerivationFlow D hD (s + t) x =
      nilpotentDerivationFlow D hD s (nilpotentDerivationFlow D hD t x) := by
  change IsNilpotent.exp ((s + t) • D.toLinearMap) x =
    IsNilpotent.exp (s • D.toLinearMap) (IsNilpotent.exp (t • D.toLinearMap) x)
  have hc : Commute (s • D.toLinearMap) (t • D.toLinearMap) := by
    change (s • D.toLinearMap) * (t • D.toLinearMap) =
      (t • D.toLinearMap) * (s • D.toLinearMap)
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm s t]
  rw [add_smul, IsNilpotent.exp_add_of_commute hc (hD.smul s) (hD.smul t)]
  rfl

end PolycyclicRecognition

end

end OAI

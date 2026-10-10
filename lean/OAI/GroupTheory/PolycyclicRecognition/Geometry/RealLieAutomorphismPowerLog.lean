import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealLieJordanDecomposition
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealSemisimpleCommutingLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.UnipotentLieFlow
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RealMatrixSquareLogarithm

namespace OAI

/-! # A finite power of every real Lie automorphism has a derivation logarithm

The semisimple logarithm respects spectral multiplicative relations and the
real form. Its commutation with the unipotent logarithm allows the two flows
to be combined.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance realLiePowerLogRationalModule : Module ℚ L :=
  Module.compHom L (algebraMap ℚ ℝ)

theorem real_lie_automorphism_has_commuting_power_log (A : L ≃ₗ⁅ℝ⁆ L) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℝ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        A.toLinearMap ^ m ∧
      ∀ T : Module.End ℝ L, Commute A.toLinearMap T → Commute D.toLinearMap T := by
  obtain ⟨S, U, hS, hU, hSU, hA, hcentral⟩ := real_lie_jordan_decomposition_centralizer A
  obtain ⟨m, hm, B, hB, hcomm⟩ :=
    real_semisimple_lie_automorphism_has_commuting_power_log S hS
  let C := unipotentLieLogarithm U hU
  let b : Module.End ℝ L := B.toLinearMap
  let c : Module.End ℝ L := C.toLinearMap
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hBC : Commute b c :=
    commute_nilpotentLog_right ((hcomm U.toLinearMap hSU).sub_right (Commute.one_right _))
  have hEB : NormedSpace.exp (E b) = E (S.toLinearMap ^ m) := by
    apply ContinuousLinearMap.ext
    intro x
    exact DFunLike.congr_fun hB x
  have hEC : NormedSpace.exp (E c) = E U.toLinearMap := by
    have he : E c = nilpotentLog (E (U.toLinearMap - 1)) :=
      (nilpotentLog_map E.toRingHom (U.toLinearMap - 1) hU).symm
    have hn : IsNilpotent (E (U.toLinearMap - 1)) := hU.map E.toRingHom
    rw [he, analytic_exp_nilpotentLog _ hn, map_sub, map_one]
    abel
  have hc : Commute (E b) (E c) := hBC.map E.toRingHom
  refine ⟨m, hm, B + m • C, ?_, ?_⟩
  · have he : NormedSpace.exp (E b + m • E c) =
        E (A.toLinearMap ^ m) := by
      rw [NormedSpace.exp_add_of_commute (hc.smul_right m), NormedSpace.exp_nsmul,
        hEB, hEC, ← map_pow, ← map_mul, ← hSU.mul_pow, ← hA]
    exact congrArg (fun T : L →L[ℝ] L => T.toLinearMap) he
  · intro T hT
    obtain ⟨hST, hUT⟩ := hcentral T hT
    have hbT : Commute b T := hcomm T hST
    have hcT : Commute c T :=
      (commute_nilpotentLog_right (hUT.symm.sub_right (Commute.one_right _))).symm
    exact hbT.add_left (hcT.smul_left m)

theorem real_lie_automorphism_has_power_log (A : L ≃ₗ⁅ℝ⁆ L) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℝ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        A.toLinearMap ^ m := by
  obtain ⟨m, hm, D, he, _⟩ := real_lie_automorphism_has_commuting_power_log A
  exact ⟨m, hm, D, he⟩

end PolycyclicRecognition

end

end OAI

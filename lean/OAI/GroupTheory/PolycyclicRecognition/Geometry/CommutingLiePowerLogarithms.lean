import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealLieAutomorphismPowerLog

namespace OAI

/-! # Commuting logarithms for finitely many commuting Lie automorphisms

A single positive power works for the entire finite family. The logarithms
commute because each constructed logarithm commutes with the full commutant
of its original automorphism.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L I : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L] [Fintype I]

theorem commuting_lie_automorphisms_have_power_logs (A : I → L ≃ₗ⁅ℝ⁆ L)
    (hA : ∀ i j, Commute (A i).toLinearMap (A j).toLinearMap) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : I → LieDerivation ℝ L L,
      (∀ i, (NormedSpace.exp (LinearMap.toContinuousLinearMap (D i).toLinearMap)).toLinearMap =
        (A i).toLinearMap ^ m) ∧
      ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap := by
  classical
  choose n hn B hB hcomm using fun i => real_lie_automorphism_has_commuting_power_log (A i)
  let m := ∏ i, n i
  have hm : 0 < m := Finset.prod_pos (fun i _ => hn i)
  have hd (i : I) : n i ∣ m := Finset.dvd_prod_of_mem (fun j => n j) (Finset.mem_univ i)
  let q := fun i => m / n i
  have hq (i : I) : n i * q i = m := Nat.mul_div_cancel' (hd i)
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  refine ⟨m, hm, fun i => q i • B i, ?_, ?_⟩
  · intro i
    have he : NormedSpace.exp (E (B i).toLinearMap) = E ((A i).toLinearMap ^ n i) := by
      apply ContinuousLinearMap.ext
      intro x
      exact DFunLike.congr_fun (hB i) x
    have hep : NormedSpace.exp (q i • E (B i).toLinearMap) = E ((A i).toLinearMap ^ m) := by
      rw [NormedSpace.exp_nsmul, he, ← map_pow, ← pow_mul, hq]
    exact congrArg (fun T : L →L[ℝ] L => T.toLinearMap) hep
  · intro i j
    have hc : Commute (B i).toLinearMap (B j).toLinearMap :=
      (hcomm j _ ((hcomm i _ (hA i j)).symm)).symm
    exact (hc.smul_left (q i)).smul_right (q j)

end PolycyclicRecognition

end

end OAI

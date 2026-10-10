import OAI.GroupTheory.PolycyclicRecognition.Geometry.FixedVectorLieLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CommutingLiePowerLogarithms

namespace OAI

/-! # Commuting real logarithms retaining the fixed directions -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance fixedPowerLogRationalModule : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

theorem real_lie_automorphism_has_fixed_power_log (A : L ≃ₗ⁅ℝ⁆ L) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℝ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        A.toLinearMap ^ m ∧
      (∀ T : Module.End ℝ L, Commute A.toLinearMap T → Commute D.toLinearMap T) ∧
      ∀ x, A x = x → D x = 0 := by
  obtain ⟨S, U, hS, hU, hSU, hA, hcentral⟩ := real_lie_jordan_decomposition_centralizer A
  obtain ⟨m, hm, B, hB, hcomm, hfixed⟩ := real_semisimple_has_fixed_power_log S hS
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
  refine ⟨m, hm, B + m • C, ?_, ?_, ?_⟩
  · have he : NormedSpace.exp (E b + m • E c) = E (A.toLinearMap ^ m) := by
      rw [NormedSpace.exp_add_of_commute (hc.smul_right m), NormedSpace.exp_nsmul,
        hEB, hEC, ← map_pow, ← map_mul, ← hSU.mul_pow, ← hA]
    exact congrArg (fun T : L →L[ℝ] L => T.toLinearMap) he
  · intro T hT
    obtain ⟨hST, hUT⟩ := hcentral T hT
    have hbT : Commute b T := hcomm T hST
    have hcT : Commute c T :=
      (commute_nilpotentLog_right (hUT.symm.sub_right (Commute.one_right _))).symm
    exact hbT.add_left (hcT.smul_left m)
  · intro x hx
    obtain ⟨hs, hu⟩ := lie_jordan_fixed A S U hS hU hSU hA x hx
    change B x + m • C x = 0
    rw [hfixed x hs, show C x = 0 from unipotentLieLogarithm_fixed U hU x hu]
    simp

variable {I : Type} [Fintype I]

theorem commuting_lie_automorphisms_have_fixed_power_logs (A : I → L ≃ₗ⁅ℝ⁆ L)
    (hA : ∀ i j, Commute (A i).toLinearMap (A j).toLinearMap) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : I → LieDerivation ℝ L L,
      (∀ i, (NormedSpace.exp (LinearMap.toContinuousLinearMap (D i).toLinearMap)).toLinearMap =
        (A i).toLinearMap ^ m) ∧
      (∀ i j, Commute (D i).toLinearMap (D j).toLinearMap) ∧
      (∀ i T, Commute (A i).toLinearMap T → Commute (D i).toLinearMap T) ∧
      ∀ i x, A i x = x → D i x = 0 := by
  classical
  choose n hn B hB hcomm hfixed using fun i => real_lie_automorphism_has_fixed_power_log (A i)
  let m := ∏ i, n i
  have hm : 0 < m := Finset.prod_pos (fun i _ => hn i)
  have hd (i : I) : n i ∣ m := Finset.dvd_prod_of_mem (fun j => n j) (Finset.mem_univ i)
  let q := fun i => m / n i
  have hq (i : I) : n i * q i = m := Nat.mul_div_cancel' (hd i)
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  refine ⟨m, hm, fun i => q i • B i, ?_, ?_, ?_, ?_⟩
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
  · intro i T hT
    exact (hcomm i T hT).smul_left (q i)
  · intro i x hx
    change q i • B i x = 0
    rw [hfixed i x hx, smul_zero]

end PolycyclicRecognition

end

end OAI

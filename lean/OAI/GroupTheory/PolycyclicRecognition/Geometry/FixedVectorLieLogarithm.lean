import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealLieAutomorphismPowerLog
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteLogCoefficientBound

namespace OAI

/-! # The chosen Lie logarithm vanishes on fixed vectors

The compatible spectral character has value zero at the identity. This
retains the quotient directions when extending the integral nilshadow action.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct

section Complex
variable {L : Type} [ComplexNormedLieAlgebra L] [FiniteDimensional ℂ L] [CompleteSpace L]

omit [FiniteDimensional ℂ L] [CompleteSpace L] in
theorem spectralLogValue_one (S : Module.End ℂ L)
    (l : spectralUnitGroup S →* Multiplicative ℂ) : spectralLogValue S l 1 = 0 := by
  have h := spectralLogValue_unit S l (1 : spectralUnitGroup S)
  simpa only [OneMemClass.coe_one, Units.val_one, map_one, toAdd_one] using h

omit [CompleteSpace L] in
theorem spectralLieDerivation_fixed (S : L ≃ₗ⁅ℂ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (l : spectralUnitGroup S.toLinearMap →* Multiplicative ℂ) (x : L) (hx : S x = x) :
    spectralLieDerivation S hS l x = 0 := by
  have hx' : x ∈ Module.End.eigenspace S.toLinearMap 1 := by
    rw [Module.End.mem_eigenspace_iff, one_smul]
    exact hx
  change semisimpleSpectralOperator S.toLinearMap hS
    (spectralLogValue S.toLinearMap l) x = 0
  rw [semisimpleSpectralOperator_apply _ _ _ hx', spectralLogValue_one, zero_smul]

theorem semisimple_real_form_has_fixed_power_log (S : L ≃ₗ⁅ℂ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (c : L →ₗ⋆[ℂ] L) (hc : ∀ x, c (S x) = S (c x)) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℂ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        S.toLinearMap ^ m ∧ (∀ x, c (D x) = D (c x)) ∧
      (∀ T : Module.End ℂ L, Commute S.toLinearMap T → Commute D.toLinearMap T) ∧
      ∀ x, S x = x → D x = 0 := by
  obtain ⟨m, hm, l, he, hr⟩ := spectralUnitGroup_logarithm S.toLinearMap
  exact ⟨m, hm, spectralLieDerivation S hS l,
    exp_compatibleSpectralLog S.toLinearMap hS ((Module.End.isUnit_iff _).mpr S.bijective) l m he,
    compatibleSpectralLog_conjugation S.toLinearMap hS l hr c hc,
    fun T hT => semisimpleSpectralOperator_commute S.toLinearMap hS _ T hT,
    spectralLieDerivation_fixed S hS l⟩

end Complex

section Real
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
local instance fixedVectorLogRationalModule : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

theorem real_semisimple_has_fixed_power_log (S : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap) :
    ∃ m : ℕ, 0 < m ∧ ∃ D : LieDerivation ℝ L L,
      (NormedSpace.exp (LinearMap.toContinuousLinearMap D.toLinearMap)).toLinearMap =
        S.toLinearMap ^ m ∧
      (∀ T : Module.End ℝ L, Commute S.toLinearMap T → Commute D.toLinearMap T) ∧
      ∀ x, S x = x → D x = 0 := by
  let : ComplexNormedLieAlgebra (ℂ ⊗[ℝ] L) := complexificationNormedLie L
  let CS := complexifiedLieEquiv L S
  obtain ⟨m, hm, D, he, hc, hcomm, hfixed⟩ := semisimple_real_form_has_fixed_power_log CS
    (complexifiedLieEquiv_semisimple L S hS) (complexificationConjSemilinear L)
    (complexifiedLieEquiv_conj L S)
  refine ⟨m, hm, complexDerivationRealPart L D, ?_, ?_, ?_⟩
  · apply realEnd_baseChange_injective L
    change ((NormedSpace.exp (LinearMap.toContinuousLinearMap
        (complexDerivationRealPart L D).toLinearMap)).toLinearMap).baseChange ℂ =
      (S.toLinearMap ^ m).baseChange ℂ
    rw [complexifiedEnd_exp, complexDerivationRealPart_baseChange L D hc, he,
      LinearMap.baseChange_pow]
    rfl
  · intro T hT
    let f := Module.End.baseChangeHom ℝ ℂ L
    have ht : Commute D.toLinearMap (T.baseChange ℂ) := hcomm _ (hT.map f)
    apply realEnd_baseChange_injective L
    change f ((complexDerivationRealPart L D).toLinearMap * T) =
      f (T * (complexDerivationRealPart L D).toLinearMap)
    simp only [map_mul]
    change (complexDerivationRealPart L D).toLinearMap.baseChange ℂ * T.baseChange ℂ =
      T.baseChange ℂ * (complexDerivationRealPart L D).toLinearMap.baseChange ℂ
    rw [complexDerivationRealPart_baseChange L D hc]
    exact ht.eq
  · intro x hx
    apply complexificationLieHom_injective L
    change (1 : ℂ) ⊗ₜ[ℝ] complexDerivationRealPart L D x = (1 : ℂ) ⊗ₜ[ℝ] (0 : L)
    rw [complexDerivationRealPart_embed L D hc, TensorProduct.tmul_zero]
    apply hfixed
    change (1 : ℂ) ⊗ₜ[ℝ] S x = (1 : ℂ) ⊗ₜ[ℝ] x
    rw [hx]

omit [FiniteDimensional ℝ L] in
theorem lie_jordan_fixed (A S U : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1)) (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap) (x : L) (hx : A x = x) :
    S x = x ∧ U x = x := by
  have hc : Commute A.toLinearMap S.toLinearMap := by
    rw [hA]
    exact (Commute.refl _).mul_left hSU.symm
  have hn : IsNilpotent (A.toLinearMap - S.toLinearMap) := by
    rw [hA, show S.toLinearMap * U.toLinearMap - S.toLinearMap =
      S.toLinearMap * (U.toLinearMap - 1) by noncomm_ring]
    obtain ⟨k, hk⟩ := hU
    exact ⟨k, by rw [(hSU.sub_right (Commute.one_right _)).mul_pow, hk, mul_zero]⟩
  have hx' : x ∈ Module.End.genEigenspace A.toLinearMap 1 1 := by
    rw [Module.End.genEigenspace_one]
    simp only [LinearMap.mem_ker, LinearMap.sub_apply,
      one_smul, Module.End.one_apply]
    exact sub_eq_zero.mpr hx
  have hs : S x = x := by
    have h := Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
      hx' hc hS.isFinitelySemisimple hn
    change S x = (1 : ℝ) • x at h
    simpa only [one_smul] using h
  refine ⟨hs, S.injective ?_⟩
  have ha := LinearMap.congr_fun hA x
  change A x = S (U x) at ha
  exact ha.symm.trans (hx.trans hs.symm)

theorem unipotentLieLogarithm_fixed (A : L ≃ₗ⁅ℝ⁆ L)
    (hA : IsNilpotent (A.toLinearMap - 1)) (x : L) (hx : A x = x) :
    unipotentLieLogarithm A hA x = 0 := by
  change nilpotentLog (A.toLinearMap - 1) x = 0
  unfold nilpotentLog
  rw [finiteNilpotentLog_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hz : (A.toLinearMap - 1) x = 0 := by
    change A x - x = 0
    rw [hx, sub_self]
  have hp : ((A.toLinearMap - 1) ^ (i.val + 1)) x = 0 := by
    rw [pow_succ, Module.End.mul_apply, hz, map_zero]
  rw [hp, smul_zero]

end Real
end PolycyclicRecognition

end

end OAI

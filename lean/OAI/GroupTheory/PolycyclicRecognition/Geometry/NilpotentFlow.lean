import OAI.GroupTheory.PolycyclicRecognition.Geometry.ContinuousFlowDistortion
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace OAI

/-! # Nilpotent corrections in a contracting weight flow

The nilpotent part of the infinitesimal action gives a polynomial bound
for its actual analytic exponential. Coupled with scalar exponential
contraction, it gives logarithmic metric distortion of the weight chart.
-/

noncomputable section

namespace PolycyclicRecognition

/-- Split the scalar weight from the nilpotent part in the actual analytic
exponential of the infinitesimal generator. -/
theorem exp_smul_sub_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (N : A) (t : ℝ) :
    NormedSpace.exp (t • (N - 1)) = Real.exp (-t) • NormedSpace.exp (t • N) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Commute ((-t) • (1 : A)) (t • N) := by
    change ((-t) • (1 : A)) * (t • N) = (t • N) * ((-t) • (1 : A))
    simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commutes (-t) (t • N)
  have he : NormedSpace.exp ((-t) • (1 : A)) = Real.exp (-t) • (1 : A) := by
    simpa only [Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) (-t)).symm
  rw [show t • (N - 1) = (-t) • (1 : A) + t • N by module,
    NormedSpace.exp_add_of_commute hc, he, smul_mul_assoc, one_mul]

/-- The actual exponential of a nilpotent operator has polynomial growth
in its real parameter, with an explicit uniform coefficient. -/
theorem norm_exp_smul_nilpotent_le
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]
    (N : A) {c : ℕ} (hN : N ^ (c + 1) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • N)‖ ≤
      ((c : ℝ) + 1) * (1 + ‖N‖) ^ c * (1 + t) ^ c := by
  have hpow : (t • N) ^ (c + 1) = 0 := by simp [smul_pow, hN]
  have hbound : ‖NormedSpace.exp (t • N) - 1‖ ≤
      (c : ℝ) * (1 + t * ‖N‖) ^ c := by
    apply norm_exp_sub_one_le_of_pow_eq_zero _ hpow (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hbase : 1 + t * ‖N‖ ≤ (1 + ‖N‖) * (1 + t) := by
    nlinarith [norm_nonneg N]
  have hpoly : (1 + t * ‖N‖) ^ c ≤ (1 + ‖N‖) ^ c * (1 + t) ^ c := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hbase c
  have hone : 1 ≤ (1 + ‖N‖) ^ c * (1 + t) ^ c :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg N]))
      (one_le_pow₀ (by linarith))
  calc
    ‖NormedSpace.exp (t • N)‖ ≤ ‖NormedSpace.exp (t • N) - 1‖ + ‖(1 : A)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ (c : ℝ) * (1 + t * ‖N‖) ^ c + 1 := by simpa only [norm_one] using add_le_add hbound le_rfl
    _ ≤ (c : ℝ) * ((1 + ‖N‖) ^ c * (1 + t) ^ c) +
        ((1 + ‖N‖) ^ c * (1 + t) ^ c) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg _)) hone
    _ = _ := by ring

/-- The infinitesimal nilpotent correction, with its actual operator
exponential, has exactly the polynomially corrected contraction needed above. -/
theorem norm_contracted_nilpotent_flow_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (v : V) {t : ℝ} (ht : 0 ≤ t) :
    ‖Real.exp (-t) • (NormedSpace.exp (t • N)) v‖ ≤
      (((c : ℝ) + 1) * (1 + ‖N‖) ^ c) * (1 + t) ^ c * Real.exp (-t) * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t) * ‖(NormedSpace.exp (t • N)) v‖ ≤
        Real.exp (-t) * (‖NormedSpace.exp (t • N)‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.exp_pos _).le
    _ ≤ Real.exp (-t) *
        ((((c : ℝ) + 1) * (1 + ‖N‖) ^ c * (1 + t) ^ c) * ‖v‖) := by
      gcongr
      exact norm_exp_smul_nilpotent_le N hN ht
    _ = _ := by ring

/-- A continuous weight chart with a nilpotent correction in its contracting
action is logarithmically distorted. This is the individual weight-space
estimate, before taking bounded products of generator directions. -/
theorem logarithmic_distortion_of_nilpotent_flow
    {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Nontrivial V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp (Real.exp (-t) • (NormedSpace.exp (t • N)) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  exact logarithmic_distortion_of_continuous_flow Exp hExp d hd hd0 hmul
    (fun t v => Real.exp (-t) • (NormedSpace.exp (t • N)) v)
    (C := ((c : ℝ) + 1) * (1 + ‖N‖) ^ c) (by positivity) c hconj
    (fun v _ ht => norm_contracted_nilpotent_flow_le N hN v ht)

/-- The same distortion conclusion stated directly for a generator whose
nilpotent part is `N` and whose real weight is `-1`. -/
theorem logarithmic_distortion_of_weight_generator
    {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Nontrivial V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp ((NormedSpace.exp (t • (N - 1))) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  apply logarithmic_distortion_of_nilpotent_flow Exp hExp d hd hd0 hmul N hN
  intro v t ht
  have hh := hconj v t ht
  rw [exp_smul_sub_one N t] at hh
  exact hh

end PolycyclicRecognition

end

end OAI

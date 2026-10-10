import OAI.Combinatorics.EditApproximation.Refinement.PhysicalCoarseSamplingWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedCoarseBitWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
open MeasureTheory Filter

section Symbolic
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)



theorem symbolicComputedExecutionCoarseSamplingWork_integrable :
    Integrable (symbolicComputedExecutionCoarseSamplingWork source target N depth encode)
      (physicalCoarseExecutionLaw (R := R) source target N (integerParameters N).P
        (inputHeight N) B depth) := by
  let μ := coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)
  let range := physicalFamilyRange (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)
  let f := fun outcome : PhysicalCoarseDraw source target B depth × (∀ key, Fin (range key)) =>
    symbolicComputedExecutionCoarseSamplingWork source target N depth encode
      (outcome.1, (fun _ => 0, outcome.2))
  have hf : Integrable f ((μ.prod (rejectionRuntimeArrayLaw range)).map
      (rejectionProductAccepted range)) := by
    rw [rejectionProductAccepted_law]
    exact Integrable.of_finite
  exact hf.comp_measurable (rejectionProductAccepted_measurable range)
omit [NeZero B] in
theorem symbolicComputedExecutionCoarseSamplingWork_bound
    (execution : PhysicalCoarseExecution (R := R) source target N
      (integerParameters N).P (inputHeight N) B depth) :
    symbolicComputedExecutionCoarseSamplingWork source target N depth encode execution ≤
      (Nat.size B : ℝ) * symbolicComputedExecutionCoarseWork source target N depth encode execution := by
  exact physicalFamilyCoarseSamplingWork_bound source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).T (integerParameters N).S (computedSeedPassCount N)
    (inputHeight N ^ 2) (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    execution.2.2 depth (16384 * inputHeight N + 5) encode
    (localFinalRootRequest target N (integerParameters N).T (integerParameters N).S
      (inputHeight N) (Nat.two_pow_pos _) (finalTargetState target.length)) execution.1

end Symbolic



theorem computedExecutionCoarseSamplingWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarseSamplingWork source target N) (computedExecutionLaw source target N) :=
  symbolicComputedExecutionCoarseSamplingWork_integrable source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))

theorem computedExecutionCoarseSamplingWork_bound (source target : List ℕ) (N : ℕ)
    (execution : ComputedExecutionOutcome source target N) :
    computedExecutionCoarseSamplingWork source target N execution ≤
      (Nat.size (integerParameters N).B : ℝ) * computedExecutionCoarseWork source target N execution :=
  symbolicComputedExecutionCoarseSamplingWork_bound source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2)) execution

theorem computedExecutionCoarseSamplingWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionCoarseSamplingWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have he : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedExecutionCoarseWork_expected_near_linear (epsilon / 2) he,
    fixed_height_power_subpolynomial 2 (epsilon / 2) he,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hc hp hN hell
  intro source target hsize
  have hB := Nat.size_le_size (computed_coarse_B_upper N (by omega) hell)
  rw [Nat.size_pow] at hB
  have hH := computed_coarse_height_large N (by omega) hell
  have hsizeB : Nat.size (integerParameters N).B ≤ inputHeight N ^ 2 := by nlinarith only [hB, hH]
  have hb : (∫ execution, computedExecutionCoarseSamplingWork source target N execution
      ∂computedExecutionLaw source target N) ≤
      (Nat.size (integerParameters N).B : ℝ) *
      (∫ execution, computedExecutionCoarseWork source target N execution ∂computedExecutionLaw source target N) := by
    calc
      _ ≤ ∫ execution, (Nat.size (integerParameters N).B : ℝ) *
          computedExecutionCoarseWork source target N execution ∂computedExecutionLaw source target N :=
        integral_mono (computedExecutionCoarseSamplingWork_integrable source target N)
          ((computedExecutionCoarseWork_integrable source target N).const_mul _)
          (computedExecutionCoarseSamplingWork_bound source target N)
      _ = _ := by rw [integral_const_mul]
  have hsizeBReal : (Nat.size (integerParameters N).B : ℝ) ≤ (inputHeight N : ℝ) ^ 2 := by exact_mod_cast hsizeB
  calc
    _ ≤ (Nat.size (integerParameters N).B : ℝ) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      hb.trans (mul_le_mul_of_nonneg_left (hc source target hsize) (Nat.cast_nonneg _))
    _ ≤ (inputHeight N : ℝ) ^ 2 * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hsizeBReal (by positivity)
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI

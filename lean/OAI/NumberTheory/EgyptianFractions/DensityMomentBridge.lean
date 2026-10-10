import OAI.NumberTheory.EgyptianFractions.DensityAssembly
import OAI.NumberTheory.EgyptianFractions.DivisorFactorBound
import OAI.NumberTheory.EgyptianFractions.ResidueLevels

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- The density descent and the arithmetic moment use exactly the same count. -/
theorem densityDivisorCount_eq_truncated (X : ℝ) (n : ℕ) :
    densityDivisorCount X n = (truncatedDivisorCount X n : ℝ) := rfl

/-- A common exponential size parameter for cutoffs and translated divisors. -/
def densityMomentParameter (DM : ℝ) : ℝ := 8 * (DM + 2) + DM + 1

theorem densityMomentParameter_ge_one {DM : ℝ} (hDM : 1 < DM) :
    1 ≤ densityMomentParameter DM := by
  unfold densityMomentParameter
  linarith

/-- Each nonterminal geometric level is inside the divisor-moment window. -/
theorem residue_level_moment_window
    {DM S m η : ℝ} (hDM : 1 < DM) (hS : 0 ≤ S)
    (hm : 0 < m) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hmlo : S / (2 * Real.log S) ≤ m)
    {j : ℕ} (hj : j < ResidueLevels.depth ((DM + 2) * S) m η) :
    S / (2 * Real.log S) ≤
        Real.log (ResidueLevels.level ((DM + 2) * S) m η j) ∧
    Real.log (ResidueLevels.level ((DM + 2) * S) m η j) ≤
        densityMomentParameter DM * S ∧
    Real.sqrt (ResidueLevels.level ((DM + 2) * S) m η j) ≤
        ResidueLevels.level ((DM + 2) * S) m η (j + 1) ∧
    ResidueLevels.level ((DM + 2) * S) m η (j + 1) ≤
        ResidueLevels.level ((DM + 2) * S) m η j := by
  have hjlog := (ResidueLevels.before_depth_iff hm hη j).mp hj
  have hsub : 0 ≤ η * m * (j : ℝ) := by positivity
  have hDS : (DM + 2) * S ≤ densityMomentParameter DM * S := by
    apply mul_le_mul_of_nonneg_right _ hS
    unfold densityMomentParameter
    linarith
  refine ⟨?_, ?_, ResidueLevels.sqrt_level_le_next hm hη hηhalf hj, ?_⟩
  · simpa only [ResidueLevels.level, Real.log_exp] using hmlo.trans hjlog.le
  · simp only [ResidueLevels.level, Real.log_exp]
    linarith
  · exact (ResidueLevels.level_strictAnti hm hη (Nat.lt_succ_self j)).le

/-- The changing factor and any divisor of the common denominator give a
shift with the same fixed exponential parameter, uniformly in the level. -/
theorem residue_level_shift_bound
    {DM S m η : ℝ} (_hDM : 1 < DM) (hS : 0 ≤ S)
    {C M t : ℕ} (hCpos : 0 < C) (hMpos : 0 < M)
    (hC : (C : ℝ) ≤ Real.exp (8 * (DM + 2) * S))
    (hM : (M : ℝ) ≤ Real.exp (DM * S)) (ht : t ∣ M) (j : ℕ) :
    ((ResidueLevels.factor ((DM + 2) * S) m η S C j * t : ℕ) : ℝ) ≤
      Real.exp (densityMomentParameter DM * S) := by
  have htM : (t : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hMpos ht
  have hfactor : (ResidueLevels.factor ((DM + 2) * S) m η S C j : ℝ) ≤ C := by
    exact_mod_cast ResidueLevels.factor_le hCpos j
  calc
    _ ≤ (C : ℝ) * M := by
      push_cast
      exact mul_le_mul hfactor htM (Nat.cast_nonneg t) (Nat.cast_nonneg C)
    _ ≤ Real.exp (8 * (DM + 2) * S) * Real.exp (DM * S) :=
      mul_le_mul hC hM (Nat.cast_nonneg M) (Real.exp_pos _).le
    _ = Real.exp ((8 * (DM + 2) + DM) * S) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (densityMomentParameter DM * S) := by
      apply Real.exp_le_exp.mpr
      unfold densityMomentParameter
      nlinarith

/-- Pointwise adapter from the uniform arithmetic estimate to the exact
shifted-moment field consumed by `DensityResidueFamily`. -/
theorem residue_level_moment_of_uniform
    {DM S m η r : ℝ} (hDM : 1 < DM) (hS : 0 ≤ S)
    (hm : 0 < m) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hmlo : S / (2 * Real.log S) ≤ m)
    (hmoment : ∀ (X Y : ℝ) (N : ℕ),
      S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ densityMomentParameter DM * S →
      Real.sqrt X ≤ Y → Y ≤ X →
      (N : ℝ) ≤ Real.exp (densityMomentParameter DM * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊,
        (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
          Y * Real.exp (S ^ (1 / 4 : ℝ)))
    {C M t : ℕ} (hCpos : 0 < C) (hMpos : 0 < M)
    (hC : (C : ℝ) ≤ Real.exp (8 * (DM + 2) * S))
    (hM : (M : ℝ) ≤ Real.exp (DM * S)) (ht : t ∣ M)
    {j : ℕ} (hj : j < ResidueLevels.depth ((DM + 2) * S) m η) :
    (∑ h ∈ Finset.Icc 1 ⌊ResidueLevels.level ((DM + 2) * S) m η (j + 1)⌋₊,
      densityDivisorCount (ResidueLevels.level ((DM + 2) * S) m η j)
        (ResidueLevels.factor ((DM + 2) * S) m η S C j * t + h) ^ r) ≤
      ResidueLevels.level ((DM + 2) * S) m η (j + 1) *
        Real.exp (S ^ (1 / 4 : ℝ)) := by
  obtain ⟨hlo, hhi, hsqrt, hnext⟩ :=
    residue_level_moment_window hDM hS hm hη hηhalf hmlo hj
  simpa only [densityDivisorCount_eq_truncated] using
    hmoment _ _ _ hlo hhi hsqrt hnext
      (residue_level_shift_bound hDM hS hCpos hMpos hC hM ht j)

/-- One eventual scalar moment theorem supplies every level and divisor
simultaneously. The threshold does not depend on `C`, `M`, `j`, or `t`. -/
theorem eventually_residue_level_moment_of_uniform
    (DM η r : ℝ) (hDM : 1 < DM) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hmoment : ∀ᶠ S : ℝ in atTop, ∀ (X Y : ℝ) (N : ℕ),
      S / (2 * Real.log S) ≤ Real.log X →
      Real.log X ≤ densityMomentParameter DM * S →
      Real.sqrt X ≤ Y → Y ≤ X →
      (N : ℝ) ≤ Real.exp (densityMomentParameter DM * S) →
      (∑ h ∈ Finset.Icc 1 ⌊Y⌋₊,
        (truncatedDivisorCount X (N + h) : ℝ) ^ r) ≤
          Y * Real.exp (S ^ (1 / 4 : ℝ))) :
    ∀ᶠ S : ℝ in atTop, ∀ C M : ℕ, 0 < C → 0 < M →
      (C : ℝ) ≤ Real.exp (8 * (DM + 2) * S) →
      (M : ℝ) ≤ Real.exp (DM * S) →
      ∀ j : ℕ, j < ResidueLevels.depth ((DM + 2) * S) (ResidueLevels.scale S) η →
      ∀ t : ℕ, t ∣ M →
      (∑ h ∈ Finset.Icc 1
          ⌊ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1)⌋₊,
        densityDivisorCount
          (ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η j)
          (ResidueLevels.factor ((DM + 2) * S) (ResidueLevels.scale S) η S C j * t + h)
          ^ r) ≤
        ResidueLevels.level ((DM + 2) * S) (ResidueLevels.scale S) η (j + 1) *
          Real.exp (S ^ (1 / 4 : ℝ)) := by
  filter_upwards [hmoment, ResidueLevels.eventually_scale_bounds,
    eventually_ge_atTop (0 : ℝ)] with S hmoment hscale hS
  intro C M hCpos hMpos hC hM j hj t ht
  have hm : (0 : ℝ) < ResidueLevels.scale S := by
    exact_mod_cast (show 0 < ResidueLevels.scale S by omega)
  exact residue_level_moment_of_uniform hDM hS hm hη hηhalf hscale.2.2.1
    hmoment hCpos hMpos hC hM ht hj

end Problem337

end

end OAI

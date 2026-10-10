import OAI.Probability.RadialTransition.FinitePartition

namespace OAI

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

def coreLift (t : ℝ) (x : Position) : ℝ := coreReal t ‖x‖

theorem continuous_coreLift (t : ℝ) : Continuous (coreLift t) :=
  (continuous_coreReal t).comp continuous_norm

theorem coreLift_nonneg (t : ℝ) (x : Position) : 0 ≤ coreLift t x := coreReal_nonneg t ‖x‖

theorem coreLift_bound (t : ℝ) (x : Position) : |coreLift t x| ≤ t ^ 2 := by
  rw [abs_of_nonneg (coreLift_nonneg t x)]
  exact coreReal_le t ‖x‖

theorem coreLift_compactSupport {t : ℝ} (ht : 1 ≤ t) : HasCompactSupport (coreLift t) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Position) 2)
  intro x hx
  by_contra h
  have hn : 2 < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using h
  apply hx
  exact coreReal_zero_outer (by linarith) (le_trans
    (by have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ht; norm_num at hh; simp only [one_div]; linarith)
    hn.le)

theorem integrable_coreLift {t : ℝ} (ht : 1 ≤ t) : Integrable (coreLift t) :=
  (continuous_coreLift t).integrable_of_hasCompactSupport (coreLift_compactSupport ht)

def coreIntegral (t : ℝ) : ℝ := ∫ x : Position, coreLift t x

theorem coreIntegral_nonneg (t : ℝ) : 0 ≤ coreIntegral t := integral_nonneg (coreLift_nonneg t)

theorem familyPotential_le_core {t : ℝ} {a R : ℕ → ℝ} (ht : 0 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (r : ℝ≥0) :
    familyPotential t a R r ≤ corePotential t r := by
  exact sub_le_self _ (mul_nonneg ht (attractionProfile_nonneg ha hR r))

theorem probability_energy_family_upper {t L : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hL : 0 < L) (N : ℕ) :
    (∫ x : Fin N → Position, energy (familyPotential t a R) x
      ∂Measure.pi (fun _ : Fin N => cubeProbability L)) ≤
      coreIntegral t * (N : ℝ)^2 / L^3 := by
  have hh := probability_energy_upper (continuous_familyPotential ha hR hs t)
    (bounded_familyPotential ha hR hs t) hL N (continuous_coreLift t)
    (coreLift_bound t) (integrable_coreLift ht) (coreLift_nonneg t)
    (fun x y => (familyPotential_le_core (by linarith) ha hR _).trans_eq (by
      simp only [corePotential, coreLift, coe_nndist, dist_eq_norm]))
  simpa only [coreIntegral, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using hh

theorem log_factorial_bounds (N : ℕ) :
    (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) ∧
      Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
  by_cases hN : N = 0
  · simp [hN]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  constructor
  · have hh := Stirling.le_log_factorial_stirling hN
    have hnlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
    have hpilog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
    linarith
  · have hf : (N.factorial : ℝ) ≤ (N : ℝ)^N := by exact_mod_cast Nat.factorial_le_pow N
    have hh := Real.log_le_log (by exact_mod_cast Nat.factorial_pos N) hf
    simpa only [Real.log_pow] using hh

def densityAt (L : ℝ) (N : ℕ) : ℝ := (N : ℝ) / L^3

theorem finiteCanonical_bounds {φ : Potential} (hφ : Continuous φ) (hb : IsBoundedPotential φ)
    {L t β c B K : ℝ} (hL : 0 < L) (ht : 0 < t) (hβ : 0 ≤ β) (N : ℕ)
    (hlow : ∀ x ∈ configurationCube L N, c * (N : ℝ)^2 / L^3 - B * N ≤ energy φ x)
    (hmean : (∫ x : Fin N → Position, energy φ x
      ∂Measure.pi (fun _ : Fin N => cubeProbability L)) ≤ K * (N : ℝ)^2 / L^3) :
    β / t * (c * densityAt L N ^ 2 - B * densityAt L N) +
        (densityAt L N * Real.log (densityAt L N) - densityAt L N) / t ≤
      finiteCanonical φ t L N β ∧
    finiteCanonical φ t L N β ≤
      β / t * K * densityAt L N ^ 2 + densityAt L N * Real.log (densityAt L N) / t := by
  have hden : 0 < t * L^3 := mul_pos ht (pow_pos hL 3)
  have hlog := log_factorial_bounds N
  have hl := log_partition_upper_of_energy_lower hφ hb hL hβ N hlow
  rw [Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hu := log_partition_lower_of_energy_mean hφ hb hL hβ N hmean
  by_cases hN : N = 0
  · subst N
    simp [densityAt, finiteCanonical, partition_zero]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hdlog : Real.log (densityAt L N) = Real.log (N : ℝ) - 3 * Real.log L := by
    rw [densityAt, Real.log_div hNr (pow_ne_zero 3 hL.ne'), Real.log_pow]
    norm_num
  constructor
  · rw [finiteCanonical, le_div_iff₀ hden]
    rw [hdlog]
    dsimp only [densityAt]
    have halg : (β / t * (c * ((N : ℝ) / L^3)^2 - B * ((N : ℝ) / L^3)) +
        (((N : ℝ) / L^3) * (Real.log N - 3 * Real.log L) - ((N : ℝ) / L^3)) / t) *
        (t * L^3) = β * (c * (N : ℝ)^2 / L^3 - B * N) +
          (N : ℝ) * Real.log N - (3 * N : ℝ) * Real.log L - N := by field_simp; ring
    rw [halg]
    linarith
  · rw [finiteCanonical, div_le_iff₀ hden]
    rw [hdlog]
    dsimp only [densityAt]
    have halg : (β / t * K * ((N : ℝ) / L^3)^2 +
        ((N : ℝ) / L^3) * (Real.log N - 3 * Real.log L) / t) * (t * L^3) =
        β * (K * (N : ℝ)^2 / L^3) + (N : ℝ) * Real.log N - (3 * N : ℝ) * Real.log L := by
      field_simp
      ring
    rw [halg]
    linarith

end RadialTransition

end

end OAI

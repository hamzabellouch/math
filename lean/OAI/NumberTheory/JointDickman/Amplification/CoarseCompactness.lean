import OAI.NumberTheory.JointDickman.Probability.UniformCoarseChannel

namespace OAI

/-! # Uniform coarse compactness of the manuscript channel -/

namespace JointDickman

open Filter Finset
open scoped Topology

theorem exists_small_coarse_cutoff (A T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 8 ∧ 8 * T * (2 * θ) ^ (1 / 4 : ℝ) * A < ε := by
  let θ : ℕ → ℝ := fun n => (1 / 8) * (1 / ((n : ℝ) + 1))
  have hθ : Tendsto θ atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 8 : ℝ)
  have ht : Tendsto (fun n => 8 * T * (2 * θ n) ^ (1 / 4 : ℝ) * A) atTop (𝓝 0) := by
    have hh := (hθ.const_mul 2).rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 4))
    simpa using (hh.const_mul (8 * T)).mul_const A
  obtain ⟨n, hn⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
  refine ⟨θ n, ?_, ?_, hn⟩
  · dsimp [θ]
    positivity
  · have hinv : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    dsimp [θ]
    linarith

open Classical in
/-- The coarse partition is fixed before B grows and works uniformly for
all real input functions, including inputs depending on B. -/
theorem groupedManuscriptChannel_coarse_compactness
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ᶠ B : ℕ in atTop,
      ∀ f : (auxiliaryPrimes B → Bool) → ℝ,
      (∑ a : Fin m × Fin (channelBlockCount m B), channelMesh (channelFineCount m B) *
        (groupedManuscriptChannel m B f a -
          finiteResidueAverage (fun r => groupedManuscriptChannel m B f (a.1, r))) ^ 2) ≤
        ε * ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 := by
  obtain ⟨A, C, T, _, hC, _, hbound⟩ := groupedManuscriptChannel_coarse_bound hSD hSW hM hMP
  obtain ⟨θ, hθ, hθmax, htail⟩ := exists_small_coarse_cutoff A T (half_pos hε)
  obtain ⟨M, L, hbound⟩ := hbound θ hθ hθmax
  have hmesh : Tendsto (fun m : ℕ => 20 * (M : ℝ) * L * channelMesh m) atTop (𝓝 0) := by
    have hh : Tendsto (fun m : ℕ => (5 / 2 : ℝ) / m) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [channelMesh, mul_zero] using hh.const_mul (20 * (M : ℝ) * L)
  obtain ⟨m, hm, hsmall⟩ := ((eventually_gt_atTop 0).and
    (hmesh.eventually (eventually_lt_nhds (half_pos hε)))).exists
  refine ⟨m, hm, ?_⟩
  have hlim := coarseChannelError_fine_tendsto A T M L θ (channelMesh m) hC.le hm
  have hlimit : 8 * T * (2 * θ) ^ (1 / 4 : ℝ) * A + 20 * (M : ℝ) * L * channelMesh m < ε := by
    linarith
  filter_upwards [hbound m hm, hlim.eventually (eventually_lt_nhds hlimit)] with B hb he
  intro f
  have hin : 0 ≤ ∑ x, fullPrimeMass (auxiliaryPrimes B) x * f x ^ 2 :=
    sum_nonneg (fun x _ => mul_nonneg (fullPrimeMass_nonneg _ (auxiliaryPrimes_prime B) x) (sq_nonneg _))
  exact (hb f).trans (mul_le_mul_of_nonneg_right he.le hin)

end JointDickman

end OAI

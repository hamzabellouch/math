import OAI.Probability.ThorpResults.UniformMoments

namespace OAI

noncomputable section
open scoped BigOperators
open Filter

namespace ThorpNine.Harmonic.Thorp.LowPlanes
open Casimir Specht UnitaryFinite

attribute [local instance] hsNorm hsInner hsFinite

def densityL2Squared (d t : ℕ) : ℝ :=
  (Nat.factorial (2 ^ d) : ℝ) * ∑ g : Equiv.Perm (Card d),
    (law d t g - 1 / (Nat.factorial (2 ^ d) : ℝ)) ^ 2

def densityL2SquaredFrom (d t : ℕ) (σ : Equiv.Perm (Card d)) : ℝ :=
  (Nat.factorial (2 ^ d) : ℝ) * ∑ g : Equiv.Perm (Card d),
    (law d t (g * σ⁻¹) - 1 / (Nat.factorial (2 ^ d) : ℝ)) ^ 2

lemma densityL2SquaredFrom_eq (d t : ℕ) (σ : Equiv.Perm (Card d)) :
    densityL2SquaredFrom d t σ = densityL2Squared d t := by
  unfold densityL2SquaredFrom densityL2Squared
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight σ⁻¹)
    (fun g : Equiv.Perm (Card d) => (law d t g - 1 / (Nat.factorial (2 ^ d) : ℝ)) ^ 2)

lemma densityL2Squared_nonneg (d t : ℕ) : 0 ≤ densityL2Squared d t := by
  unfold densityL2Squared
  positivity

lemma density_fourier_bound (d t : ℕ) :
    densityL2Squared d t ≤ ∑ μ : Shapes (2 ^ d),
      (Module.finrank ℂ (hilbertSpace μ.1) : ℝ) ^ 2 *
        ‖sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d t) -
          uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ)‖ ^ 2 := by
  let V : Shapes (2 ^ d) → Type := fun μ => hilbertSpace μ.1
  let : ∀ μ, NormedAddCommGroup (V μ) := fun _ => inferInstance
  let : ∀ μ, InnerProductSpace ℂ (V μ) := fun _ => inferInstance
  let : ∀ μ, FiniteDimensional ℂ (V μ) := fun _ => inferInstance
  let p := fun g : Equiv.Perm (Card d) => law d t g - 1 / (Nat.factorial (2 ^ d) : ℝ)
  have hb := FiniteFourier.realVector_bound V (cardRepresentation d)
    (cardRepresentation_unitary d) (cardRepresentation_distinct d) (card_conjugacy_shapes d) p
  have he (μ : Shapes (2 ^ d)) : weightedOperator (V := V μ) (cardRepresentation d μ) p =
      sampleOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) (run d t) -
        uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) := by
    rw [sampleOperator_weighted, sampleLaw_run]
    dsimp only [p]
    rw [weighted_sub]
    congr 1
    unfold uniformOperator
    rw [card_permutations]
    simp only [one_div]
  simp_rw [he] at hb
  have hn : ‖FiniteFourier.realVector p‖ ^ 2 = ∑ g, p g ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [FiniteFourier.realVector, PiLp.toLp_apply, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  rw [hn, card_permutations] at hb
  exact hb

lemma density_forward_bound (d v : ℕ) (hv : 0 < v) :
    densityL2Squared d (v * d) ≤ tailBound d v := by
  apply (density_fourier_bound d (v * d)).trans
  apply Finset.sum_le_sum
  intro μ _
  by_cases hz : μ.1.card - μ.1.rowLen 0 = 0
  · simp [hz, card_fourier_full_row d (v * d) μ hz]
  · simp only [hz, ite_false]
    have hu : uniformOperator (V := hilbertSpace μ.1) (cardRepresentation d μ) = 0 :=
      nontrivial_uniform_zero d μ.1 (cardLabels d μ) (by omega)
    rw [hu, sub_zero]
    exact mul_le_mul_of_nonneg_left
      (physical_power_bound d v hv (cardRepresentation d μ) (cardRepresentation_unitary d μ))
      (sq_nonneg _)

theorem fixed_sweep_density_decay :
    ∃ v : ℕ, 1 ≤ v ∧ ∀ d : ℕ, 1 ≤ d →
      ∀ σ : Equiv.Perm (Card d),
        densityL2SquaredFrom d (v * d) σ ≤ ((2 : ℝ) ^ d) ^ (-10 : ℤ) := by
  obtain ⟨v, hv, h⟩ := uniform_tail_bound
  refine ⟨v, hv, ?_⟩
  intro d hd σ
  rw [densityL2SquaredFrom_eq]
  exact (density_forward_bound d v (by omega)).trans (h d hd v le_rfl)

theorem fixed_sweep_density_convergence :
    ∃ v : ℕ, 1 ≤ v ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
      ∀ σ : Equiv.Perm (Card d), densityL2SquaredFrom d (v * d) σ < ε := by
  obtain ⟨v, hv, h⟩ := fixed_sweep_density_decay
  refine ⟨v, hv, ?_⟩
  intro ε hε
  have ht : Tendsto (fun d : ℕ => ((2 : ℝ) ^ d) ^ (-10 : ℤ)) atTop (nhds 0) := by
    have he (d : ℕ) : ((2 : ℝ) ^ d) ^ (-10 : ℤ) = ((2 : ℝ) ^ (-10 : ℤ)) ^ d := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    simp_rw [he]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [ht.eventually (eventually_lt_nhds hε), eventually_ge_atTop 1] with d hd hd1 σ
  exact (h d hd1 σ).trans_lt hd

theorem fixed_sweep_mixing :
    ∃ v : ℕ, 1 ≤ v ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ d : ℕ in atTop,
      ∀ σ : Equiv.Perm (Card d), sweepDistance d v σ < ε := by
  obtain ⟨v, hv, h⟩ := uniform_tail_bound
  refine ⟨v, hv, ?_⟩
  intro ε hε
  have ht : Tendsto (fun d : ℕ => (1 / 2 : ℝ) * ((2 : ℝ) ^ d) ^ (-5 : ℤ))
      atTop (nhds 0) := by
    have he (d : ℕ) : ((2 : ℝ) ^ d) ^ (-5 : ℤ) = ((2 : ℝ) ^ (-5 : ℤ)) ^ d := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    simp_rw [he]
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 2 ^ (-5 : ℤ))
      (by norm_num : (2 : ℝ) ^ (-5 : ℤ) < 1)).const_mul (1 / 2 : ℝ)
  filter_upwards [ht.eventually (eventually_lt_nhds hε), eventually_ge_atTop 1] with d hd hd1 σ
  have hb := distance_of_tail_bound d v (by omega) (h d hd1 v le_rfl)
  change fromDistance d (v * d) σ < ε
  rw [fromDistance_eq]
  exact hb.trans_lt hd

end ThorpNine.Harmonic.Thorp.LowPlanes

end

end OAI

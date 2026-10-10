import OAI.NumberTheory.JointDickman.Counting.CoefficientDyadicBoxes

namespace OAI

/-! # Removing coefficient regularity in the normalized amplification mass -/

namespace JointDickman

open Filter Finset
open scoped Topology

/-- The actual coefficient-support probability of a failed regularity
cutoff, including the outside B normalization in manuscript (13). -/
theorem coefficient_cutoff_removal
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ ε : ℕ → ℝ, (∀ B, 0 ≤ ε B) ∧ Tendsto ε atTop (𝓝 0) ∧
        ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), 0 ≤ C → 0 < T →
          (T : ℝ) ≤ Real.exp ((1 / 10 : ℝ) * B) →
          (B : ℝ) * (∑ ac ∈ amplificationCoefficientPairs B T,
            coefficientPairFailureMass B L τ C ac.1 ac.2) ≤
            K * (ε B + Real.exp (-(1 / 10 : ℝ) * C)) := by
  classical
  obtain ⟨K, hK, hboxes⟩ := coefficient_failure_box_bound hFord hM
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 32)
  refine ⟨4 * K, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨ε, hε0, hε, hlarge⟩ := hboxes L τ hL hτ
  refine ⟨ε, hε0, hε, ?_⟩
  filter_upwards [hlarge, coefficientDyadicBox_scales, eventually_gt_atTop 0] with B hb hs hB
  intro C T hC hT hTsize
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  let F := ε B + Real.exp (-(1 / 10 : ℝ) * C)
  have hF : 0 ≤ F := add_nonneg (hε0 B) (Real.exp_pos _).le
  have hpoint : ∀ k ∈ Ico B (4 * B),
      (∑ ac ∈ coefficientDyadicBox T k, coefficientPairFailureMass B L τ C ac.1 ac.2) ≤
        K / (B : ℝ)^2 * F := by
    intro k hk
    have hscale := hs T k hTsize hk
    unfold coefficientDyadicBox
    rw [sum_product]
    exact hb C T (2^k) hC hT hscale.1 hscale.2
  have hsum : (∑ ac ∈ amplificationCoefficientPairs B T,
      coefficientPairFailureMass B L τ C ac.1 ac.2) ≤
      ((Ico B (4 * B)).card : ℝ) * (K / (B : ℝ)^2 * F) := by
    calc
      _ ≤ ∑ ac ∈ coefficientDyadicCover B T, coefficientPairFailureMass B L τ C ac.1 ac.2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun ac _ _ => coefficientPairFailureMass_nonneg B L τ C ac.1 ac.2)
      _ = ∑ k ∈ Ico B (4 * B), ∑ ac ∈ coefficientDyadicBox T k,
          coefficientPairFailureMass B L τ C ac.1 ac.2 := by
        apply sum_biUnion
        intro k _ l _ hkl
        exact coefficientDyadicBox_disjoint T hkl
      _ ≤ ∑ _k ∈ Ico B (4 * B), K / (B : ℝ)^2 * F := sum_le_sum hpoint
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have hcard : ((Ico B (4 * B)).card : ℝ) ≤ 4 * B := by
    exact_mod_cast (show (Ico B (4 * B)).card ≤ 4 * B by rw [Nat.card_Ico]; omega)
  calc
    _ ≤ (B : ℝ) * (((Ico B (4 * B)).card : ℝ) * (K / (B : ℝ)^2 * F)) :=
      mul_le_mul_of_nonneg_left hsum hB0.le
    _ ≤ (B : ℝ) * ((4 * B) * (K / (B : ℝ)^2 * F)) := by
      gcongr
    _ = _ := by
      dsimp only [F]
      field_simp

end JointDickman

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateMesh
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DeterminantLowerNorm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.DerivativeOscillation

namespace OAI

/-! # Quantitative injective patches near nondegenerate derivatives -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

theorem exists_quantitative_injective_cover (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (Fin n → ℝ) → (Fin n → ℝ))
        (df : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
        (R L η : ℝ), 0 ≤ R → 1 ≤ L → 0 < η →
      (∀ z, ‖z‖ ≤ R + 2 → HasFDerivAt f (df z) z) →
      (∀ z, ‖z‖ ≤ R + 2 → ‖df z‖ ≤ L) →
      (∀ z w, ‖z‖ ≤ R + 2 → ‖w‖ ≤ R + 2 →
        ‖df z - df w‖ ≤ L * dist z w) →
      ∃ (ρ : ℝ) (k : ℕ) (c : (Fin n → Fin k) → (Fin n → ℝ)),
        ρ = min 1 (η / (8 * (C * L ^ (n - 1)) * L)) ∧ 0 < ρ ∧
        (k : ℝ) ≤ 2 * R / ρ + 2 ∧
        (∀ z, ‖z‖ ≤ R → ∃ i, z ∈ closedBall (c i) ρ) ∧
        ∀ i, Set.InjOn f
          ({z | ‖z‖ ≤ R ∧ η ≤ |(df z).det|} ∩ closedBall (c i) ρ) := by
  obtain ⟨C, hC, hbound⟩ := exists_determinant_lower_norm_bound n
  refine ⟨C, hC, ?_⟩
  intro f df R L η hR hL hη hf hdf hosc
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let D := C * L ^ (n - 1)
  have hD : 0 < D := mul_pos hC (pow_pos hLpos _)
  let ρ := min 1 (η / (8 * D * L))
  have hρ : 0 < ρ := lt_min zero_lt_one (div_pos hη (by positivity))
  have hρone : ρ ≤ 1 := min_le_left _ _
  have hgap : D * (2 * L * ρ) < η := by
    have hρle : ρ ≤ η / (8 * D * L) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0 < 8 * D * L by positivity)).mp hρle
    nlinarith
  obtain ⟨k, hk, c, hc, hcover⟩ := exists_coordinate_mesh n hR hρ
  refine ⟨ρ, k, c, rfl, hρ, hk, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hi⟩ := hcover z hz
    exact ⟨i, hi⟩
  · intro i
    by_cases hempty : ({z | ‖z‖ ≤ R ∧ η ≤ |(df z).det|} ∩ closedBall (c i) ρ).Nonempty
    · obtain ⟨z₀, hz₀, hz₀ball⟩ := hempty
      have hbig (z : Fin n → ℝ) (hz : z ∈ closedBall (c i) ρ) : ‖z‖ ≤ R + 2 := by
        have he : ‖z‖ ≤ ‖z - c i‖ + ‖c i‖ := by
          simpa only [dist_eq_norm, sub_zero] using dist_triangle z (c i) 0
        have hd : ‖z - c i‖ ≤ ρ := hz
        have hh := hc i
        linarith
      have hi : Set.InjOn f (closedBall (c i) ρ) := by
        apply injOn_of_derivative_oscillation f df (df z₀) (convex_closedBall _ _)
          (fun z hz => hf z (hbig z hz)) hD.le hgap
        · exact hbound (df z₀) L η hLpos (hdf z₀ (hbig z₀ hz₀ball)) hz₀.2
        · intro z hz
          have hd : dist z z₀ ≤ 2 * ρ := by
            calc
              dist z z₀ ≤ dist z (c i) + dist (c i) z₀ := dist_triangle _ _ _
              _ ≤ ρ + ρ := add_le_add hz
                (by simpa only [dist_comm] using (mem_closedBall.mp hz₀ball))
              _ = 2 * ρ := by ring
          exact (hosc z z₀ (hbig z hz) (hbig z₀ hz₀ball)).trans
            (by nlinarith [mul_le_mul_of_nonneg_left hd hLpos.le])
      exact hi.mono inter_subset_right
    · simpa only [not_nonempty_iff_eq_empty.mp hempty] using (Set.injOn_empty f)

end PolycyclicRecognition

end

end OAI

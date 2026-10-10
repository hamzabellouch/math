import OAI.Analysis.IrrationalRotation.Model.PhaseBlocks
import OAI.Analysis.IrrationalRotation.Product.IndependentRotation
import OAI.Analysis.IrrationalRotation.Analysis.TaggedThresholdCrossing

namespace OAI

noncomputable section

namespace Invariant233.ProductPhases

theorem strict_scale_bounds_of_independent {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (i : ι) (m K : ℕ)
    (hi : θ i ∈ Set.Icc (1 / ((m : ℝ) * K)) (2 / ((m : ℝ) * K))) :
    θ i ∈ Set.Ioo (1 / ((m : ℝ) * K)) (2 / ((m : ℝ) * K)) := by
  have hir := IndependentRotation.irrational_coordinate hθ i
  have hne₁ : θ i ≠ 1 / ((m : ℝ) * K) := by
    simpa only [Int.cast_one, Int.cast_natCast, Nat.cast_mul, Int.cast_mul] using
      hir.ne_rational 1 ((m * K : ℕ) : ℤ)
  have hne₂ : θ i ≠ 2 / ((m : ℝ) * K) := by
    simpa only [Int.cast_ofNat, Int.cast_natCast, Nat.cast_mul, Int.cast_mul] using
      hir.ne_rational 2 ((m * K : ℕ) : ℤ)
  exact ⟨lt_of_le_of_ne hi.1 hne₁.symm, lt_of_le_of_ne hi.2 hne₂⟩

theorem strict_consecutive_bounds_of_independent
    (m K : ℕ → ℕ) {θ : ℕ → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ℕ => o.elim 1 θ))
    (hb : ∀ j, ∀ i ∈ consecutiveBlock m j,
      θ i ∈ Set.Icc (1 / ((m j : ℝ) * K j)) (2 / ((m j : ℝ) * K j))) :
    ∀ j, ∀ i ∈ consecutiveBlock m j,
      θ i ∈ Set.Ioo (1 / ((m j : ℝ) * K j)) (2 / ((m j : ℝ) * K j)) := by
  intro j i hi
  exact strict_scale_bounds_of_independent hθ i (m j) (K j) (hb j i hi)

end Invariant233.ProductPhases

namespace Invariant233.FloorCocycle

theorem tagged_crossing_of_source_window {m K α x y : ℝ} (k : ℤ)
    (hm : 4 ≤ m) (hK : 0 < K)
    (hαlo : 1 / (m * K) ≤ α) (hαhi : α ≤ 2 / (m * K))
    (hklo : K < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ m * K / 4)
    (hx : x < 1 / m) (hy : 1 - 1 / m ≤ y) :
    x < 1 - Int.fract ((k : ℝ) * α) ∧
      1 - Int.fract ((k : ℝ) * α) ≤ y := by
  have hm0 : 0 < m := by linarith
  have hmK : 0 < m * K := mul_pos hm0 hK
  have hα0 : 0 < α := (one_div_pos.mpr hmK).trans_le hαlo
  have hk0 : 0 < |(k : ℝ)| := hK.trans hklo
  have hlo : 1 / m < |(k : ℝ)| * α := by
    calc
      1 / m = K * (1 / (m * K)) := by field_simp
      _ < |(k : ℝ)| * (1 / (m * K)) :=
        mul_lt_mul_of_pos_right hklo (one_div_pos.mpr hmK)
      _ ≤ |(k : ℝ)| * α := mul_le_mul_of_nonneg_left hαlo hk0.le
  have hhalf : |(k : ℝ)| * α ≤ 1 / 2 := by
    calc
      |(k : ℝ)| * α ≤ |(k : ℝ)| * (2 / (m * K)) :=
        mul_le_mul_of_nonneg_left hαhi hk0.le
      _ ≤ (m * K / 4) * (2 / (m * K)) :=
        mul_le_mul_of_nonneg_right hkhi (div_nonneg (by norm_num) hmK.le)
      _ = 1 / 2 := by field_simp; ring
  have hinv : 1 / m ≤ (1 / 4 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hm
  have hthreshold := threshold_mem_Ioo_of_abs_phase
    (one_div_pos.mpr hm0).le
    (show 1 / m < |(k : ℝ) * α| by
      simpa only [abs_mul, abs_of_pos hα0] using hlo)
    (show |(k : ℝ) * α| < 1 - 1 / m by
      rw [abs_mul, abs_of_pos hα0]
      linarith)
  exact ⟨hx.trans hthreshold.1, hthreshold.2.le.trans hy⟩

end Invariant233.FloorCocycle

end

end OAI

import OAI.MeasureTheory.Falconer.Radial.UniformVanishingSlabs

namespace OAI

/-! # Uniform vanishing over all affine hyperplanes for a bounded measure -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem uniform_affine_slabs {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ] {M : ℝ} (hM : 0 ≤ M)
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M)
    (hzero : ∀ w : Space d, ‖w‖ = 1 → ∀ a : ℝ, μ {x | inner ℝ w x = a} = 0)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ w : Space d, ‖w‖ = 1 → ∀ a : ℝ,
      μ {x | |inner ℝ w x-a| ≤ r} < η := by
  obtain ⟨ρ,hρ,hsmall⟩ := uniform_bounded_affine_slabs (B := M+1) μ hM hbounded hzero hη
  refine ⟨min ρ 1,lt_min hρ zero_lt_one,min_le_right _ _,?_⟩
  intro w hw a
  by_cases ha : |a| ≤ M+1
  · apply (measure_mono (show {x | |inner ℝ w x-a| ≤ min ρ 1} ⊆
        {x | |inner ℝ w x-a| ≤ ρ} from by
          intro x hx
          exact le_trans (show |inner ℝ w x-a| ≤ min ρ 1 from hx) (min_le_left _ _))).trans_lt
    exact hsmall w hw a (abs_le.mp ha)
  · have hm : μ {x | |inner ℝ w x-a| ≤ min ρ 1} ≤ μ (∅ : Set (Space d)) := by
      apply measure_mono_ae
      filter_upwards [hbounded] with x hx
      intro hxa
      have hi : |inner ℝ w x| ≤ M := by
        have hh := abs_real_inner_le_norm w x
        rw [hw,one_mul] at hh
        exact hh.trans hx
      have habs : |a| ≤ |inner ℝ w x|+|inner ℝ w x-a| := by
        calc
          _ = |inner ℝ w x-(inner ℝ w x-a)| := by congr 1; ring
          _ ≤ _ := abs_sub _ _
      have hr : min ρ 1 ≤ 1 := min_le_right _ _
      exact (ha (by linarith only [hi,habs,hxa,hr])).elim
    exact hm.trans_lt (by simpa only [measure_empty] using hη)

end Falconer

end OAI

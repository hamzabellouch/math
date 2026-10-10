import OAI.MeasureTheory.Falconer.Recursion.ProfileRoundContact

namespace OAI

/-! # Fixed positive margins at the rounded contact depths -/

namespace Falconer
open Filter
open scoped Topology

theorem contact_depth_margins {A B : ℝ} (hA : 0 < A) (hAB : A < B)
    (hB : B < 1) (hBA : B < 2*A) :
    ∃ β γ : ℝ, 0 < β ∧ 0 < γ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let a := Nat.floor (A*(N:ℝ))
      let b := Nat.floor (B*(N:ℝ))
      a ≤ b ∧ b ≤ N ∧ β*(N:ℝ) ≤ (b-a:ℕ) ∧ γ*(N:ℝ) ≤ 2*(a:ℝ)-(b:ℝ) := by
  let β := (B-A)/2
  let γ := (2*A-B)/2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hAlim := floor_depth_ratio_tendsto hA.le
  have hBlim := floor_depth_ratio_tendsto (hA.trans hAB).le
  have hgap := (hBlim.sub hAlim).eventually (eventually_gt_nhds (show β < B-A by dsimp [β]; linarith))
  have hlinear := ((tendsto_const_nhds.mul hAlim).sub hBlim).eventually
    (eventually_gt_nhds (show γ < 2*A-B by dsimp [γ]; linarith))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (hgap.and (hlinear.and (eventually_ge_atTop 1)))
  refine ⟨β,γ,hβ,hγ,N₀,?_⟩
  intro N hN
  obtain ⟨hgap,hlinear,hNpos⟩ := hN₀ N hN
  have hNp : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  let a := Nat.floor (A*(N:ℝ))
  let b := Nat.floor (B*(N:ℝ))
  have hab : a ≤ b := Nat.floor_mono (mul_le_mul_of_nonneg_right hAB.le hNp.le)
  have hbN : b ≤ N := by
    apply Nat.floor_le_of_le
    exact (mul_le_mul_of_nonneg_right hB.le hNp.le).trans_eq (one_mul _)
  refine ⟨hab,hbN,?_,?_⟩
  · rw [Nat.cast_sub hab]
    apply (le_div_iff₀ hNp).mp
    simpa only [sub_div] using hgap.le
  · apply (le_div_iff₀ hNp).mp
    simpa only [sub_div,mul_div_assoc] using hlinear.le

end Falconer

end OAI

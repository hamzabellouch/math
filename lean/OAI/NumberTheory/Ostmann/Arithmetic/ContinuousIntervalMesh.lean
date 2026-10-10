import Mathlib.Topology.UniformSpace.HeineCantor
import OAI.NumberTheory.Ostmann.Arithmetic.PrimePartitionVariation

namespace OAI

/-! # Finite meshes for the continuous factors in prime comparison -/

namespace Ostmann

/-- Mesh fineness is arbitrary and has no arithmetic cost: the progression
comparison uses total variation instead of counting the subintervals. -/
theorem continuous_interval_mesh (u v : ℝ) (huv : u ≤ v) (w : ℝ → ℂ)
    (hw : ContinuousOn w (Set.Icc u v)) (η : ℝ) (hη : 0 < η) :
    ∃ (s : ℕ → ℝ) (N : ℕ), 0 < N ∧ Monotone s ∧ s 0 = u ∧ s N = v ∧
      ∀ j < N, ∀ y ∈ Set.Ioc (s j) (s (j + 1)), ‖w y - w (s j)‖ ≤ η := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hw) η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((v - u) / δ)
  let N := n + 1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hmesh : (v - u) / N < δ := by
    apply (div_lt_iff₀ hN).mpr
    have hh : (v - u) / δ < (N : ℝ) := hn.trans (by dsimp [N]; push_cast; linarith)
    have := (div_lt_iff₀ hδ).mp hh
    nlinarith
  let s : ℕ → ℝ := fun j => u + (v - u) * j / N
  have hs : Monotone s := by
    intro i j hij
    dsimp [s]
    apply add_le_add le_rfl
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by exact_mod_cast hij)
      (sub_nonneg.mpr huv)) hN.le
  have hs0 : s 0 = u := by simp [s]
  have hsN : s N = v := by dsimp [s]; field_simp; ring
  refine ⟨s, N, by dsimp [N]; omega, hs, hs0, hsN, ?_⟩
  intro j hj y hy
  have hsju : u ≤ s j := by rw [← hs0]; exact hs (Nat.zero_le _)
  have hsjv : s (j + 1) ≤ v := by rw [← hsN]; exact hs (by omega)
  have hsj : s j ∈ Set.Icc u v := ⟨hsju, (hs (Nat.le_succ _)).trans hsjv⟩
  have hyuv : y ∈ Set.Icc u v := ⟨hsju.trans hy.1.le, hy.2.trans hsjv⟩
  have hwidth : s (j + 1) - s j = (v - u) / N := by dsimp [s]; push_cast; ring
  have hdist : dist y (s j) < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1.le)]
    calc
      y - s j ≤ s (j + 1) - s j := sub_le_sub_right hy.2 _
      _ < δ := hwidth ▸ hmesh
  simpa only [dist_eq_norm] using (hmod y hyuv (s j) hsj hdist).le

end Ostmann

end OAI

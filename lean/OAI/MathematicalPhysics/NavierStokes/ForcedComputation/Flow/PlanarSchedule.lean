import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarSegments
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarActionOrder

namespace OAI

/-! The finite pulse slots occupy successive closed cells. The unused half
of each cell and the final cell are stationary. -/

noncomputable section

namespace ForcedComputation.PlanarTiming

open ShearFlows Set

def cut (n i : ℕ) : ℝ := (i : ℝ) / (n + 1)

@[simp] theorem cut_zero (n : ℕ) : cut n 0 = 0 := by simp [cut]

@[simp] theorem cut_last (n : ℕ) : cut n (n + 1) = 1 := by
  have h : (n : ℝ) + 1 ≠ 0 := by positivity
  simp [cut, Nat.cast_add, Nat.cast_one, h]

theorem cut_mono (n : ℕ) {i j : ℕ} (h : i ≤ j) : cut n i ≤ cut n j :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem finish_eq_cut {n : ℕ} (i : Fin n) : (finish i : ℝ) = cut n (i.val + 1) := by
  simp only [finish, cut, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_one, Nat.cast_add, Nat.cast_one]
  field_simp

theorem cut_le_start {n : ℕ} (i : Fin n) : cut n i.val ≤ (start i : ℝ) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [cut, start, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_one]
  apply (div_le_div_iff₀ hn (by positivity)).mpr
  nlinarith

theorem pulse_other_on_cell {n : ℕ} {i j : Fin n} (hne : i ≠ j) {t : ℝ}
    (ht : t ∈ Icc (cut n i.val) (cut n (i.val + 1))) : pulse j t = 0 := by
  have ho : (start j : ℝ) < finish j := by exact_mod_cast (intervals j).2.1
  rcases lt_or_gt_of_ne hne with h | h
  · apply smoothPulse_before ho
    have hh : (finish i : ℝ) < start j := by exact_mod_cast ordered h
    rw [finish_eq_cut] at hh
    exact ht.2.trans hh.le
  · apply smoothPulse_after ho
    rw [finish_eq_cut]
    exact (cut_mono n (show j.val + 1 ≤ i.val from h)).trans ht.1

theorem pulse_on_tail {n : ℕ} (i : Fin n) {t : ℝ} (ht : cut n n ≤ t) : pulse i t = 0 := by
  apply smoothPulse_after (by exact_mod_cast (intervals i).2.1)
  rw [finish_eq_cut]
  exact (cut_mono n i.isLt).trans ht

end ForcedComputation.PlanarTiming

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarHamiltonian PlanarTiming Set

theorem compiledVelocity_on_cell (M : Alternating.Machine) (hM : M.WellFormed)
    (i : Fin (actions M hM).length) {t : ℝ}
    (ht : t ∈ Icc (cut (actions M hM).length i.val) (cut (actions M hM).length (i.val + 1)))
    (x : Plane) :
    processorVelocity (compiledPulse M hM) t x = (compiledPulse M hM i).velocity t x := by
  rw [processorVelocity_eq_sum]
  apply Finset.sum_eq_single i
  · intro j _ hji
    change pulse j t • (compiledPulse M hM j).spatial x = 0
    rw [pulse_other_on_cell hji.symm ht, zero_smul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem compiledVelocity_on_tail (M : Alternating.Machine) (hM : M.WellFormed) {t : ℝ}
    (ht : cut (actions M hM).length (actions M hM).length ≤ t) (x : Plane) :
    processorVelocity (compiledPulse M hM) t x = 0 := by
  rw [processorVelocity_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  change pulse i t • (compiledPulse M hM i).spatial x = 0
  rw [pulse_on_tail i ht, zero_smul]

end ForcedComputation.Recorder.Planar

end

end OAI

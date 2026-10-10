import OAI.Analysis.PeriodicLattice.Profiles

namespace OAI

/-! Uniqueness of trajectories and smooth flow estimates. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingTrajectories {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace Trajectories

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem unique {v : ℝ → E → E} (hv : ContDiff ℝ 1 (fun tx : ℝ × E => v tx.1 tx.2))
    {X Y : ℝ → E} (hX : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt X (v t (X t)) (Ici 0) t)
    (hY : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt Y (v t (Y t)) (Ici 0) t)
    (h₀ : X 0 = Y 0) {T : ℝ} (hT : 0 ≤ T) : X T = Y T := by
  have hcX : ContinuousOn X (Icc 0 T) := fun t ht =>
    ((hX t ht.1).mono Icc_subset_Ici_self).continuousWithinAt
  have hcY : ContinuousOn Y (Icc 0 T) := fun t ht =>
    ((hY t ht.1).mono Icc_subset_Ici_self).continuousWithinAt
  obtain ⟨R₁, hR₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcX
  obtain ⟨R₂, hR₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcY
  let R := max R₁ R₂
  have hBX : ∀ t ∈ Icc 0 T, X t ∈ Metric.closedBall (0 : E) R := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hR₁ t ht).trans (le_max_left _ _)
  have hBY : ∀ t ∈ Icc 0 T, Y t ∈ Metric.closedBall (0 : E) R := by
    intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hR₂ t ht).trans (le_max_right _ _)
  let S : Set (ℝ × E) := Icc 0 T ×ˢ Metric.closedBall 0 R
  have hcS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨B, hB⟩ := hcS.exists_bound_of_continuousOn
    (hv.continuous_fderiv (by norm_num)).continuousOn
  have hlip : LipschitzOnWith B.toNNReal (fun tx : ℝ × E => v tx.1 tx.2) S := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · intro tx htx
      exact (hv.differentiable (by norm_num)).differentiableAt
    · intro tx htx
      simpa only [norm_toNNReal] using Real.toNNReal_le_toNNReal (hB tx htx)
    · exact (convex_Icc (0 : ℝ) T).prod (convex_closedBall (0 : E) R)
  have hlip' : ∀ t ∈ Ico 0 T, LipschitzOnWith B.toNNReal (v t) (Metric.closedBall 0 R) := by
    intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa using hlip.dist_le_mul (t, x) ⟨⟨ht.1, ht.2.le⟩, hx⟩
      (t, y) ⟨⟨ht.1, ht.2.le⟩, hy⟩
  have heq := ODE_solution_unique_of_mem_Icc_right hlip' hcX
    (fun t ht => (hX t ht.1).mono (Ici_subset_Ici.mpr ht.1))
    (fun t ht => hBX t ⟨ht.1, ht.2.le⟩) hcY
    (fun t ht => (hY t ht.1).mono (Ici_subset_Ici.mpr ht.1))
    (fun t ht => hBY t ⟨ht.1, ht.2.le⟩) h₀
  exact heq ⟨hT, le_rfl⟩

end Trajectories

namespace Profiles

open Filter Set
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def accumulated (W : ℕ → E) (t : ℝ) : E := ∑ᶠ n : ℕ, shiftedClock n t • W n

theorem accumulated_contDiff (W : ℕ → E) : ContDiff ℝ ∞ (accumulated W) := by
  apply contMDiff_iff_contDiff.mp
  apply contMDiff_finsum
  · intro n
    exact contMDiff_iff_contDiff.mpr ((shiftedClock_contDiff n).smul contDiff_const)
  · apply shiftedClock_locallyFinite.subset
    intro n t ht hz
    exact ht (by simp [hz])

theorem accumulated_in_collar (W : ℕ → E) (n : ℕ) {t : ℝ}
    (ht : (n : ℝ) - 1 / 3 < t) (ht' : t < n + 4 / 3) :
    accumulated W t = (∑ m ∈ Finset.range n, W m) + shiftedClock n t • W n := by
  have hs : Function.support (fun m : ℕ => shiftedClock m t • W m) ⊆
      (Finset.range (n + 1) : Set ℕ) := by
    intro m hm
    by_contra h
    have hm' : n + 1 ≤ m := by simpa only [Finset.mem_coe, Finset.mem_range, not_lt] using h
    have hm'' : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hm'
    have hz : shiftedClock m t = 0 := clock_zero (by linarith)
    exact hm (by simp only [hz, zero_smul])
  rw [accumulated, finsum_eq_sum_of_support_subset _ hs, Finset.sum_range_succ]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hm' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Finset.mem_range.mp hm
  rw [show shiftedClock m t = 1 from clock_one (by linarith), one_smul]

theorem accumulated_eventually (W : ℕ → E) (n : ℕ) {t : ℝ}
    (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1) :
    accumulated W =ᶠ[𝓝 t]
      (fun s => (∑ m ∈ Finset.range n, W m) + shiftedClock n s • W n) := by
  filter_upwards [Ioo_mem_nhds (show (n : ℝ) - 1 / 3 < t by linarith)
    (show t < n + 4 / 3 by linarith)] with s hs
  exact accumulated_in_collar W n hs.1 hs.2

theorem accumulated_on_slot (W : ℕ → E) (n : ℕ) {t : ℝ}
    (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1) :
    accumulated W t = (∑ m ∈ Finset.range n, W m) + shiftedClock n t • W n :=
  (accumulated_eventually W n ht ht').eq_of_nhds

theorem accumulated_at_integer (W : ℕ → E) (n : ℕ) :
    accumulated W n = ∑ m ∈ Finset.range n, W m := by
  rw [accumulated_on_slot W n le_rfl (by linarith)]
  have hz : shiftedClock n n = 0 := clock_zero (by norm_num)
  rw [hz, zero_smul, add_zero]

theorem accumulated_hasDerivAt (W : ℕ → E) (n : ℕ) {t : ℝ}
    (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1) :
    HasDerivAt (accumulated W) (pulse n t • W n) t := by
  apply (accumulated_eventually W n ht ht').hasDerivAt_iff.mpr
  exact ((shiftedClock_hasDerivAt n t).smul_const (W n)).const_add _

end Profiles

end
end PeriodicLattice

end OAI

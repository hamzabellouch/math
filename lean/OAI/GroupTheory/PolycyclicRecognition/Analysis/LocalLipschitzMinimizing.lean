import OAI.GroupTheory.PolycyclicRecognition.Analysis.MinimizingMetricChains

namespace OAI

/-! # From a fixed-radius Lipschitz bound to the global bound -/

namespace PolycyclicRecognition

open Set
open scoped NNReal

theorem lipschitzWith_of_unit_local_bound
    {G Y : Type*} [Group G] [MetricSpace G] [IsIsometricSMul G G] [MetricSpace Y]
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ≥0} (f : G → Y)
    (hf : ∀ x y, dist x y ≤ 1 → dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith K f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  obtain ⟨γ, h0, h1, hγ⟩ := hpath (x⁻¹ * y)
  let D := dist 1 (x⁻¹ * y)
  let n := ⌊D⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hDn : D ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one D).le
  let p : ℕ → G := fun k => x * γ ((k : ℝ) / n)
  have hp0 : p 0 = x := by simp [p, h0]
  have hpn : p n = y := by simp [p, h1, hnr.ne']
  have hp (k : ℕ) (hk : k < n) : dist (p k) (p (k + 1)) ≤ D / (n : ℝ) := by
    have ht : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr (by exact_mod_cast hk.le)⟩
    have hu : ((k + 1 : ℕ) : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity, (div_le_one hnr).mpr (by exact_mod_cast hk)⟩
    have hd : |(k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n| = 1 / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr (div_le_div_of_nonneg_right (by simp) hnr.le))]
      push_cast
      ring
    change dist (x * γ _) (x * γ _) ≤ _
    rw [dist_mul_left]
    simpa only [hd, mul_one_div] using hγ _ ht _ hu
  have hstep (k : ℕ) (hk : k < n) : dist (f (p k)) (f (p (k + 1))) ≤ K * (D / (n : ℝ)) :=
    (hf _ _ ((hp k hk).trans ((div_le_one hnr).mpr hDn))).trans
      (mul_le_mul_of_nonneg_left (hp k hk) K.2)
  calc
    dist (f x) (f y) = dist (f (p 0)) (f (p n)) := by rw [hp0, hpn]
    _ ≤ ∑ k ∈ Finset.range n, K * (D / (n : ℝ)) :=
      dist_le_range_sum_of_dist_le (f := fun k => f (p k)) n (fun {k} hk => hstep k hk)
    _ = K * D := by simp; field_simp
    _ = K * dist x y := by rw [show D = dist x y from dist_one_groupDifference x y]

end PolycyclicRecognition

end OAI

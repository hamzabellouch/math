import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelRootCount

namespace OAI

namespace Ostmann.QuadraticCenter

theorem kernel_population_real_bound_of_range
    (S : Finset ℤ) {m : ℕ} (hm : 0 < m) {u h : ℤ}
    (hc : IsCoprime h (m : ℤ)) (hu : u ≠ 0)
    (t : ℤ → ℕ) (lo hi : ℕ) {X : ℝ} (hX : 0 ≤ X)
    (heq : ∀ x ∈ S, (m : ℤ) * x - h = u * (t x : ℤ) ^ 2)
    (hrange : ∀ x ∈ S, lo ≤ t x ∧ t x ≤ hi)
    (hdiam : ((hi - lo : ℕ) : ℝ) ≤ Real.sqrt ((m : ℝ) * X / |(u : ℝ)|)) :
    (S.card : ℝ) ≤ 4 * Real.sqrt (X / |(u : ℝ)|) + 8 * Real.sqrt (m : ℝ) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hur : (u : ℝ) ≠ 0 := by exact_mod_cast hu
  have hcnt : (S.card : ℝ) ≤ ((kernelRootResidues m u h).card : ℝ) *
      (((hi - lo) / m : ℕ) + 2 : ℝ) := by
    exact_mod_cast kernel_population_le_diameter S hm t lo hi heq hrange
  have hsqrt : (Nat.sqrt m : ℝ) ≤ Real.sqrt (m : ℝ) := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) hmr.le).mpr
    rw [pow_two]
    exact_mod_cast Nat.sqrt_le m
  have hroots : ((kernelRootResidues m u h).card : ℝ) ≤ 4 * Real.sqrt (m : ℝ) := by
    have hn : ((kernelRootResidues m u h).card : ℝ) ≤ 4 * (Nat.sqrt m : ℝ) := by
      exact_mod_cast kernelRootResidues_card_le_four_sqrt hm hc
    nlinarith
  have hdiv : (((hi - lo) / m : ℕ) : ℝ) ≤
      Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) / m :=
    (Nat.cast_div_le (α := ℝ)).trans (div_le_div_of_nonneg_right hdiam hmr.le)
  calc
    (S.card : ℝ) ≤ ((kernelRootResidues m u h).card : ℝ) *
        (((hi - lo) / m : ℕ) + 2 : ℝ) := hcnt
    _ ≤ (4 * Real.sqrt (m : ℝ)) *
        (Real.sqrt ((m : ℝ) * X / |(u : ℝ)|) / m + 2) := by
      apply mul_le_mul hroots (by linarith) (by positivity) (by positivity)
    _ = 4 * Real.sqrt (X / |(u : ℝ)|) + 8 * Real.sqrt (m : ℝ) := by
      rw [mul_div_assoc, Real.sqrt_mul' _ (div_nonneg hX (abs_nonneg _))]
      have hs := Real.sq_sqrt hmr.le
      field_simp
      have hs' := congrArg (fun z : ℝ => z * Real.sqrt (X / |(u : ℝ)|)) hs
      nlinarith [hs']

theorem kernel_population_real_bound
    (S : Finset ℤ) {m : ℕ} (hm : 0 < m) {u h : ℤ}
    (hc : IsCoprime h (m : ℤ)) (hu : u ≠ 0)
    (t : ℤ → ℕ) {X : ℝ} (hX : 0 ≤ X)
    (heq : ∀ x ∈ S, (m : ℤ) * x - h = u * (t x : ℤ) ^ 2)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |(x : ℝ) - (y : ℝ)| ≤ X) :
    (S.card : ℝ) ≤ 4 * Real.sqrt (X / |(u : ℝ)|) + 8 * Real.sqrt (m : ℝ) := by
  classical
  by_cases hne : S.Nonempty
  · let T := S.image t
    have hT : T.Nonempty := hne.image t
    let lo := T.min' hT
    let hi := T.max' hT
    have hrange : ∀ x ∈ S, lo ≤ t x ∧ t x ≤ hi := by
      intro x hx
      exact ⟨T.min'_le (t x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩),
        T.le_max' (t x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)⟩
    obtain ⟨a, ha, hta⟩ := Finset.mem_image.mp (T.min'_mem hT)
    obtain ⟨b, hb, htb⟩ := Finset.mem_image.mp (T.max'_mem hT)
    have hlohi : lo ≤ hi := (hrange a ha).1.trans (hrange a ha).2
    apply kernel_population_real_bound_of_range S hm hc hu t lo hi hX heq hrange
    have hd := kernel_squareFactor_diameter hu hX (heq b hb) (heq a ha) (hdiam b hb a ha)
    have hmn : |((m : ℤ) : ℝ)| = (m : ℝ) := by simp
    rw [hmn] at hd
    change t a = lo at hta
    change t b = hi at htb
    rw [hta, htb] at hd
    rw [Nat.cast_sub hlohi]
    rwa [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hlohi))] at hd
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end Ostmann.QuadraticCenter

end OAI

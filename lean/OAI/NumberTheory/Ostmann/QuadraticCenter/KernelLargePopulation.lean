import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelPopulationBound

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem kernel_population_le_kernel_count
    (S K : Finset ℤ) {m : ℕ} (hm : 0 < m) {h : ℤ}
    (hc : IsCoprime h (m : ℤ)) (u : ℤ → ℤ) (t : ℤ → ℕ)
    {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 < Y)
    (heq : ∀ x ∈ S, (m : ℤ) * x - h = u x * (t x : ℤ) ^ 2)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |(x : ℝ) - (y : ℝ)| ≤ X)
    (hmem : ∀ x ∈ S, u x ∈ K)
    (hlarge : ∀ v ∈ K, Y ≤ |(v : ℝ)|) :
    (S.card : ℝ) ≤ (K.card : ℝ) *
      (4 * Real.sqrt (X / Y) + 8 * Real.sqrt (m : ℝ)) := by
  classical
  have hsum : (S.card : ℝ) = ∑ v ∈ K, ((S.filter (fun x => u x = v)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise (f := u) (s := S) (t := K) hmem
  rw [hsum]
  calc
    (∑ v ∈ K, ((S.filter (fun x => u x = v)).card : ℝ)) ≤
        ∑ _v ∈ K, (4 * Real.sqrt (X / Y) + 8 * Real.sqrt (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro v hv
      have hvpos : 0 < |(v : ℝ)| := hY.trans_le (hlarge v hv)
      have hvne : v ≠ 0 := by
        intro hz
        simp [hz] at hvpos
      have hb := kernel_population_real_bound (S.filter (fun x => u x = v)) hm hc hvne
        t hX (fun x hx => by
          obtain ⟨hxs, hxv⟩ := Finset.mem_filter.mp hx
          simpa only [hxv] using heq x hxs)
        (fun x hx y hy => hdiam x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1)
      have hdiv : X / |(v : ℝ)| ≤ X / Y := div_le_div_of_nonneg_left hX hY (hlarge v hv)
      have hsqrt := Real.sqrt_le_sqrt hdiv
      exact hb.trans (by nlinarith)
    _ = (K.card : ℝ) * (4 * Real.sqrt (X / Y) + 8 * Real.sqrt (m : ℝ)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

theorem large_kernel_tail_bound
    (S : Finset ℤ) {m : ℕ} (hm : 0 < m) {h : ℤ}
    (hc : IsCoprime h (m : ℤ)) (u : ℤ → ℤ) (t : ℤ → ℕ)
    {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 < Y)
    (heq : ∀ x ∈ S, (m : ℤ) * x - h = u x * (t x : ℤ) ^ 2)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |(x : ℝ) - (y : ℝ)| ≤ X) :
    let T := S.filter (fun x => Y ≤ |(u x : ℝ)|)
    (T.card : ℝ) ≤ ((T.image u).card : ℝ) *
      (4 * Real.sqrt (X / Y) + 8 * Real.sqrt (m : ℝ)) := by
  classical
  dsimp only
  apply kernel_population_le_kernel_count _ _ hm hc u t hX hY
  · intro x hx
    exact heq x (Finset.mem_filter.mp hx).1
  · intro x hx y hy
    exact hdiam x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1
  · intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hx).2

end Ostmann.QuadraticCenter

end OAI

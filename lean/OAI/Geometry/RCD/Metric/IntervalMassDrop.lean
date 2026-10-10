import Mathlib

namespace OAI

/-! # A uniform subdivision detects a quantitative drop in finite mass -/

open Set Filter MeasureTheory Finset
noncomputable section
namespace RegularPointCoordinates

theorem exists_large_sequence_drop (v : ℕ → ℝ) {n : ℕ} (hn : 0<n) :
    ∃ k<n, (v 0-v n)/(n:ℝ)≤v k-v (k+1) := by
  by_contra h
  have hlt : ∀ k∈Finset.range n, v k-v (k+1)<(v 0-v n)/(n:ℝ) := by
    intro k hk
    exact lt_of_not_ge (fun hk' => h ⟨k,Finset.mem_range.mp hk,hk'⟩)
  have hs := Finset.sum_lt_sum (fun k hk => (hlt k hk).le)
    ⟨0,Finset.mem_range.mpr hn,hlt 0 (Finset.mem_range.mpr hn)⟩
  rw [Finset.sum_range_sub',Finset.sum_const,Finset.card_range,nsmul_eq_mul,
    mul_div_cancel₀ _ (show (n:ℝ)≠0 by positivity)] at hs
  exact (lt_irrefl _ hs)

def intervalGrid (a b : ℝ) (n k : ℕ) : ℝ := a+(b-a)*(k:ℝ)/(n:ℝ)

theorem intervalGrid_zero (a b : ℝ) (n : ℕ) : intervalGrid a b n 0=a := by
  simp [intervalGrid]

theorem intervalGrid_self (a b : ℝ) {n : ℕ} (hn : 0<n) : intervalGrid a b n n=b := by
  unfold intervalGrid
  rw [mul_div_cancel_right₀ _ (show (n:ℝ)≠0 by positivity)]
  ring

theorem intervalGrid_monotone {a b : ℝ} (hab : a≤b) {n : ℕ} (hn : 0<n) :
    Monotone (intervalGrid a b n) := by
  intro i j hij
  unfold intervalGrid
  gcongr

theorem exists_large_interval_drop (f : ℝ → ℝ) (a b : ℝ) {n : ℕ} (hn : 0<n) :
    ∃ k<n, (f a-f b)/(n:ℝ)≤
      f (intervalGrid a b n k)-f (intervalGrid a b n (k+1)) := by
  simpa only [intervalGrid_zero,intervalGrid_self a b hn] using
    exists_large_sequence_drop (fun k => f (intervalGrid a b n k)) hn

variable {Ω : Type*} [MeasurableSpace Ω]

theorem exists_large_nested_mass_drop (σ : Measure Ω) [IsFiniteMeasure σ]
    {B : ℝ → Set Ω} (hB : ∀ t, MeasurableSet (B t)) (hmono : Antitone B)
    {a b : ℝ} (hab : a≤b) {n : ℕ} (hn : 0<n) :
    ∃ k<n, (σ.real (B a)-σ.real (B b))/(n:ℝ)≤
      σ.real (B (intervalGrid a b n k) \ B (intervalGrid a b n (k+1))) := by
  obtain ⟨k,hk,hdrop⟩ := exists_large_interval_drop (fun t => σ.real (B t)) a b hn
  refine ⟨k,hk,?_⟩
  rwa [measureReal_sdiff (hmono (intervalGrid_monotone hab hn (Nat.le_succ k)))
    (hB _) (by finiteness)]

end RegularPointCoordinates

end

end OAI

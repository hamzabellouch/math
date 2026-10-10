import OAI.NumberTheory.ZetaFive.Identities.WeightedPNT

namespace OAI

open Finset

namespace Zeta5.Workers.W14

theorem log_prime_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ Real.log (p : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast hp.one_lt.le

theorem weightedPrimeIntervalSum_mono
    {F G : ℝ → ℝ} {α β R : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hR : 0 < R)
    (hFG : ∀ x ∈ Set.Ioc α β, F x ≤ G x) :
    weightedPrimeIntervalSum F α β R ≤ weightedPrimeIntervalSum G α β R := by
  unfold weightedPrimeIntervalSum
  apply div_le_div_of_nonneg_right _ hR.le
  apply Finset.sum_le_sum
  intro p hp
  have hmem := (mem_primeInterval_iff (mul_nonneg hα hR.le)
    (mul_le_mul_of_nonneg_right hαβ hR.le) p).mp hp
  apply mul_le_mul_of_nonneg_right _ (log_prime_nonneg hmem.2.2)
  apply hFG
  exact ⟨(lt_div_iff₀ hR).mpr hmem.1, (div_le_iff₀ hR).mpr hmem.2.1⟩

theorem weightedPrimeIntervalSum_nonneg
    {F : ℝ → ℝ} {α β R : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hR : 0 < R)
    (hF : ∀ x ∈ Set.Ioc α β, 0 ≤ F x) :
    0 ≤ weightedPrimeIntervalSum F α β R := by
  have h := weightedPrimeIntervalSum_mono hα hαβ hR hF
  simpa only [weightedPrimeIntervalSum_const, zero_mul] using h

theorem weightedPrimeIntervalSum_bounds
    {F : ℝ → ℝ} {α β R l u : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hR : 0 < R)
    (hF : ∀ x ∈ Set.Ioc α β, l ≤ F x ∧ F x ≤ u) :
    l * (primeIntervalSum (α * R) (β * R) / R) ≤
        weightedPrimeIntervalSum F α β R ∧
      weightedPrimeIntervalSum F α β R ≤
        u * (primeIntervalSum (α * R) (β * R) / R) := by
  constructor
  · simpa only [weightedPrimeIntervalSum_const] using
      weightedPrimeIntervalSum_mono hα hαβ hR (fun x hx => (hF x hx).1)
  · simpa only [weightedPrimeIntervalSum_const] using
      weightedPrimeIntervalSum_mono hα hαβ hR (fun x hx => (hF x hx).2)

theorem weightedPrimeIntervalSum_sub (F G : ℝ → ℝ) (α β R : ℝ) :
    weightedPrimeIntervalSum (fun x => F x - G x) α β R =
      weightedPrimeIntervalSum F α β R - weightedPrimeIntervalSum G α β R := by
  simp only [weightedPrimeIntervalSum, sub_mul, Finset.sum_sub_distrib, sub_div]

theorem weightedPrimeIntervalSum_uniform_error
    {F G : ℝ → ℝ} {α β R ε : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hR : 0 < R)
    (hFG : ∀ x ∈ Set.Ioc α β, |F x - G x| ≤ ε) :
    |weightedPrimeIntervalSum F α β R - weightedPrimeIntervalSum G α β R| ≤
      ε * (primeIntervalSum (α * R) (β * R) / R) := by
  have h := weightedPrimeIntervalSum_bounds hα hαβ hR
    (fun x hx => abs_le.mp (hFG x hx))
  rw [weightedPrimeIntervalSum_sub] at h
  exact abs_le.mpr ⟨by simpa only [neg_mul] using h.1, h.2⟩

end Zeta5.Workers.W14

end OAI

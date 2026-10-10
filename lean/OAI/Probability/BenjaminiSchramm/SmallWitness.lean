import OAI.Probability.UnimodularPercolation.Exploration.Marked
import OAI.Probability.UnimodularPercolation.Criticality.Susceptibility

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe v
variable {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem small_witness_derivative_bound (Q : Finset E) (A : Finset E → Prop)
    (hmono : ∀ ω η, ω ⊆ η → A ω → A η) (r : ℕ)
    (hcert : ∀ ω ⊆ Q, A ω → ∃ s ⊆ ω, s.card ≤ r ∧ ∀ η, s ⊆ η → A η)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    p * deriv (bernoulliPolynomial Q (fun ω => if A ω then 1 else 0)) p ≤
      (r : ℝ) * bernoulliPolynomial Q (fun ω => if A ω then 1 else 0) p := by
  let f : Finset E → ℝ := fun ω => if A ω then 1 else 0
  have hrusso : p * deriv (bernoulliPolynomial Q f) p =
      bernoulliPolynomial Q (fun ω => ∑ e ∈ Q,
        if e ∈ ω then f ω - f (ω.erase e) else 0) p := by
    rw [(hasDerivAt_bernoulliPolynomial Q f p).deriv, Finset.mul_sum,
      bernoulliPolynomial_sum]
    apply Finset.sum_congr rfl
    intro e he
    exact (bernoulliPolynomial_open_difference Q e he f p).symm
  change p * deriv (bernoulliPolynomial Q f) p ≤
    (r : ℝ) * bernoulliPolynomial Q f p
  rw [hrusso, ←bernoulliPolynomial_const_mul]
  apply bernoulliPolynomial_mono Q _ _ p hp
  intro ω hω
  by_cases hA : A ω
  · obtain ⟨s,hs,hsr,hsa⟩ := hcert ω hω hA
    calc
      _ ≤ ∑ e ∈ Q, if e ∈ s then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro e he
        by_cases hes : e ∈ s
        · by_cases heω : e ∈ ω <;> by_cases herase : A (ω.erase e) <;>
            simp [f,hA,hes,heω,herase]
        · have herase : A (ω.erase e) := hsa _ (by
            intro a ha
            exact Finset.mem_erase.mpr ⟨fun hae => hes (hae ▸ ha),hs ha⟩)
          simp [f,hA,hes,herase]
      _ = ((Q.filter (fun e => e ∈ s)).card : ℝ) := by
        rw [Finset.card_filter, Nat.cast_sum]
        simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      _ ≤ (s.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (show Q.filter (fun e => e ∈ s) ⊆ s from
          fun e he => (Finset.mem_filter.mp he).2)
      _ ≤ (r : ℝ) * f ω := by simpa [f,hA] using (show (s.card : ℝ) ≤ r by exact_mod_cast hsr)
  · have herase (e : E) : ¬ A (ω.erase e) := fun h =>
      hA (hmono _ _ (Finset.erase_subset e ω) h)
    simp [f,hA,herase]

theorem small_witness_probability_transfer (Q : Finset E) (A : Finset E → Prop)
    (hmono : ∀ ω η, ω ⊆ η → A ω → A η) (r : ℕ)
    (hcert : ∀ ω ⊆ Q, A ω → ∃ s ⊆ ω, s.card ≤ r ∧ ∀ η, s ⊆ η → A η)
    (p q : unitInterval) (hp : 0 < (p : ℝ)) (hpq : p ≤ q) :
    bernoulliPolynomial Q (fun ω => if A ω then 1 else 0) q ≤
      Real.exp ((r : ℝ) / p * ((q : ℝ) - p)) *
        bernoulliPolynomial Q (fun ω => if A ω then 1 else 0) p := by
  let H := bernoulliPolynomial Q (fun ω => if A ω then (1 : ℝ) else 0)
  apply exponential_transfer_of_deriv_bound H p q ((r : ℝ) / p)
    (fun t => (hasDerivAt_bernoulliPolynomial Q _ t).differentiableAt) hpq
  intro t ht
  have ht0 : 0 < t := hp.trans_le ht.1
  have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht0.le,ht.2.trans q.2.2⟩
  have hb := small_witness_derivative_bound Q A hmono r hcert t htI
  have hH : 0 ≤ H t := bernoulliPolynomial_nonneg Q _ t htI (fun ω _ => by split <;> positivity)
  calc
    deriv H t ≤ (r : ℝ) * H t / t := (le_div_iff₀ ht0).mpr (by simpa only [mul_comm t] using hb)
    _ ≤ (r : ℝ) * H t / p := div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg r) hH) hp ht.1
    _ = _ := by ring

end Percolation.BenjaminiSchramm

end OAI

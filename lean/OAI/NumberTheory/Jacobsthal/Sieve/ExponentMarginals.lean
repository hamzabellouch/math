import OAI.NumberTheory.Jacobsthal.Estimates.ProductRestriction

namespace OAI

namespace Erdos970


namespace EulerWeightedLower
open Erdos970.EulerPrimeLaw
attribute [local instance] Classical.propDecidable

lemma product_event_indicator {ι : Type*} [Fintype ι] (A : ι → Prop)
    (w : ι → ℝ) :
    (∏ i, if A i then w i else 0) = if ∀ i, A i then ∏ i, w i else 0 := by
  classical
  by_cases h : ∀ i, A i
  · simp [h]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem product_marginal (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p)
    (A : E → Sample → Prop) (a : E → ℝ)
    (ha : ∀ p, (∑' s : Sample, if A p s then jointMass (p : ℝ) s else 0) = a p) :
    eventMass E (fun s => ∀ p, A p (s p)) = ∏ p, a p := by
  have h := hasSum_finite_product (fun p s => if A p s then jointMass (p : ℝ) s else 0)
    a (by intro p s; split_ifs; exact jointMass_nonneg (by exact_mod_cast hE p p.property) s; rfl)
    (by intro p; rw [← ha p]; exact (event_summable (by exact_mod_cast hE p p.property) (A p)).hasSum)
  rw [← h.tsum_eq]
  apply tsum_congr
  intro s
  have he := (product_event_indicator (fun p => A p (s p)) (fun p => jointMass (p : ℝ) (s p))).symm
  by_cases hh : ∀ p, A p (s p)
  · rw [ite_eq_left hh] at he
    rw [ite_eq_left hh]
    exact he
  · rw [ite_eq_right hh] at he
    rw [ite_eq_right hh]
    exact he

theorem upper_vector_marginal (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p) (k : E → ℕ) :
    eventMass E (fun s => ∀ p, upperExponent (s p) = k p) =
      ∏ p : E, eulerMass (p : ℝ) (k p) := by
  exact product_marginal E hE (fun p s => upperExponent s = k p)
    (fun p => eulerMass (p : ℝ) (k p))
    (by
      intro p
      have hp := upperExponent_marginal (p := (p : ℝ)) (by exact_mod_cast hE p p.property) (k p)
      convert hp using 1
      apply tsum_congr
      intro s
      by_cases hh : upperExponent s = k p <;> simp only [hh, ite_true, ite_false])

theorem lower_vector_marginal (E : Finset ℕ) (hE : ∀ p ∈ E, 2 ≤ p) (k : E → ℕ) :
    eventMass E (fun s => ∀ p, lowerExponent (s p) = k p) =
      ∏ p : E, geometricMass (p : ℝ) (k p) := by
  exact product_marginal E hE (fun p s => lowerExponent s = k p)
    (fun p => geometricMass (p : ℝ) (k p))
    (by
      intro p
      have hp := lowerExponent_marginal (p := (p : ℝ)) (by exact_mod_cast hE p p.property) (k p)
      convert hp using 1
      apply tsum_congr
      intro s
      by_cases hh : lowerExponent s = k p <;> simp only [hh, ite_true, ite_false])

end EulerWeightedLower


end Erdos970

end OAI

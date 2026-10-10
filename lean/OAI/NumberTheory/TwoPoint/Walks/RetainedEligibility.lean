import OAI.NumberTheory.TwoPoint.Bounds.PrefixDeletionBridge

namespace OAI

/-! On the actual tuple and padding pools, canonical pair membership
agrees with the original bin eligibility, including inside the density cut. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma canonicalTraceFamily_pair_on_pool (h : ℕ) (E : Finset ℕ) (W L : ℝ)
    (eligible : ℕ → ℕ → Prop) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hE : ∀ p, p.Prime → p ∣ h → p ∈ E) (d q : ℕ)
    (hd : d ∈ primeTupleDivisors
      (centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W (primeSupplyCount W L)))
    (hq : q ∈ boundedPaddingDivisors (paddingPrimeSupply E L) ⌊100 * Real.log L⌋₊) :
    (d, q) ∈ (canonicalTraceFamily h E W L eligible hL hW hE).pairs ↔ eligible d q := by
  rw [canonicalTraceFamily, actualProhibitedPrimeFamily_pairs]
  simp only [hd, (mem_filter.mp hq).1, (mem_filter.mp hq).2, true_and]

lemma integerEdgeKeep_congr_eligible (R : Finset ℕ) (u : ℕ → ℝ)
    (e f : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop)
    (hef : ∀ q ∈ R, e q ↔ f q) (n : ℤ) :
    integerEdgeKeep R u e g L K extra n ↔ integerEdgeKeep R u f g L K extra n := by
  have he : paddingDensity R u e g n = paddingDensity R u f g n := by
    unfold paddingDensity
    congr 1
    apply sum_congr rfl
    intro q hq
    simp only [hef q hq]
  simp only [integerEdgeKeep, he]

lemma retainedNumericalEdge_congr_eligible {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (u : ℕ → ℝ) (e f : ℕ → ℕ → Prop) (L K W : ℝ)
    (extra : ℕ → ℤ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (keep : ℤ → Prop) (d q : ℕ) (n m : ℤ) (hq : q ∈ R)
    (hef : ∀ r ∈ R, e d r ↔ f d r) :
    retainedNumericalEdge P R Q u e L K W extra h gate keep d q n m =
      retainedNumericalEdge P R Q u f L K W extra h gate keep d q n m := by
  have hk := integerEdgeKeep_congr_eligible R u (e d) (f d)
    (actualPaddingVertex Q) L K (extra d) hef
  simp only [retainedNumericalEdge, retainedLiouvilleEdge, hef q hq, hk]
  split_ifs <;> rfl

lemma retainedPrimePrefix_congr_eligible {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ i, ∀ p ∈ P i, p.Prime)
    (hdisjoint : ∀ i k, k ≠ i → Disjoint (P i) (P k))
    (R Q : Finset ℕ) (u : ℕ → ℝ) (e f : ℕ → ℕ → Prop) (L K W : ℝ)
    (extra : ℕ → ℤ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (keep : ℤ → Prop) (N : ℕ)
    (hef : ∀ d ∈ primeTupleDivisors P, ∀ q ∈ R, e d q ↔ f d q) :
    retainedPrimePrefix P R Q u e L K W extra h gate keep N =
      retainedPrimePrefix P R Q u f L K W extra h gate keep N := by
  rw [retainedPrimePrefix_eq_numerical P hprime hdisjoint,
    retainedPrimePrefix_eq_numerical P hprime hdisjoint]
  congr 2
  funext n
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro q hq
  exact retainedNumericalEdge_congr_eligible P R Q u e f L K W extra h gate keep
    d q n ((n : ℤ) + (h * q * d : ℕ)) hq (hef d hd)

end TwoPointCorrelations

end OAI

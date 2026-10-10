import OAI.NumberTheory.Ostmann.Supply.ConcreteExtensionWeights

namespace OAI

/-! # The centered-subset budget with all extension weights discharged -/

namespace Ostmann
open scoped Classical BigOperators

theorem floor_product_half_bound {Q t : ℕ} (ht : 0 < t) (htQ : t ≤ Q) :
    (Q : ℝ) / 2 ≤ (t : ℝ) * (Q / t : ℕ) := by
  have hU : 1 ≤ Q / t := (Nat.le_div_iff_mul_le ht).mpr (by simpa using htQ)
  have hmod := Nat.mod_lt Q ht
  have hid := Nat.mod_add_div Q t
  have htU := Nat.mul_le_mul_left t hU
  have hQ : Q ≤ 2 * (t * (Q / t)) := by nlinarith
  have hQr : (Q : ℝ) ≤ 2 * ((t : ℝ) * (Q / t : ℕ)) := by exact_mod_cast hQ
  linarith

/-- The finite form of (5.4), before specializing the logarithmic budget.
Its multiplier lower bound is proved from squarefreeness, divisibility counts
and Markov's inequality; it is not an additional analytic assumption. -/
theorem concrete_subset_energy_budget (ls : PublishedAdditiveLargeSieve)
    {n M Q : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (hS : ∀ i, (S i).Nonempty)
    (κ : ℕ → ℝ) (hκ : ∀ q ∈ Finset.univ.image p, 0 < κ q)
    (hκS : ∀ i, κ (p i) = (p i : ℝ) / (S i).card - 1)
    (hQ : 1 ≤ Q) (hM : 1 ≤ M)
    (hcover : ∀ q, Nat.Prime q → q ≤ Q → ∃ i, p i = q)
    (A : Finset (Fin M)) (hA : A.Nonempty) (J : ℤ)
    (ha : ∀ x ∈ A, ∀ i, ((J + (x.val : ℤ) : ℤ) : ZMod (p i)) ∈ S i)
    (F : Finset (Finset (Fin n)))
    (hprod : ∀ T ∈ F, (∏ i ∈ T, p i) ≤ Q)
    (hsmall : ∀ T ∈ F, (∑ q ∈ T.image p, (q : ℝ)⁻¹) ≤ 1 / 16)
    (B : ℝ) (hB : 0 < B)
    (hP : (∑ q ∈ Finset.univ.image p, |Real.log (κ q)| / q) ≤ B / 16) :
    ((Q : ℝ) / 16 * Real.exp (-B)) *
      (∑ T ∈ F, centeredSubsetEnergy p S T A
        (fun x i => ((J + (x.val : ℤ) : ℤ) : ZMod (p i)))) ≤
      ((M : ℝ) + (Q : ℝ) ^ 2) / A.card := by
  apply prime_subset_energy_budget ls p hc S hS F (primeProductSubsets p Q)
    hQ hM A hA J
  · intro R hR
    exact (Finset.mem_filter.mp hR).2
  · intro R _ x hx i _
    exact ha x hx i
  · intro T hT
    have ht : 0 < ∏ i ∈ T, p i :=
      Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
    have hhalf := floor_product_half_bound ht (hprod T hT)
    have hw := concrete_extension_weight_lower p hc S hS κ hκ hκS Q T hcover B hB
      (hsmall T hT) hP
    apply le_trans _ hw
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    linarith

end Ostmann

end OAI

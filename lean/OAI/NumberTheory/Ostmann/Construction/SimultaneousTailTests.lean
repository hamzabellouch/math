import OAI.NumberTheory.Ostmann.Construction.EndpointTestScale

namespace OAI

/-! # Simultaneously typical endpoints for a finite family of prime sets -/

namespace Ostmann

open scoped BigOperators Classical

theorem simultaneous_tail_tests {ι : Type*} [DecidableEq ι]
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite)
    (N X Q K : ℕ) (hX : 1 ≤ X) (hQ : 1 ≤ Q) (hK : 0 < K)
    (hdis : ∀ p ∈ Nat.primesLE Q, Disjoint (tailResidues A N p) (negTailResidues B N p))
    (E D : Finset ℕ) (hD : K ≤ D.card)
    (hEtail : ∀ a ∈ E, a ∈ A ∧ N + Q < a ∧ a ≤ X)
    (hDtail : ∀ b ∈ D, b ∈ B ∧ N + Q < b ∧ b ≤ X)
    (J : Finset ι) (P : ι → Finset ℕ) (b δ c C : ℝ)
    (hb : 0 < b) (hδ : 0 < δ) (hc : 0 < c) (hM : MertensLowerBound C)
    (F : ℕ → ℕ → ℝ)
    (hP : ∀ j ∈ J, P j ⊆ Nat.primesLE Q)
    (hlog : ∀ j ∈ J, ∀ p ∈ P j, b ≤ Real.log (p : ℝ))
    (hF : ∀ j ∈ J, ∀ p ∈ P j, ∀ r ∈ tailSupport A N p, |F p r| ≤ 1)
    (hmass : ∀ j ∈ J, c ≤ ∑ p ∈ P j, (p : ℝ)⁻¹)
    (href : ∀ j ∈ J, δ * (∑ p ∈ P j, (p : ℝ)⁻¹) ≤
      ∑ p ∈ P j, (p : ℝ)⁻¹ * residueTestMean (tailSupport A N p) (F p))
    (hsmall : 4 * ((2 * Real.log X - 4 * Real.log Q + 4 * C +
      2 * (1 / (K : ℝ)) * Real.log 4 * Q) / b) < δ ^ 2 * c) :
    ∃ G ⊆ E, E.card ≤ G.card + J.card * K ∧
      ∀ a ∈ G, ∀ j ∈ J,
        (δ / 2) * (∑ p ∈ P j, (p : ℝ)⁻¹) ≤
          ∑ p ∈ P j, (p : ℝ)⁻¹ * F p (a % p) := by
  let bad := fun j => badEndpoints E (P j) (fun p => (p : ℝ)⁻¹)
    (fun a p => F p (a % p)) δ
  have hbad : ∀ j ∈ J, (bad j).card ≤ K := by
    intro j hj
    apply Nat.le_of_lt
    apply few_bad_tail_endpoints hA hB N X Q K hX hQ hK hdis E D (P j) hD hEtail hDtail
      (hP j hj) b δ C hb hδ hM (hlog j hj) F (hF j hj)
      (hc.trans_le (hmass j hj)) (href j hj)
    exact hsmall.trans_le (mul_le_mul_of_nonneg_left (hmass j hj) (sq_nonneg δ))
  obtain ⟨G, hGE, hGcard, hG⟩ := simultaneous_good_endpoints E J bad K hbad
  refine ⟨G, hGE, hGcard, ?_⟩
  intro a ha j hj
  have h := hG a ha j hj
  have haE := hGE ha
  simpa only [bad, badEndpoints, Finset.mem_filter, haE, true_and, not_lt] using h

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Construction.SimultaneousTailTests

namespace OAI

/-! # Large sets of endpoints passing every prescribed prime test -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem eventual_typical_tail_tests {ι : Type*} [DecidableEq ι]
    (hsize : PublishedSummandSizeBound) {C : ℝ} (hM : MertensLowerBound C)
    {A B : Set ℕ} (hA : A.Infinite) (hB : B.Infinite) (h : EventuallyPrimeSumset A B)
    (N : ℕ) (hN : ∀ p, p.Prime → Disjoint (tailResidues A N p) (negTailResidues B N p))
    (J : Finset ι) (α β D δ c : ℝ) (hα : 0 < α) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ a : ℝ, 0 < a ∧ ∃ L₀ t₀ : ℝ, ∀ L t : ℝ, L₀ ≤ L → t₀ ≤ t →
      Real.log t ≤ β * L + D → ∀ X : ℕ, (X : ℝ) = Real.exp t →
      ∀ (P : ι → Finset ℕ) (F : ℕ → ℕ → ℝ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime ∧ (p : ℝ) ≤ Real.exp (t / 4) ∧
        Real.exp (α * L) ≤ Real.log (p : ℝ)) →
      (∀ j ∈ J, ∀ p ∈ P j, ∀ r ∈ tailSupport A N p, |F p r| ≤ 1) →
      (∀ j ∈ J, c ≤ ∑ p ∈ P j, (p : ℝ)⁻¹) →
      (∀ j ∈ J, δ * (∑ p ∈ P j, (p : ℝ)⁻¹) ≤
        ∑ p ∈ P j, (p : ℝ)⁻¹ * residueTestMean (tailSupport A N p) (F p)) →
      ∃ G ⊆ summandTail A (summandTailCutoff t) X,
        a * Real.exp (t / 2) / t ^ 3 ≤ (G.card : ℝ) ∧
        ∀ x ∈ G, ∀ j ∈ J, (δ / 2) * (∑ p ∈ P j, (p : ℝ)⁻¹) ≤
          ∑ p ∈ P j, (p : ℝ)⁻¹ * F p (x % p) := by
  obtain ⟨a, ha, hcounts⟩ := exists_large_summand_tails hsize hA hB h
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventual_endpoint_test_error_small α β D C δ c hα hδ hc)
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp (hcounts.and
    (eventual_endpointTestCutoff.and (eventual_endpointTestCutoff_quarter.and
      ((eventual_tailCollisionCutoff N).and
        ((eventual_endpoint_test_threshold_negligible a ha 1).and
          (eventual_endpoint_test_threshold_negligible a ha J.card))))))
  refine ⟨a / 2, by positivity, L₀, t₀, ?_⟩
  intro L t hL ht hlog X hX P F hP hF hmass href
  obtain ⟨hcounts, hcut, hquarter, htail, hKsmall, hJsmall⟩ := ht₀ t ht
  have htp : 0 < t := by linarith [hcut.1]
  obtain ⟨hEA, hDB, _⟩ := hcounts X hX
  simp only [positiveSummandTail_card] at hEA
  simp only [negativeSummandTail_card] at hDB
  let E := summandTail A (summandTailCutoff t) X
  let T := summandTail B (summandTailCutoff t) X
  let Q := endpointTestCutoff t
  let K := endpointTestThreshold t
  have hKpos : 0 < K := lt_of_lt_of_le (by decide : 0 < 1)
    (endpointTestThreshold_bounds t htp).1
  have hQpos : 1 ≤ Q := (endpointTestCutoff_bounds t hcut.1 hcut.2).1
  have hXpos : 1 ≤ X := by
    have hx := Real.one_le_exp htp.le
    rw [← hX] at hx
    exact_mod_cast hx
  have hTK : K ≤ T.card := by
    simp only [Nat.cast_one, one_mul] at hKsmall
    have hscale : (a / 2) * Real.exp (t / 2) / t ^ 3 ≤ a * Real.exp (t / 2) / t ^ 3 := by
      gcongr
      linarith
    have hk : (K : ℝ) ≤ T.card := hKsmall.trans (hscale.trans hDB)
    exact_mod_cast hk
  have hNQ : N + Q ≤ summandTailCutoff t :=
    (Nat.add_le_add_left (endpointTestCutoff_le_tailCollisionCutoff t hcut.1) N).trans htail.2.2
  have hEtail : ∀ x ∈ E, x ∈ A ∧ N + Q < x ∧ x ≤ X := by
    intro x hx
    obtain ⟨hxA, hxlo, hxX⟩ := (mem_summandTail A _ _ x).mp hx
    exact ⟨hxA, hNQ.trans_lt hxlo, hxX⟩
  have hTtail : ∀ x ∈ T, x ∈ B ∧ N + Q < x ∧ x ≤ X := by
    intro x hx
    obtain ⟨hxB, hxlo, hxX⟩ := (mem_summandTail B _ _ x).mp hx
    exact ⟨hxB, hNQ.trans_lt hxlo, hxX⟩
  have hPQ : ∀ j ∈ J, P j ⊆ Nat.primesLE Q := by
    intro j hj p hp
    exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast ((hP j hj p hp).2.1.trans hquarter),
      (hP j hj p hp).1⟩
  have hsmall : 4 * ((2 * Real.log X - 4 * Real.log Q + 4 * C +
      2 * (1 / (K : ℝ)) * Real.log 4 * Q) / Real.exp (α * L)) < δ ^ 2 * c := by
    have hbudget := endpoint_test_collision_budget_le t C X hcut.1 hcut.2
      (by rw [hX, Real.log_exp])
    have hb := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hbudget (Real.exp_nonneg (α * L))) (by norm_num : (0 : ℝ) ≤ 4)
    exact hb.trans_lt (hL₀ L hL t hlog)
  obtain ⟨G, hGE, hGcard, hGgood⟩ := simultaneous_tail_tests hA hB N X Q K hXpos hQpos hKpos
    (fun p hp => hN p (Nat.prime_of_mem_primesLE hp)) E T hTK hEtail hTtail J P
    (Real.exp (α * L)) δ c C (Real.exp_pos _) hδ hc hM F hPQ
    (fun j hj p hp => (hP j hj p hp).2.2) hF hmass href hsmall
  refine ⟨G, hGE, ?_, hGgood⟩
  have hcardR : (E.card : ℝ) ≤ (G.card : ℝ) + (J.card : ℝ) * K := by exact_mod_cast hGcard
  have hscale : a * Real.exp (t / 2) / t ^ 3 =
      2 * ((a / 2) * Real.exp (t / 2) / t ^ 3) := by ring
  rw [hscale] at hEA
  linarith

end Ostmann

end OAI

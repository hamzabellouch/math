import OAI.NumberTheory.EgyptianFractions.Defs

namespace OAI
noncomputable section

open scoped BigOperators
open Filter

namespace Problem337

/-- A positive tail whose total is smaller than every reserved term cannot
reuse a reserved denominator. -/
theorem marked_tail_disjoint (p t : Finset ℕ)
    (hsmall : ∀ d ∈ p, (∑ e ∈ t, (1 : ℚ) / (e : ℚ)) < 1 / (d : ℚ)) :
    Disjoint p t := by
  apply Finset.disjoint_left.2
  intro d hdp hdt
  have hterm : (1 : ℚ) / (d : ℚ) ≤ ∑ e ∈ t, (1 : ℚ) / (e : ℚ) := by
    exact Finset.single_le_sum (f := fun e : ℕ => (1 : ℚ) / (e : ℚ))
      (fun e he => by positivity) hdt
  exact (not_lt_of_ge hterm) (hsmall d hdp)

/-- Adjoining a small distinct tail preserves every denominator in the prefix,
including the prescribed marker, and adds the lengths exactly. -/
theorem marked_expansion_of_small_tail (p t : Finset ℕ) (m : ℕ)
    (hp : ∀ d ∈ p, 1 ≤ d) (ht : ∀ d ∈ t, 1 ≤ d)
    (hm : m ∈ p)
    (hsum : (∑ d ∈ p, (1 : ℚ) / (d : ℚ)) +
      (∑ d ∈ t, (1 : ℚ) / (d : ℚ)) = 1)
    (hsmall : ∀ d ∈ p, (∑ e ∈ t, (1 : ℚ) / (e : ℚ)) < 1 / (d : ℚ)) :
    ∃ n : Fin (p.card + t.card) → ℕ,
      IsOneExpansion n ∧ ∃ i, n i = m := by
  classical
  have hdis : Disjoint p t := marked_tail_disjoint p t hsmall
  let s := p ∪ t
  have hcard : s.card = p.card + t.card := Finset.card_union_of_disjoint hdis
  let n : Fin (p.card + t.card) ↪o ℕ := s.orderEmbOfFin hcard
  refine ⟨n, ⟨?_, n.strictMono, ?_⟩, ?_⟩
  · intro i
    have hi : n i ∈ s := s.orderEmbOfFin_mem hcard i
    rcases Finset.mem_union.1 hi with hi | hi
    · exact hp _ hi
    · exact ht _ hi
  · have hn : Finset.univ.image n = s := s.image_orderEmbOfFin_univ hcard
    calc
      (∑ i, (1 : ℚ) / (n i : ℚ)) = ∑ d ∈ s, (1 : ℚ) / (d : ℚ) := by
        rw [← hn, Finset.sum_image]
        intro a ha b hb hab
        exact n.injective hab
      _ = 1 := by
        change (∑ d ∈ p ∪ t, (1 : ℚ) / (d : ℚ)) = 1
        rw [Finset.sum_union hdis]
        exact hsum
  · have hm' : m ∈ s := Finset.mem_union_left t hm
    have hrange : Set.range n = (s : Set ℕ) := s.range_orderEmbOfFin hcard
    change m ∈ Set.range n
    rw [hrange]
    exact hm'

/-- The small-tail assembly accepts the standard Egyptian expansion interface. -/
theorem marked_expansion_of_egyptian_tail {k : ℕ} {x : ℚ}
    (p : Finset ℕ) (m : ℕ) (n : Fin k → ℕ)
    (hp : ∀ d ∈ p, 1 ≤ d) (hm : m ∈ p)
    (hn : IsEgyptianExpansion x n)
    (hsum : (∑ d ∈ p, (1 : ℚ) / (d : ℚ)) + x = 1)
    (hsmall : ∀ d ∈ p, x < 1 / (d : ℚ)) :
    ∃ n' : Fin (p.card + k) → ℕ,
      IsOneExpansion n' ∧ ∃ i, n' i = m := by
  classical
  let t : Finset ℕ := Finset.univ.image n
  have htcard : t.card = k := by
    simp [t, Finset.card_image_of_injective _ hn.2.1.injective]
  have htsum : (∑ d ∈ t, (1 : ℚ) / (d : ℚ)) = x := by
    rw [Finset.sum_image]
    · exact hn.2.2
    · intro a ha b hb hab
      exact hn.2.1.injective hab
  have htpos : ∀ d ∈ t, 1 ≤ d := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
    exact (hn.1 i).trans' (by omega)
  have h := marked_expansion_of_small_tail p t m hp htpos hm
    (by rw [htsum]; exact hsum) (by intro d hd; rw [htsum]; exact hsmall d hd)
  rw [← htcard]
  exact h

/-- The explicit bookkeeping at the end of the marked construction.  The
prefix costs `1 / log 2` and sixteen terms in each of `16 / log 2` groups;
the reserved marker is absorbed by the diverging double logarithm. -/
theorem quantitative_marked_length_of_prefix_group_budget
    (hbudget : ∀ δ : ℝ, 0 < δ → ∀ᶠ m : ℕ in atTop,
      ∃ j G k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        k ≤ 1 + j + 16 * G ∧
        (j : ℝ) ≤ (1 / Real.log 2 + δ) * Real.log (Real.log (m : ℝ)) ∧
        (G : ℝ) ≤ (16 / Real.log 2 + δ) * Real.log (Real.log (m : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
  intro ε hε
  have hloglog : Tendsto (fun m : ℕ => Real.log (Real.log (m : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlarge : ∀ᶠ m : ℕ in atTop, 2 / ε ≤ Real.log (Real.log (m : ℝ)) :=
    hloglog.eventually (eventually_ge_atTop (2 / ε))
  have hevent : ∀ᶠ m : ℕ in atTop, ∃ k : ℕ, ∃ n : Fin k → ℕ,
      IsOneExpansion n ∧ (∃ i, n i = m) ∧
      (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) := by
    filter_upwards [hbudget (ε / 34) (by positivity), hlarge] with m hm hlarge
    obtain ⟨j, G, k, n, hn, hmarker, hk, hj, hG⟩ := hm
    refine ⟨k, n, hn, hmarker, ?_⟩
    have hkR : (k : ℝ) ≤ 1 + (j : ℝ) + 16 * (G : ℝ) := by exact_mod_cast hk
    have hlarge' : 2 ≤ Real.log (Real.log (m : ℝ)) * ε :=
      (div_le_iff₀ hε).1 hlarge
    have hcoef : (1 : ℝ) / Real.log 2 + 16 * (16 / Real.log 2) = 257 / Real.log 2 := by ring
    nlinarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro m hm
  exact hN m ((le_max_right _ _).trans hm)

end Problem337

end

end OAI

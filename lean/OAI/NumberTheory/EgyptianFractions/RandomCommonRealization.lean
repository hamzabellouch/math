import OAI.NumberTheory.EgyptianFractions.RandomSecondMoment
import OAI.NumberTheory.EgyptianFractions.FourierCommonRealization

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- Total version of the normalized sampled character average. -/
def sampledMean {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u l : ℕ) : ℂ :=
  if hu : u = 0 then 0 else
    letI : NeZero u := ⟨hu⟩
    𝔼 I : Fin m → Bool, sampledPhase u l p I

@[simp] theorem sampledMean_eq {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u l : ℕ) [NeZero u] :
    sampledMean p u l = 𝔼 I : Fin m → Bool, sampledPhase u l p I := by
  simp [sampledMean, NeZero.ne u]

/-- The complete random moment theorem in the total normalized-average interface. -/
theorem sampledMean_second_moment_bound
    (S : ℝ) (hS : 3 ≤ S) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (u l : ℕ) (hu : 0 < u)
    (hV : 100000 * Real.log S ≤ Real.log (u : ℝ))
    (hVS : Real.log (u : ℝ) ≤ S) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200)) :
    (∑ p : (Fin (blockLength S) × Bool) → P, ‖sampledMean p u l‖ ^ 2) /
      Fintype.card ((Fin (blockLength S) × Bool) → P) ≤
        Real.exp (-min (blockLength S : ℝ) (Real.log (u : ℝ)) / 100) := by
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  simpa only [sampledMean_eq, Fintype.expect_eq_sum_div_card] using
    sampled_product_second_moment_log_bound S hS P hprime hinterval hsize u l
      hV hVS hl hlbound

/-- Concrete labelled-prime-product realization. All remaining hypotheses are
finite index bounds and explicit numeric ranges, not moment assumptions. -/
theorem exists_common_sampled_realization :
    ∃ N : ℕ, ∀ (S : ℝ) (P : Finset ℕ) (J : Type)
      (tests : Finset J) (level : J → Finset ℕ) (X : J → ℝ)
      (freq : Finset ℕ) (terminalFreq : ℕ → Finset ℕ) (terminal : Finset ℕ),
      3 ≤ S →
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
      S ^ 99 ≤ (P.card : ℝ) →
      500000 ≤ (blockLength S : ℝ) →
      (tests.card : ℝ) ≤ (blockLength S : ℝ) →
      (∀ j ∈ tests, 0 < X j) →
      (∀ j ∈ tests, ((level j).card : ℝ) ≤ X j) →
      (freq.card : ℝ) ≤ Real.exp (4 * (blockLength S : ℝ) / 10000) →
      (∀ j ∈ tests, ∀ u ∈ level j, 0 < u ∧
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ S ∧
        (9999 / 10000 : ℝ) * (blockLength S : ℝ) ≤ Real.log (u : ℝ)) →
      (∀ j ∈ tests, ∀ u ∈ level j, ∀ l ∈ freq, 0 < l ∧
        (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200)) →
      (∀ u ∈ terminal, max N 1 ≤ u ∧
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧
        Real.log (u : ℝ) ≤ min (blockLength S : ℝ) S) →
      (∀ u ∈ terminal, ((terminalFreq u).card : ℝ) ≤
        Real.exp (4 * Real.log (u : ℝ) / 10000)) →
      (∀ u ∈ terminal, ∀ l ∈ terminalFreq u, 0 < l ∧
        (l : ℝ) ≤ Real.exp (Real.log (u : ℝ) / 200)) →
      ∃ f : Fin 1000 → ((Fin (blockLength S) × Bool) → P),
        (∀ j ∈ tests,
          (((level j).filter (fun u => ∃ l ∈ freq,
            Real.exp (-3 * (blockLength S : ℝ) / 10000) <
              ‖sampledMean (f 0) u l‖)).card : ℝ) ≤
                X j * Real.exp (-(blockLength S : ℝ) / 1000)) ∧
        ∀ u ∈ terminal, ∃ i : Fin 1000, ∀ l ∈ terminalFreq u,
          ‖sampledMean (f i) u l‖ ≤ Real.exp (-3 * Real.log (u : ℝ) / 10000) := by
  classical
  obtain ⟨N, hN⟩ := FourierCommonRealization.exists_common_fourier_realization
  refine ⟨N, ?_⟩
  intro S P J tests level X freq terminalFreq terminal hS hp hi hs hm ht hX hlevel
    hf hmid hmf hterminal htf htl
  have hcard : 0 < (P.card : ℝ) := lt_of_lt_of_le (by positivity) hs
  have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcard)
  let : Nonempty P := hP.to_subtype
  apply hN ((Fin (blockLength S) × Bool) → P) J tests level X
    (blockLength S : ℝ) freq terminalFreq sampledMean
    (fun u => min (blockLength S : ℝ) (Real.log (u : ℝ))) terminal
    hm ht hX hlevel hf
  · intro j hj u hu
    apply le_min
    · have : (0 : ℝ) ≤ blockLength S := Nat.cast_nonneg _
      nlinarith
    · exact (hmid j hj u hu).2.2.2
  · intro j hj u hu l hl
    exact sampledMean_second_moment_bound S hS P hp hi hs u l
      (hmid j hj u hu).1 (hmid j hj u hu).2.1 (hmid j hj u hu).2.2.1
      (hmf j hj u hu l hl).1 (hmf j hj u hu l hl).2
  · intro u hu
    exact (le_max_left N 1).trans (hterminal u hu).1
  · exact htf
  · intro u hu l hl
    have hmin : min (blockLength S : ℝ) (Real.log (u : ℝ)) = Real.log (u : ℝ) :=
      min_eq_right ((hterminal u hu).2.2.trans (min_le_left _ _))
    have hu0 : 0 < u := by have := (le_max_right N 1).trans (hterminal u hu).1; omega
    have hbound := (htl u hu l hl).2
    rw [← hmin] at hbound
    have h := sampledMean_second_moment_bound S hS P hp hi hs u l hu0
      (hterminal u hu).2.1 ((hterminal u hu).2.2.trans (min_le_right _ _))
      (htl u hu l hl).1 hbound
    simpa only [hmin] using h

end Problem337.RandomProducts

end

end OAI

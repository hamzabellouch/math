import OAI.NumberTheory.EgyptianFractions.RandomSecondMoment
import OAI.NumberTheory.EgyptianFractions.FourierCommonRealization
import OAI.NumberTheory.EgyptianFractions.RandomSelectionParameters

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- The actual Boolean product Fourier average, extended by zero at modulus zero
only to permit a single function on all natural moduli. -/
def sampledFourierMean {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u l : ℕ) : ℂ :=
  if hu : u = 0 then 0 else
    letI : NeZero u := ⟨hu⟩
    𝔼 I : Fin m → Bool, sampledPhase u l p I

@[simp] theorem sampledFourierMean_eq {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u l : ℕ) [NeZero u] :
    sampledFourierMean p u l = 𝔼 I : Fin m → Bool, sampledPhase u l p I := by
  simp [sampledFourierMean, NeZero.ne u]

/-- The positive frequencies required by the discrepancy stage. -/
def fourierFrequencySet (t : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌊Real.exp (t / 2500)⌋₊

theorem mem_fourierFrequencySet {t : ℝ} {l : ℕ}
    (hl : l ∈ fourierFrequencySet t) :
    0 < l ∧ (l : ℝ) ≤ Real.exp (t / 2500) := by
  obtain ⟨hl, hbound⟩ := Finset.mem_Icc.mp hl
  refine ⟨hl, ?_⟩
  exact (Nat.cast_le.mpr hbound).trans (Nat.floor_le (Real.exp_pos _).le)

theorem card_fourierFrequencySet (t : ℝ) :
    ((fourierFrequencySet t).card : ℝ) ≤ Real.exp (4 * t / 10000) := by
  simp only [fourierFrequencySet, Nat.card_Icc, Nat.add_sub_cancel]
  convert Nat.floor_le (Real.exp_pos (t / 2500)).le using 1
  congr 1
  ring

/-- Normalized finite-sum form of the proved random-product second moment. -/
theorem sampledFourierMean_second_moment
    (S : ℝ) (hS : 3 ≤ S) (P : Finset ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hinterval : ∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101)
    (hsize : S ^ 99 ≤ (P.card : ℝ)) (u l : ℕ) (hu : 0 < u)
    (hV : 100000 * Real.log S ≤ Real.log (u : ℝ))
    (hVS : Real.log (u : ℝ) ≤ S) (hl : 0 < l)
    (hlbound : (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200)) :
    (∑ p : (Fin (blockLength S) × Bool) → P, ‖sampledFourierMean p u l‖ ^ 2) /
      Fintype.card ((Fin (blockLength S) × Bool) → P) ≤
        Real.exp (-min (blockLength S : ℝ) (Real.log (u : ℝ)) / 100) := by
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  simpa only [sampledFourierMean_eq, Fintype.expect_eq_sum_div_card] using
    sampled_product_second_moment_log_bound S hS P hprime hinterval hsize u l
      hV hVS hl hlbound

theorem modulus_pos_of_random_cutoff {S : ℝ} (hS : 3 ≤ S) {u : ℕ}
    (hV : 100000 * Real.log S ≤ Real.log (u : ℝ)) : 0 < u := by
  by_contra hu
  have hu0 : u = 0 := by omega
  have hlog : 0 < Real.log S := Real.log_pos (by linarith)
  simp only [hu0, Nat.cast_zero, Real.log_zero] at hV
  linarith

/-- One common collection of a thousand actual prime-sample blocks.  All
second-moment and frequency-union premises are discharged; only prime-pool,
finite-level size, and the explicit modulus-range hypotheses remain. -/
theorem exists_common_sampled_fourier :
    ∃ N : ℕ, ∀ (S : ℝ), 3 ≤ S → ∀ (P : Finset ℕ),
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
      S ^ 99 ≤ (P.card : ℝ) →
      ∀ (J : Type) (tests : Finset J) (level : J → Finset ℕ) (X : J → ℝ)
        (terminal : Finset ℕ),
      500000 ≤ (blockLength S : ℝ) →
      (tests.card : ℝ) ≤ (blockLength S : ℝ) →
      (∀ j ∈ tests, 0 < X j) →
      (∀ j ∈ tests, ((level j).card : ℝ) ≤ X j) →
      (∀ j ∈ tests, ∀ u ∈ level j,
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧
        Real.log (u : ℝ) ≤ S ∧
        (9999 / 10000 : ℝ) * (blockLength S : ℝ) ≤ Real.log (u : ℝ)) →
      (∀ u ∈ terminal, N ≤ u) →
      (∀ u ∈ terminal, 100000 * Real.log S ≤ Real.log (u : ℝ) ∧
        Real.log (u : ℝ) ≤ (blockLength S : ℝ)) →
      ∃ f : Fin 1000 → ((Fin (blockLength S) × Bool) → P),
        (∀ j ∈ tests,
          (((level j).filter (fun u => ∃ l ∈ fourierFrequencySet (blockLength S : ℝ),
            Real.exp (-3 * (blockLength S : ℝ) / 10000) <
              ‖sampledFourierMean (f 0) u l‖)).card : ℝ) ≤
                X j * Real.exp (-(blockLength S : ℝ) / 1000)) ∧
        ∀ u ∈ terminal, ∃ i : Fin 1000,
          ∀ l ∈ fourierFrequencySet (Real.log (u : ℝ)),
            ‖sampledFourierMean (f i) u l‖ ≤
              Real.exp (-3 * Real.log (u : ℝ) / 10000) := by
  classical
  obtain ⟨N, hN⟩ := FourierCommonRealization.exists_common_fourier_realization
  refine ⟨N, ?_⟩
  intro S hS P hprime hinterval hsize J tests level X terminal
    hm htests hX hlevels hmiddle hterminal htrange
  have hSpos : 0 < S := by linarith
  have hcard : 0 < (P.card : ℝ) := (pow_pos hSpos 99).trans_le hsize
  have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcard)
  let : Nonempty P := hP.to_subtype
  have hm0 : (0 : ℝ) ≤ blockLength S := Nat.cast_nonneg _
  apply hN ((Fin (blockLength S) × Bool) → P) J tests level X (blockLength S : ℝ)
    (fourierFrequencySet (blockLength S : ℝ))
    (fun u => fourierFrequencySet (Real.log (u : ℝ)))
    (fun p u l => sampledFourierMean p u l)
    (fun u => min (blockLength S : ℝ) (Real.log (u : ℝ))) terminal
    hm htests hX hlevels (card_fourierFrequencySet _)
  · intro j hj u hu
    exact le_min (by nlinarith) (hmiddle j hj u hu).2.2
  · intro j hj u hu l hl
    obtain ⟨hV, hVS, hVm⟩ := hmiddle j hj u hu
    obtain ⟨hl0, hlbound⟩ := mem_fourierFrequencySet hl
    exact sampledFourierMean_second_moment S hS P hprime hinterval hsize u l
      (modulus_pos_of_random_cutoff hS hV) hV hVS hl0
      (hlbound.trans (middle_frequency_cutoff hm0 hVm))
  · exact hterminal
  · intro u hu
    exact card_fourierFrequencySet _
  · intro u hu l hl
    obtain ⟨hV, hVm⟩ := htrange u hu
    have hu0 := modulus_pos_of_random_cutoff hS hV
    obtain ⟨hl0, hlbound⟩ := mem_fourierFrequencySet hl
    have hmin : min (blockLength S : ℝ) (Real.log (u : ℝ)) = Real.log (u : ℝ) :=
      min_eq_right hVm
    have hlog : 0 ≤ Real.log (u : ℝ) := Real.log_nonneg (by exact_mod_cast hu0)
    have hfreq : (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200) := by
      rw [hmin]
      exact hlbound.trans (Real.exp_le_exp.mpr (by linarith))
    have htop : Real.log (u : ℝ) ≤ S := hVm.trans
      (blockLength_le_self (Real.exp_one_lt_three.le.trans hS))
    simpa only [hmin] using sampledFourierMean_second_moment S hS P hprime
      hinterval hsize u l hu0 hV htop hl0 hfreq

end Problem337.RandomProducts

end

end OAI

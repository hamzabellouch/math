import OAI.NumberTheory.EgyptianFractions.RandomCommonRealization
import OAI.NumberTheory.EgyptianFractions.CyclicCeilingCount
import OAI.NumberTheory.EgyptianFractions.FejerExponentialBudget
import OAI.NumberTheory.EgyptianFractions.CeilResidue

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RandomProducts

/-- The least nonnegative remainder used by numerator descent, for an actual
labelled prime sample and an actual Boolean choice. -/
def sampledRemainder {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (I : Fin m → Bool) : ℕ :=
  u * ⌈(sampledProduct p I : ℚ) / (u : ℚ)⌉₊ - sampledProduct p I

/-- The exact, normalized random Fourier bound gives the half-mass
small-remainder bound. Indexed repeated products are retained. -/
theorem sampled_remainder_count_of_fourier {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (hu : 0 < u) (w : ℝ)
    (hw : 10000 * Real.log 65536 ≤ w)
    (hfourier : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (4 * w / 10000)⌋₊ →
      ‖sampledMean p u l‖ ≤ Real.exp (-3 * w / 10000)) :
    (Real.exp (-w / 10000) / 2) * (2 : ℝ) ^ m ≤
      ((Finset.univ.filter (fun I : Fin m → Bool =>
        (sampledRemainder p u I : ℝ) < Real.exp (-w / 10000) * u)).card : ℝ) := by
  classical
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  have hsmall : Real.exp (-w / 10000) ≤ 1 / 65536 := by
    calc
      Real.exp (-w / 10000) ≤ Real.exp (-Real.log 65536) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hcube : Real.exp (-w / 10000) ^ 3 = Real.exp (-3 * w / 10000) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hfourth : 1 / Real.exp (-w / 10000) ^ 4 = Real.exp (4 * w / 10000) := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1
    norm_num
    ring
  have h := ceiling_remainder_count_of_character_expect_automatic
    (sampledProduct p) (Real.exp (-w / 10000)) (Real.exp_pos _) hsmall
    (fun l hl hlH => by
      rw [hfourth] at hlH
      rw [hcube]
      simpa only [sampledMean_eq, sampledPhase, Nat.cast_mul] using hfourier l hl hlH)
  convert h using 1 <;> simp [sampledRemainder]
  congr 1

/-- Every Fourier-good terminal modulus has an actual Boolean product with
remainder smaller than the required power of that modulus. -/
theorem exists_sampled_terminal_remainder {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (hu : 0 < u)
    (hw : 10000 * Real.log 65536 ≤ Real.log (u : ℝ))
    (hfourier : ∀ l : ℕ, 1 ≤ l →
      l ≤ ⌊Real.exp (4 * Real.log (u : ℝ) / 10000)⌋₊ →
      ‖sampledMean p u l‖ ≤ Real.exp (-3 * Real.log (u : ℝ) / 10000)) :
    ∃ I : Fin m → Bool,
      (sampledRemainder p u I : ℝ) < (u : ℝ) ^ (9999 / 10000 : ℝ) := by
  classical
  have h := sampled_remainder_count_of_fourier p u hu (Real.log (u : ℝ)) hw hfourier
  have hc : 0 < (Finset.univ.filter (fun I : Fin m → Bool =>
      (sampledRemainder p u I : ℝ) <
        Real.exp (-Real.log (u : ℝ) / 10000) * u)).card := by
    have hpos : (0 : ℝ) < (Real.exp (-Real.log (u : ℝ) / 10000) / 2) * (2 : ℝ) ^ m := by positivity
    exact_mod_cast hpos.trans_le h
  obtain ⟨I, hI⟩ := Finset.card_pos.mp hc
  refine ⟨I, ?_⟩
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hpower : Real.exp (-Real.log (u : ℝ) / 10000) * u =
      (u : ℝ) ^ (9999 / 10000 : ℝ) := by
    conv_lhs => rhs; rw [← Real.exp_log huR]
    rw [← Real.exp_add, Real.rpow_def_of_pos huR]
    congr 1
    ring
  simpa only [hpower] using (Finset.mem_filter.mp hI).2


/-- The finite Fourier frequency window used at every scale. -/
def residueFrequencies (w : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌊Real.exp (4 * w / 10000)⌋₊

/-- A common choice of actual prime samples supplies the middle-level
small-remainder counts and covers every prescribed terminal numerator.
All hypotheses are explicit finite size/range conditions. -/
theorem exists_common_sampled_residue_realization :
    ∃ N : ℕ, ∀ (S : ℝ) (P : Finset ℕ) (J : Type)
      (tests : Finset J) (level : J → Finset ℕ) (X : J → ℝ)
      (terminal : Finset ℕ),
      3 ≤ S →
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
      S ^ 99 ≤ (P.card : ℝ) →
      500000 ≤ (blockLength S : ℝ) →
      10000 * Real.log 65536 ≤ (blockLength S : ℝ) →
      (tests.card : ℝ) ≤ (blockLength S : ℝ) →
      (∀ j ∈ tests, 0 < X j) →
      (∀ j ∈ tests, ((level j).card : ℝ) ≤ X j) →
      (∀ j ∈ tests, ∀ u ∈ level j, 0 < u ∧ (u : ℝ) ≤ X j ∧
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ S ∧
        (9999 / 10000 : ℝ) * (blockLength S : ℝ) ≤ Real.log (u : ℝ)) →
      (∀ u ∈ terminal, max N 1 ≤ u ∧
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧
        Real.log (u : ℝ) ≤ min (blockLength S : ℝ) S ∧
        10000 * Real.log 65536 ≤ Real.log (u : ℝ)) →
      ∃ (f : Fin 1000 → ((Fin (blockLength S) × Bool) → P))
        (exceptional : J → Finset ℕ),
        (∀ j ∈ tests, exceptional j ⊆ level j ∧
          ((exceptional j).card : ℝ) ≤ X j * Real.exp (-(blockLength S : ℝ) / 1000) ∧
          ∀ u ∈ level j, u ∉ exceptional j →
            (Real.exp (-(blockLength S : ℝ) / 10000) / 2) *
                (2 : ℝ) ^ blockLength S ≤
              ((Finset.univ.filter (fun I : Fin (blockLength S) → Bool =>
                (sampledRemainder (f 0) u I : ℝ) ≤
                  Real.exp (-(blockLength S : ℝ) / 10000) * X j)).card : ℝ)) ∧
        ∀ u ∈ terminal, ∃ i : Fin 1000, ∃ I : Fin (blockLength S) → Bool,
          (sampledRemainder (f i) u I : ℝ) < (u : ℝ) ^ (9999 / 10000 : ℝ) := by
  classical
  obtain ⟨N, hN⟩ := exists_common_sampled_realization
  refine ⟨N, ?_⟩
  intro S P J tests level X terminal hS hp hi hs hm hsmallm ht hX hlevel hmid hterminal
  have hfreqcard (w : ℝ) : ((residueFrequencies w).card : ℝ) ≤
      Real.exp (4 * w / 10000) := by
    simpa [residueFrequencies] using Nat.floor_le (Real.exp_pos (4 * w / 10000)).le
  have hfreqmem {w : ℝ} {l : ℕ} (hl : l ∈ residueFrequencies w) :
      0 < l ∧ (l : ℝ) ≤ Real.exp (4 * w / 10000) := by
    obtain ⟨hl1, hlH⟩ := Finset.mem_Icc.mp hl
    exact ⟨hl1, (Nat.cast_le.mpr hlH).trans (Nat.floor_le (Real.exp_pos _).le)⟩
  have hmiddlefreq : ∀ j ∈ tests, ∀ u ∈ level j,
      ∀ l ∈ residueFrequencies (blockLength S : ℝ), 0 < l ∧
        (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200) := by
    intro j hj u hu l hl
    obtain ⟨hl0, hlbound⟩ := hfreqmem hl
    refine ⟨hl0, hlbound.trans (Real.exp_le_exp.mpr ?_)⟩
    have hmin : (9999 / 10000 : ℝ) * (blockLength S : ℝ) ≤
        min (blockLength S : ℝ) (Real.log (u : ℝ)) :=
      le_min (by have := Nat.cast_nonneg (blockLength S) (α := ℝ); nlinarith) (hmid j hj u hu).2.2.2.2
    linarith
  have hterminalfreq : ∀ u ∈ terminal,
      ∀ l ∈ residueFrequencies (Real.log (u : ℝ)), 0 < l ∧
        (l : ℝ) ≤ Real.exp (Real.log (u : ℝ) / 200) := by
    intro u hu l hl
    obtain ⟨hl0, hlbound⟩ := hfreqmem hl
    refine ⟨hl0, hlbound.trans (Real.exp_le_exp.mpr ?_)⟩
    have hu1 : 1 ≤ u := (le_max_right N 1).trans (hterminal u hu).1
    have hlog : 0 ≤ Real.log (u : ℝ) := Real.log_nonneg (by exact_mod_cast hu1)
    linarith
  obtain ⟨f, hmiddle, hterm⟩ := hN S P J tests level X
    (residueFrequencies (blockLength S : ℝ))
    (fun u => residueFrequencies (Real.log (u : ℝ))) terminal
    hS hp hi hs hm ht hX hlevel (hfreqcard _)
    (fun j hj u hu => ⟨(hmid j hj u hu).1, (hmid j hj u hu).2.2⟩)
    hmiddlefreq
    (fun u hu => ⟨(hterminal u hu).1, (hterminal u hu).2.1,
      (hterminal u hu).2.2.1⟩)
    (fun u _ => hfreqcard _) hterminalfreq
  let exceptional : J → Finset ℕ := fun j => (level j).filter (fun u =>
    ∃ l ∈ residueFrequencies (blockLength S : ℝ),
      Real.exp (-3 * (blockLength S : ℝ) / 10000) < ‖sampledMean (f 0) u l‖)
  refine ⟨f, exceptional, ?_, ?_⟩
  · intro j hj
    refine ⟨Finset.filter_subset _ _, hmiddle j hj, ?_⟩
    intro u hu hnot
    have hgood : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (4 * (blockLength S : ℝ) / 10000)⌋₊ →
        ‖sampledMean (f 0) u l‖ ≤ Real.exp (-3 * (blockLength S : ℝ) / 10000) := by
      intro l hl hlH
      by_contra hbad
      apply hnot
      exact Finset.mem_filter.mpr ⟨hu, l, Finset.mem_Icc.mpr ⟨hl, hlH⟩, lt_of_not_ge hbad⟩
    have hcount := sampled_remainder_count_of_fourier (f 0) u (hmid j hj u hu).1
      (blockLength S : ℝ) hsmallm hgood
    apply hcount.trans
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro I hI
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact (Finset.mem_filter.mp hI).2.le.trans
      (mul_le_mul_of_nonneg_left (hmid j hj u hu).2.1 (Real.exp_pos _).le)
  · intro u hu
    obtain ⟨i, hi⟩ := hterm u hu
    have hu0 : 0 < u := by have := (le_max_right N 1).trans (hterminal u hu).1; omega
    obtain ⟨I, hI⟩ := exists_sampled_terminal_remainder (f i) u hu0
      (hterminal u hu).2.2.2 (fun l hl hlH => hi l (Finset.mem_Icc.mpr ⟨hl, hlH⟩))
    exact ⟨i, I, hI⟩

/-- Rational and real ceiling remainder formulas agree exactly. -/
theorem sampledRemainder_eq_real_ceil {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (hu : 0 < u) (I : Fin m → Bool) :
    sampledRemainder p u I =
      u * ⌈(sampledProduct p I : ℝ) / u⌉₊ - sampledProduct p I := by
  let : NeZero u := ⟨Nat.ne_of_gt hu⟩
  unfold sampledRemainder
  rw [ceiling_remainder_eq_neg_cast_val,
    natural_ceil_residue_eq_neg_zmod_val u (sampledProduct p I) hu]

/-- A sampled rational-ceiling remainder has exactly the same normalized
fractional-part interpretation as the real-ceiling construction. -/
theorem sampledRemainder_lt_iff_fract {m : ℕ} {P : Finset ℕ}
    (p : (Fin m × Bool) → P) (u : ℕ) (hu : 0 < u)
    (I : Fin m → Bool) (δ : ℝ) :
    (sampledRemainder p u I : ℝ) < δ * u ↔
      Int.fract (-(sampledProduct p I : ℝ) / u) < δ := by
  have hrem := sampledRemainder_eq_real_ceil p u hu I
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  rw [← natural_ceil_residue_div_eq_fract_neg u (sampledProduct p I) hu, ← hrem]
  exact (div_lt_iff₀ huR).symm

/-- A common choice of actual prime samples supplies the middle-level
small-remainder counts and covers every prescribed terminal numerator.
All hypotheses are explicit finite size/range conditions. -/
theorem exists_common_sampled_residue_realization_strict :
    ∃ N : ℕ, ∀ (S : ℝ) (P : Finset ℕ) (J : Type)
      (tests : Finset J) (level : J → Finset ℕ) (X : J → ℝ)
      (terminal : Finset ℕ),
      3 ≤ S →
      (∀ p ∈ P, Nat.Prime p) →
      (∀ p ∈ P, S ^ 100 ≤ (p : ℝ) ∧ (p : ℝ) ≤ S ^ 101) →
      S ^ 99 ≤ (P.card : ℝ) →
      500000 ≤ (blockLength S : ℝ) →
      10000 * Real.log 65536 ≤ (blockLength S : ℝ) →
      (tests.card : ℝ) ≤ (blockLength S : ℝ) →
      (∀ j ∈ tests, 0 < X j) →
      (∀ j ∈ tests, ((level j).card : ℝ) ≤ X j) →
      (∀ j ∈ tests, ∀ u ∈ level j, 0 < u ∧ (u : ℝ) ≤ X j ∧
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧ Real.log (u : ℝ) ≤ S ∧
        (9999 / 10000 : ℝ) * (blockLength S : ℝ) ≤ Real.log (u : ℝ)) →
      (∀ u ∈ terminal, max N 1 ≤ u ∧
        100000 * Real.log S ≤ Real.log (u : ℝ) ∧
        Real.log (u : ℝ) ≤ min (blockLength S : ℝ) S ∧
        10000 * Real.log 65536 ≤ Real.log (u : ℝ)) →
      ∃ (f : Fin 1000 → ((Fin (blockLength S) × Bool) → P))
        (exceptional : J → Finset ℕ),
        (∀ j ∈ tests, exceptional j ⊆ level j ∧
          ((exceptional j).card : ℝ) ≤ X j * Real.exp (-(blockLength S : ℝ) / 1000) ∧
          ∀ u ∈ level j, u ∉ exceptional j →
            (Real.exp (-(blockLength S : ℝ) / 10000) / 2) *
                (2 : ℝ) ^ blockLength S ≤
              ((Finset.univ.filter (fun I : Fin (blockLength S) → Bool =>
                (sampledRemainder (f 0) u I : ℝ) <
                  Real.exp (-(blockLength S : ℝ) / 10000) * u)).card : ℝ)) ∧
        ∀ u ∈ terminal, ∃ i : Fin 1000, ∃ I : Fin (blockLength S) → Bool,
          (sampledRemainder (f i) u I : ℝ) < (u : ℝ) ^ (9999 / 10000 : ℝ) := by
  classical
  obtain ⟨N, hN⟩ := exists_common_sampled_realization
  refine ⟨N, ?_⟩
  intro S P J tests level X terminal hS hp hi hs hm hsmallm ht hX hlevel hmid hterminal
  have hfreqcard (w : ℝ) : ((residueFrequencies w).card : ℝ) ≤
      Real.exp (4 * w / 10000) := by
    simpa [residueFrequencies] using Nat.floor_le (Real.exp_pos (4 * w / 10000)).le
  have hfreqmem {w : ℝ} {l : ℕ} (hl : l ∈ residueFrequencies w) :
      0 < l ∧ (l : ℝ) ≤ Real.exp (4 * w / 10000) := by
    obtain ⟨hl1, hlH⟩ := Finset.mem_Icc.mp hl
    exact ⟨hl1, (Nat.cast_le.mpr hlH).trans (Nat.floor_le (Real.exp_pos _).le)⟩
  have hmiddlefreq : ∀ j ∈ tests, ∀ u ∈ level j,
      ∀ l ∈ residueFrequencies (blockLength S : ℝ), 0 < l ∧
        (l : ℝ) ≤ Real.exp (min (blockLength S : ℝ) (Real.log (u : ℝ)) / 200) := by
    intro j hj u hu l hl
    obtain ⟨hl0, hlbound⟩ := hfreqmem hl
    refine ⟨hl0, hlbound.trans (Real.exp_le_exp.mpr ?_)⟩
    have hmin : (9999 / 10000 : ℝ) * (blockLength S : ℝ) ≤
        min (blockLength S : ℝ) (Real.log (u : ℝ)) :=
      le_min (by have := Nat.cast_nonneg (blockLength S) (α := ℝ); nlinarith) (hmid j hj u hu).2.2.2.2
    linarith
  have hterminalfreq : ∀ u ∈ terminal,
      ∀ l ∈ residueFrequencies (Real.log (u : ℝ)), 0 < l ∧
        (l : ℝ) ≤ Real.exp (Real.log (u : ℝ) / 200) := by
    intro u hu l hl
    obtain ⟨hl0, hlbound⟩ := hfreqmem hl
    refine ⟨hl0, hlbound.trans (Real.exp_le_exp.mpr ?_)⟩
    have hu1 : 1 ≤ u := (le_max_right N 1).trans (hterminal u hu).1
    have hlog : 0 ≤ Real.log (u : ℝ) := Real.log_nonneg (by exact_mod_cast hu1)
    linarith
  obtain ⟨f, hmiddle, hterm⟩ := hN S P J tests level X
    (residueFrequencies (blockLength S : ℝ))
    (fun u => residueFrequencies (Real.log (u : ℝ))) terminal
    hS hp hi hs hm ht hX hlevel (hfreqcard _)
    (fun j hj u hu => ⟨(hmid j hj u hu).1, (hmid j hj u hu).2.2⟩)
    hmiddlefreq
    (fun u hu => ⟨(hterminal u hu).1, (hterminal u hu).2.1,
      (hterminal u hu).2.2.1⟩)
    (fun u _ => hfreqcard _) hterminalfreq
  let exceptional : J → Finset ℕ := fun j => (level j).filter (fun u =>
    ∃ l ∈ residueFrequencies (blockLength S : ℝ),
      Real.exp (-3 * (blockLength S : ℝ) / 10000) < ‖sampledMean (f 0) u l‖)
  refine ⟨f, exceptional, ?_, ?_⟩
  · intro j hj
    refine ⟨Finset.filter_subset _ _, hmiddle j hj, ?_⟩
    intro u hu hnot
    have hgood : ∀ l : ℕ, 1 ≤ l → l ≤ ⌊Real.exp (4 * (blockLength S : ℝ) / 10000)⌋₊ →
        ‖sampledMean (f 0) u l‖ ≤ Real.exp (-3 * (blockLength S : ℝ) / 10000) := by
      intro l hl hlH
      by_contra hbad
      apply hnot
      exact Finset.mem_filter.mpr ⟨hu, l, Finset.mem_Icc.mpr ⟨hl, hlH⟩, lt_of_not_ge hbad⟩
    have hcount := sampled_remainder_count_of_fourier (f 0) u (hmid j hj u hu).1
      (blockLength S : ℝ) hsmallm hgood
    exact hcount
  · intro u hu
    obtain ⟨i, hi⟩ := hterm u hu
    have hu0 : 0 < u := by have := (le_max_right N 1).trans (hterminal u hu).1; omega
    obtain ⟨I, hI⟩ := exists_sampled_terminal_remainder (f i) u hu0
      (hterminal u hu).2.2.2 (fun l hl hlH => hi l (Finset.mem_Icc.mpr ⟨hl, hlH⟩))
    exact ⟨i, I, hI⟩

end Problem337.RandomProducts

end

end OAI

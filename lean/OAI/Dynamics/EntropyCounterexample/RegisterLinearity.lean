import Mathlib

namespace OAI

noncomputable section

namespace Problem340
namespace Register

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def delayedCandidate (L : ℝ) (j : ℕ) (c : ℕ → E) (n : ℕ) : E :=
  L ^ ((n : ℤ) - (j : ℤ)) • ∑ i ∈ Finset.range n, c i

@[simp] theorem delayedCandidate_zero (L : ℝ) (j : ℕ) (c : ℕ → E) :
    delayedCandidate L j c 0 = 0 := by
  simp [delayedCandidate]

@[simp] theorem delayedCandidate_readout (L : ℝ) (j : ℕ) (c : ℕ → E) :
    delayedCandidate L j c j = ∑ i ∈ Finset.range j, c i := by
  simp [delayedCandidate]

theorem delayedCandidate_succ (L : ℝ) (hL : L ≠ 0) (j : ℕ)
    (c : ℕ → E) (n : ℕ) :
    delayedCandidate L j c (n + 1) =
      L • delayedCandidate L j c n +
        L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n := by
  have hp : L ^ (((n + 1 : ℕ) : ℤ) - (j : ℤ)) =
      L * L ^ ((n : ℤ) - (j : ℤ)) := by
    rw [show (((n + 1 : ℕ) : ℤ) - (j : ℤ)) =
      1 + ((n : ℤ) - (j : ℤ)) by omega, zpow_add₀ hL]
    simp
  unfold delayedCandidate
  rw [Finset.sum_range_succ, smul_add, hp, mul_smul]
  congr 1
  rw [← hp]
  congr 2

theorem norm_delayedCandidate_le (L : ℝ) (hL : 1 ≤ L) (j : ℕ)
    (c : ℕ → E) {R : ℝ}
    (hc : (∑ i ∈ Finset.range j, ‖c i‖) ≤ R)
    {n : ℕ} (hn : n ≤ j) :
    ‖delayedCandidate L j c n‖ ≤ R := by
  have hpow_nonneg : 0 ≤ L ^ ((n : ℤ) - (j : ℤ)) :=
    zpow_nonneg (by linarith) _
  have hpow_le : L ^ ((n : ℤ) - (j : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ hL (by omega)
  have hsum : (∑ i ∈ Finset.range n, ‖c i‖) ≤
      ∑ i ∈ Finset.range j, ‖c i‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
      (fun i _ _ => norm_nonneg (c i))
  calc
    ‖delayedCandidate L j c n‖ =
        L ^ ((n : ℤ) - (j : ℤ)) * ‖∑ i ∈ Finset.range n, c i‖ := by
      rw [delayedCandidate, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hpow_nonneg]
    _ ≤ 1 * ‖∑ i ∈ Finset.range n, c i‖ :=
      mul_le_mul_of_nonneg_right hpow_le (norm_nonneg _)
    _ = ‖∑ i ∈ Finset.range n, c i‖ := one_mul _
    _ ≤ ∑ i ∈ Finset.range n, ‖c i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range j, ‖c i‖ := hsum
    _ ≤ R := hc

theorem delayed_register_linearity (L : ℝ) (hL : 1 ≤ L) (j : ℕ)
    (c : ℕ → E) (S : E → E) (v : ℕ → E)
    (hc : (∑ i ∈ Finset.range j, ‖c i‖) ≤ (1 / 2 : ℝ))
    (hS : ∀ x : E, ‖x‖ ≤ 1 → S x = x)
    (hv0 : v 0 = 0)
    (hstep : ∀ n < j, v (n + 1) = L • S (v n) +
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n) :
    (∀ n ≤ j, v n = delayedCandidate L j c n ∧ ‖v n‖ ≤ (1 / 2 : ℝ)) ∧
      v j = ∑ i ∈ Finset.range j, c i := by
  have hL0 : L ≠ 0 := by linarith
  have hmain : ∀ n ≤ j, v n = delayedCandidate L j c n ∧
      ‖v n‖ ≤ (1 / 2 : ℝ) := by
    intro n
    induction n with
    | zero =>
        intro _
        simp [hv0]
    | succ n ih =>
        intro hn
        have hn' : n ≤ j := by omega
        obtain ⟨heq, hnorm⟩ := ih hn'
        have hnext : v (n + 1) = delayedCandidate L j c (n + 1) := by
          rw [hstep n (by omega), hS (v n) (by linarith), heq]
          exact (delayedCandidate_succ L hL0 j c n).symm
        refine ⟨hnext, ?_⟩
        rw [hnext]
        exact norm_delayedCandidate_le L hL j c hc hn
  refine ⟨hmain, ?_⟩
  simpa using (hmain j le_rfl).1

omit [NormedSpace ℝ E] in

theorem coefficient_norm_sum_le_half {ι : Type*} (I : Finset ι) (c : ι → E)
    (hcard : I.card ≤ 5) (hc : ∀ i ∈ I, ‖c i‖ ≤ (1 / 10 : ℝ)) :
    (∑ i ∈ I, ‖c i‖) ≤ (1 / 2 : ℝ) := by
  calc
    (∑ i ∈ I, ‖c i‖) ≤ I.card • (1 / 10 : ℝ) :=
      Finset.sum_le_card_nsmul I (fun i => ‖c i‖) _ hc
    _ ≤ (1 / 2 : ℝ) := by
      simp only [nsmul_eq_mul]
      have : (I.card : ℝ) ≤ 5 := by exact_mod_cast hcard
      linarith

def finiteSignals (I : Finset ℕ) (c : ℕ → E) (n : ℕ) : E :=
  if n ∈ I then c n else 0

omit [NormedSpace ℝ E] in

theorem sum_finiteSignals (I : Finset ℕ) (c : ℕ → E) (j : ℕ)
    (hI : I ⊆ Finset.range j) :
    (∑ i ∈ Finset.range j, finiteSignals I c i) = ∑ i ∈ I, c i := by
  calc
    (∑ i ∈ Finset.range j, finiteSignals I c i) =
        ∑ i ∈ I, finiteSignals I c i :=
      (Finset.sum_subset hI (fun i _ hi => by simp [finiteSignals, hi])).symm
    _ = ∑ i ∈ I, c i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [finiteSignals, hi]

omit [NormedSpace ℝ E] in

theorem norm_sum_finiteSignals_le_half (I : Finset ℕ) (c : ℕ → E) (j : ℕ)
    (hI : I ⊆ Finset.range j) (hcard : I.card ≤ 5)
    (hc : ∀ i ∈ I, ‖c i‖ ≤ (1 / 10 : ℝ)) :
    (∑ i ∈ Finset.range j, ‖finiteSignals I c i‖) ≤ (1 / 2 : ℝ) := by
  have heq : (∑ i ∈ Finset.range j, ‖finiteSignals I c i‖) =
      ∑ i ∈ I, ‖c i‖ := by
    calc
      (∑ i ∈ Finset.range j, ‖finiteSignals I c i‖) =
          ∑ i ∈ Finset.range j, finiteSignals I (fun k => ‖c k‖) i := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [finiteSignals]
        split_ifs <;> simp
      _ = ∑ i ∈ I, ‖c i‖ := sum_finiteSignals I (fun i => ‖c i‖) j hI
  rw [heq]
  exact coefficient_norm_sum_le_half I c hcard hc

theorem delayed_register_of_finite_signals
    (L : ℝ) (hL : 1 ≤ L) (j : ℕ) (I : Finset ℕ) (c : ℕ → E)
    (S : E → E) (v : ℕ → E)
    (hI : I ⊆ Finset.range j) (hcard : I.card ≤ 5)
    (hc : ∀ i ∈ I, ‖c i‖ ≤ (1 / 10 : ℝ))
    (hS : ∀ x : E, ‖x‖ ≤ 1 → S x = x)
    (hv0 : v 0 = 0)
    (hstep : ∀ n < j, v (n + 1) = L • S (v n) +
      L ^ ((n : ℤ) + 1 - (j : ℤ)) • finiteSignals I c n) :
    (∀ n ≤ j,
      v n = delayedCandidate L j (finiteSignals I c) n ∧
      ‖v n‖ ≤ (1 / 2 : ℝ)) ∧
      v j = ∑ i ∈ I, c i := by
  obtain ⟨hpartial, hfinal⟩ := delayed_register_linearity L hL j
    (finiteSignals I c) S v
    (norm_sum_finiteSignals_le_half I c j hI hcard hc) hS hv0 hstep
  refine ⟨hpartial, ?_⟩
  rw [hfinal, sum_finiteSignals I c j hI]

theorem norm_scheduledCoefficient_le {β α χ : ℝ} {phase : E}
    (hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hχ : χ ∈ Set.Icc (0 : ℝ) 1)
    (hphase : ‖phase‖ ≤ 1) :
    ‖(β / 10 * α * χ) • phase‖ ≤ (1 / 10 : ℝ) := by
  have hcoeff0 : 0 ≤ β / 10 * α * χ :=
    mul_nonneg (mul_nonneg (div_nonneg hβ.1 (by norm_num)) hα.1) hχ.1
  have hcoeff : β / 10 * α * χ ≤ (1 / 10 : ℝ) := by
    have hprod : α * χ ≤ 1 := (mul_le_of_le_one_left hχ.1 hα.2).trans hχ.2
    calc
      β / 10 * α * χ = (β * (α * χ)) / 10 := by ring
      _ ≤ 1 / 10 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact (mul_le_of_le_one_left (mul_nonneg hα.1 hχ.1) hβ.2).trans hprod
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoeff0]
  exact (mul_le_mul_of_nonneg_left hphase hcoeff0).trans (by simpa using hcoeff)

end Register
end Problem340

end

end OAI

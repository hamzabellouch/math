import OAI.NumberTheory.Ostmann.Quadratic.CommonCenterCutoffs

namespace OAI

/-! # A common rational center from the original positive lift family -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

/-- The scalar hypotheses of the finite common-center theorem have now been
discharged at the original scales. The input probability is supplied by
`eventual_original_lift_probability`. -/
theorem eventual_original_commonCenter (Cpop : ℝ) (hCpop : 500 ≤ Cpop) :
    ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (t : ℕ → ℤ) (k : ℕ) (K X : ℝ),
      ∀ hP : ∀ p ∈ P, p.Prime, (∀ p ∈ P, Real.exp T ≤ (p : ℝ)) →
      Real.exp T ≤ Cpop * T * P.card → (P.card : ℝ) ≤ Real.exp (T + 1) →
      10 ≤ k + 1 → 2 * (k + 1) ^ 2 ≤ P.card →
      ((k + 1 : ℕ) : ℝ) ≤ 2 * T ^ (3 / 5 : ℝ) →
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ K → K ≤ T →
      1 ≤ X → X ≤ Real.exp (((k + 1 - 10 : ℕ) : ℝ) * T) →
      Real.exp (-K / 5) ≤ (Fintype.card (Fin (k + 1) ↪ P) : ℝ)⁻¹ *
        (tupleLiftFamily P (k + 1) ⌈Real.exp (13 * T / 100)⌉₊
          ⌈X * Real.exp (13 * T / 100)⌉₊ t).card →
      ∃ a ∈ Finset.Icc 1 ⌈Real.exp (13 * T / 100)⌉₊,
        ∃ n ∈ Finset.Ico (-(⌈X * Real.exp (13 * T / 100)⌉₊ : ℤ))
          (⌈X * Real.exp (13 * T / 100)⌉₊ + 1), ∃ h : ℤ, ∃ m : ℕ,
          0 < m ∧ m ≤ ⌈Real.exp (13 * T / 100)⌉₊ ∧ h.natAbs.Coprime m ∧ |h| ≤ |n| ∧
          Real.exp (3 * T / 5) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
          (P.card : ℝ) * Real.exp (-T / k) ≤ ((matchingPrimes P a t n).card : ℝ) ∧
          ∀ (p : ℕ) (hp : p ∈ matchingPrimes P a t n),
            let _ : Fact p.Prime := ⟨hP p (Finset.mem_filter.mp hp).1⟩
            (t p : ZMod p) = (h : ZMod p) / (m : ZMod p) := by
  filter_upwards [eventual_commonCenter_discard_budget Cpop hCpop, eventual_commonCenter_small_budget,
    eventual_two_pow_moment_budget, eventually_ge_atTop (30 : ℝ)] with T hd hs hp hT
  intro P t k K X hP hmin hpop hPU hk hsize hkU hK hKT hX hXU hprob
  let Amax := ⌈Real.exp (13 * T / 100)⌉₊
  let H := ⌈X * Real.exp (13 * T / 100)⌉₊
  let Z := ⌊Real.exp T⌋₊
  obtain ⟨hApos, hAU, hHU, hZpos, hZlo⟩ := commonCenter_original_cutoffs T X (k + 1)
    (by linarith) hX hXU
  have hpow : (2 : ℝ) ^ (k + 1) ≤ Real.exp (T / 10) :=
    (hp (k + 1) K (by omega) hkU hK).trans (Real.exp_le_exp.mpr (by linarith))
  have hdiscard := hd P.card (k + 1) H Z Amax K hk hKT hApos hpop hpow hZlo hHU hAU
  have hlog (p : ℕ) (hpp : p ∈ P) : T ≤ Real.log (p : ℝ) :=
    (Real.le_log_iff_exp_le (by exact_mod_cast (hP p hpp).pos)).mpr (hmin p hpp)
  have hfloor (p : ℕ) (hpp : p ∈ P) : Z ≤ p := by
    have hh : (Z : ℝ) ≤ p := (Nat.floor_le (Real.exp_nonneg T)).trans (hmin p hpp)
    exact_mod_cast hh
  obtain ⟨a, ha, n, hn, h, m, hm, hma, hcop, hbound, hlarge, hmoment, hcenters⟩ :=
    exists_commonCenter_of_lift_probability P t k 10 (k + 1) H Z Amax hk
      (Real.exp (3 * T / 5)) T (Real.exp (-K / 5)) (Real.exp_pos _) (by linarith)
      (Real.exp_pos _) hZpos hApos hP
      (fun p hpp => commonCenter_denominator_lt_primes T Amax p (by linarith) hAU (hmin p hpp))
      hfloor hlog (commonCenter_log_budget T (k + 1) H (by linarith) hk hHU)
      (hs P.card (k + 1) hkU hPU) hsize hprob hdiscard
  have hJ : (0 : ℝ) < P.card := by
    have hh : 0 < P.card := by nlinarith
    exact_mod_cast hh
  refine ⟨a, ha, n, hn, h, m, hm, hma, hcop, hbound, hlarge, ?_, hcenters⟩
  exact commonCenter_relative_size T K P.card (matchingPrimes P a t n).card Amax k
    hT hKT hJ (Nat.cast_nonneg _) (by exact_mod_cast hApos) hAU (by omega) hmoment

end Ostmann

end OAI

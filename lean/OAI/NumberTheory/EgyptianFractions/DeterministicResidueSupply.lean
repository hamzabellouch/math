import OAI.NumberTheory.EgyptianFractions.DeterministicMean
import OAI.NumberTheory.EgyptianFractions.DeterministicMeanDecay
import OAI.NumberTheory.EgyptianFractions.HighResidueDistribution

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- Uniform positivity and localization cutoff for every admissible real
prime-product scale, not only the floor choice. -/
theorem eventually_high_residue_scale_window :
    ∀ᶠ S : ℝ in atTop, ∀ m : ℝ, S / (2 * Real.log S) ≤ m →
      0 ≤ m ∧ Real.exp (-m / 10000) ≤ 1 / 65536 := by
  have ht : Tendsto (fun S : ℝ => S / (2 * Real.log S)) atTop atTop := by
    convert ResidueLevels.tendsto_div_log.atTop_div_const
      (by norm_num : (0 : ℝ) < 2) using 1
    funext S
    ring
  have he : Tendsto
      (fun S : ℝ => Real.exp (-((S / (2 * Real.log S)) / 10000)))
      atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (ht.atTop_div_const (by norm_num))
  filter_upwards [ht.eventually (eventually_ge_atTop (0 : ℝ)),
    he.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 65536))] with S hS hsmall
  intro m hm
  refine ⟨hS.trans hm, ?_⟩
  apply le_trans _ hsmall.le
  apply Real.exp_le_exp.mpr
  linarith

/-- The two phase conventions agree exactly, including zero modulus where
both divisions use their usual totalized field convention. -/
theorem natural_product_phase_eq_differencing (l C t u : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (l * (C * t) : ℕ) / (u : ℂ)) =
      differencingPhase ((l : ℝ) * C * t / (u : ℝ)) := by
  unfold differencingPhase
  congr 1
  push_cast
  ring

/-- Unconditional deterministic high-level small-residue distribution.
The only hypotheses concern the explicit scale, factor, size and distinctness
of the list. Reciprocal cancellation, frequency moments, Markov selection and
sharp localization are all discharged by the imported checked theorems. -/
theorem deterministic_high_residue_distribution (D : ℝ) (hD : 255 ≤ D) :
    ∀ᶠ S : ℝ in atTop, ∀ (m X : ℝ) (C : ℕ),
      S / (2 * Real.log S) ≤ m → m ≤ S / Real.log S →
      Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
      Real.exp (D * S) ≤ (C : ℝ) → (C : ℝ) ≤ Real.exp (2 * D * S) →
      ∀ {ι : Type*} (T : Finset ι) (t : ι → ℕ),
        Set.InjOn t (T : Set ι) →
        Real.exp (Real.log 2 * m) ≤ (T.card : ℝ) →
        (∀ i ∈ T, (t i : ℝ) ≤ Real.exp (101 * S)) →
        ∃ E : Finset ℕ,
          E ⊆ Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊ ∧
          (E.card : ℝ) ≤ X * Real.exp (-m / 1000) ∧
          ∀ u ∈ Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊,
            u ∉ E →
            Real.exp (-m / 10000) * (T.card : ℝ) / 2 ≤
              ((T.filter (fun i => Int.fract (-((C * t i : ℕ) : ℝ) / u) <
                Real.exp (-m / 10000))).card : ℝ) := by
  obtain ⟨A, c, hA, hc, hmean⟩ := deterministic_mean_two_errors D hD
  have hlogtwo : (1 / 100 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  filter_upwards [hmean, ResidueLevels.eventually_exp_absorb_real_scale
      (a := 1 / 100) (b := Real.log 2) (c := c) (C := A) hlogtwo hc hA.le,
    eventually_high_residue_scale_window, eventually_ge_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with S hmean habs hscale hS hlog
  intro m X C hmlo hmhi hXlo hXhi hClo hChi ι T t ht hcard hsize
  have hX : 0 ≤ X := (Real.exp_pos S).le.trans hXlo
  have hmS : m ≤ S := by
    apply hmhi.trans
    apply (div_le_iff₀ (by linarith : 0 < Real.log S)).mpr
    nlinarith
  obtain ⟨hm, hsmall⟩ := hscale m hmlo
  have hbound := high_level_fractional_residues_finset T (fun i => C * t i)
    (Finset.Icc (⌊Real.exp (-m / 10000) * X⌋₊ + 1) ⌊X⌋₊) m X hm hX hsmall
    (by intro u hu; have := (Finset.mem_Icc.mp hu).1; omega) (by
      intro l hl hlH
      have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
      have hlup : (l : ℝ) ≤ Real.exp (m / 2500) :=
        (Nat.cast_le.mpr hlH).trans (Nat.floor_le (Real.exp_pos _).le)
      have hmoment := hmean m X C l hmS hXlo hXhi hClo hChi hlR hlup
        T t ht hcard hsize
      simp only [natural_product_phase_eq_differencing]
      apply hmoment.trans
      have ha := mul_le_mul_of_nonneg_left (habs m hmlo hmhi) hX
      simpa only [show -(1 / 100 : ℝ) * m = -m / 100 by ring] using ha)
  obtain ⟨E, hEU, hEc, hE⟩ := hbound
  refine ⟨E, hEU, hEc, ?_⟩
  intro u hu hgood
  simpa only [div_mul_eq_mul_div] using hE u hu hgood

end Problem337

end

end OAI

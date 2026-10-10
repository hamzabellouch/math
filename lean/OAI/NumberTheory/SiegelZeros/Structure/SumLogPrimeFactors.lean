import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.Characters.RealLogDerivConductorCompletedLDivisorTsum
import OAI.NumberTheory.SiegelZeros.Structure.CharacterEstimates

namespace OAI

namespace SiegelZeros
open scoped _root_.SiegelZeros

open scoped BigOperators Topology

open scoped BigOperators

namespace WeightedTorusJets

theorem sum_log_primeFactors_le (q : ℕ) :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hp : ∀ p ∈ q.primeFactors, 0 < (p : ℝ) := by
    intro p hp
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.pos
  rw [← Real.log_prod (fun p hp' => (hp p hp').ne')]
  apply Real.log_le_log (Finset.prod_pos hp)
  rw [← Nat.cast_prod]
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)

theorem sum_log_div_primeFactors_le (q : ℕ) :
    ∑ p ∈ q.primeFactors, Real.log p / p ≤ Real.log q := by
  refine (Finset.sum_le_sum fun p hp => ?_).trans (sum_log_primeFactors_le q)
  have hp1 : 1 ≤ (p : ℝ) := by
    exact_mod_cast (Nat.mem_primeFactors.mp hp).1.one_le
  exact div_le_self (Real.log_nonneg hp1) hp1

theorem sum_log_div_filter_dvd_le (q : ℕ) (hq : q ≠ 0) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s with p ∣ q, Real.log p / p ≤ Real.log q := by
  refine (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans
    (sum_log_div_primeFactors_le q)
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hps, hpq⟩
    exact Nat.mem_primeFactors.mpr ⟨hprime p hps, hpq, hq⟩
  · intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem sum_log_div_filter_le_cutoff (s : Finset ℕ) (H : ℕ) :
    ∑ p ∈ s with p ≤ H, Real.log p / p ≤
      ∑ p ∈ Finset.range (H + 1), Real.log p / p := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
  · intro p _ _
    exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

theorem prime_mass_partition_le {q H : ℕ} (hH : 2 ≤ H) (s : Finset ℕ)
    (c : ℕ → ℂ) (hprime : ∀ p ∈ s, p.Prime)
    (hclass : ∀ p ∈ s, c p = 1 ∨ p ∣ q ∨ c p = -1) :
    ∑ p ∈ s, Real.log p / p ≤
      (∑ p ∈ s with c p = 1, Real.log p / p) +
      (∑ p ∈ s with p ∣ q, Real.log p / p) +
      (∑ p ∈ s with p ≤ H, Real.log p / p) +
      ∑ p ∈ s with H < p ∧ ¬ p ∣ 2 * q ∧ c p = -1, Real.log p / p := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hn : 0 ≤ Real.log p / p := by
    apply div_nonneg (Real.log_nonneg _) (Nat.cast_nonneg _)
    exact_mod_cast (hprime p hp).one_lt.le
  by_cases hsmall : p ≤ H
  · simp only [hsmall, ite_true]
    split_ifs <;> linarith
  have hlarge : H < p := lt_of_not_ge hsmall
  rcases hclass p hp with hpos | hram | hneg
  · simp only [hpos, ite_true]
    split_ifs <;> linarith
  · simp only [hram, ite_true]
    split_ifs <;> linarith
  · by_cases hram : p ∣ q
    · simp only [hram, ite_true]
      split_ifs <;> linarith
    have htwo : ¬ p ∣ 2 := by
      intro hp2
      have := Nat.le_of_dvd (by decide : 0 < 2) hp2
      omega
    simp only [hsmall, hram, hneg, hlarge, (hprime p hp).not_dvd_mul htwo hram,
      ite_false, ite_true, and_self, not_false_eq_true]
    split_ifs <;> linarith

theorem good_mass_of_estimates {q H : ℕ} (hH : 2 ≤ H) (s : Finset ℕ)
    (c : ℕ → ℂ) (hprime : ∀ p ∈ s, p.Prime)
    (hclass : ∀ p ∈ s, c p = 1 ∨ p ∣ q ∨ c p = -1)
    {L ell E A B D CH : ℝ} (hell : 0 ≤ ell) (hE : 0 ≤ E)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htotal : L - D ≤ ∑ p ∈ s, Real.log p / p)
    (hpositive : (∑ p ∈ s with c p = 1, Real.log p / p) ≤ A * ell + B * E)
    (hramified : (∑ p ∈ s with p ∣ q, Real.log p / p) ≤ ell)
    (hsmall : (∑ p ∈ s with p ≤ H, Real.log p / p) ≤ CH) :
    L - (A + B + 1) * ell - (A + B + 1) * E - (D + CH) ≤
      ∑ p ∈ s with H < p ∧ ¬ p ∣ 2 * q ∧ c p = -1, Real.log p / p := by
  have hpartition := prime_mass_partition_le hH s c hprime hclass
  nlinarith [mul_nonneg hB hell, mul_nonneg hA hE]

section

theorem good_prime_mass_of_primebias {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
      ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
      (∀ a : ZMod q, (χ a).im = 0) → ∀ X δ : ℝ, 3 ≤ X → 0 ≤ δ →
      (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1, Real.log p / p) ≤
        A * Real.log q + B * (δ * (Real.log X) ^ 2 / Real.log q) →
      Real.log X - C * Real.log q - C * (δ * (Real.log X) ^ 2 / Real.log q) - CH ≤
        ∑ p ∈ Nat.primesLE ⌊X⌋₊ with
          H < p ∧ ¬ p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1, Real.log p / p := by
  classical
  obtain ⟨D, _, hD⟩ := Mertens.prime_log_div_bounded_error
  refine ⟨A + B + 1, by linarith, fun H hH =>
    ⟨D + ∑ p ∈ Finset.range (H + 1), Real.log p / p, ?_⟩⟩
  intro q _ hq χ hreal X δ hX hδ hbias
  have hprime : ∀ p ∈ Nat.primesLE ⌊X⌋₊, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primesLE hp
  have hquadratic := (RealCharacterAnalysis.real_values_iff_quadratic χ).mp hreal
  have hclass : ∀ p ∈ Nat.primesLE ⌊X⌋₊,
      χ ((p : ℕ) : ZMod q) = 1 ∨ p ∣ q ∨ χ ((p : ℕ) : ZMod q) = -1 := by
    intro p hp
    rcases hquadratic ((p : ℕ) : ZMod q) with hz | ho | hm
    · exact Or.inr (Or.inl ((RealCharacterAnalysis.apply_prime_eq_zero_iff χ
        (hprime p hp)).mp hz))
    · exact Or.inl ho
    · exact Or.inr (Or.inr hm)
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hE : 0 ≤ δ * (Real.log X) ^ 2 / Real.log q :=
    div_nonneg (mul_nonneg hδ (sq_nonneg _)) hlogq
  have htotal : Real.log X - D ≤
      ∑ p ∈ Nat.primesLE ⌊X⌋₊, Real.log p / p := by
    have := (abs_le.mp (hD X (by linarith))).1
    linarith
  exact good_mass_of_estimates hH (Nat.primesLE ⌊X⌋₊) (fun p => χ ((p : ℕ) : ZMod q))
    hprime hclass hlogq hE hA hB htotal hbias
    (sum_log_div_filter_dvd_le q (by omega) _ hprime)
    (sum_log_div_filter_le_cutoff _ H)

theorem source_analytic_lemma :
    ∃ C : ℝ, 0 < C ∧
      (∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
        ∀ X : ℝ, 3 ≤ X →
        (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1, Real.log p / p) ≤
          C * Real.log q + C * (((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q)) ∧
      (∀ H : ℕ, 2 ≤ H → ∃ CH : ℝ,
        ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
        ∀ X : ℝ, 3 ≤ X →
        Real.log X - C * Real.log q -
          C * (((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q) - CH ≤
          ∑ p ∈ Nat.primesLE ⌊X⌋₊ with
            H < p ∧ ¬ p ∣ 2 * q ∧ χ ((p : ℕ) : ZMod q) = -1, Real.log p / p) := by
  classical
  obtain ⟨K, hK, hupper⟩ := logDeriv_upper_of_completedL_lower
  let A := Real.exp 1 / 2 * K
  let B := Real.exp 1 / 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let Cb := A + B + 1
  have hCb : 0 < Cb := by dsimp [Cb]; linarith
  have hbias : ∀ (q : ℕ) [NeZero q], 3 ≤ q → ∀ χ : DirichletCharacter ℂ q,
      χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
      ∀ β : ℝ, 0 < β → β < 1 → DirichletCharacter.LFunction χ (β : ℂ) = 0 →
      ∀ X : ℝ, 3 ≤ X →
      (∑ p ∈ Nat.primesLE ⌊X⌋₊ with χ ((p : ℕ) : ZMod q) = 1, Real.log p / p) ≤
        Cb * Real.log q + Cb * (((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q) := by
    intro q _ hq χ hprim hχ hreal β hβ0 hβ1 hzero X hX
    have hs := primebias_sampling_point hX
    have hu := hupper q hq χ hχ (1 + 1 / Real.log X) β hs.1 hs.2
      (real_zero_le_conductorCompletedL_logDeriv χ hprim hχ
        ((RealCharacterAnalysis.real_values_iff_quadratic χ).mp hreal) hβ0 hzero hs.1)
    have hp := positive_prime_mass_of_logDeriv_upper χ (X := X) (β := β) (K := K) (by linarith) hβ1
      (by simpa only [logDeriv_apply, neg_div] using hu)
    have hell : 0 < Real.log q := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
    have hdelta : 0 ≤ (1 - β) * Real.log q := mul_nonneg (by linarith) hell.le
    have hE : 0 ≤ ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q :=
      div_nonneg (mul_nonneg hdelta (sq_nonneg _)) hell.le
    have heq : ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q =
        (1 - β) * (Real.log X) ^ 2 := by field_simp
    rw [← heq] at hp
    dsimp [A, B, Cb] at *
    nlinarith [mul_nonneg hB hell.le, mul_nonneg hA hE]
  obtain ⟨Cg, _, hgood⟩ := good_prime_mass_of_primebias hCb.le hCb.le
  refine ⟨max Cb Cg, hCb.trans_le (le_max_left _ _), ?_, ?_⟩
  · intro q _ hq χ hprim hχ hreal β hβ0 hβ1 hzero X hX
    have hp := hbias q hq χ hprim hχ hreal β hβ0 hβ1 hzero X hX
    have hell : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    have hE : 0 ≤ ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) hell) (sq_nonneg _)) hell
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_left Cb Cg)) hell,
      mul_nonneg (sub_nonneg.mpr (le_max_left Cb Cg)) hE]
  · intro H hH
    obtain ⟨CH, hCH⟩ := hgood H hH
    refine ⟨CH, ?_⟩
    intro q _ hq χ hprim hχ hreal β hβ0 hβ1 hzero X hX
    have hell : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    have hdelta : 0 ≤ (1 - β) * Real.log q := mul_nonneg (by linarith) hell
    have hE : 0 ≤ ((1 - β) * Real.log q) * (Real.log X) ^ 2 / Real.log q :=
      div_nonneg (mul_nonneg hdelta (sq_nonneg _)) hell
    have hg := hCH q hq χ hreal X ((1 - β) * Real.log q) hX hdelta
      (hbias q hq χ hprim hχ hreal β hβ0 hβ1 hzero X hX)
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_right Cb Cg)) hell,
      mul_nonneg (sub_nonneg.mpr (le_max_right Cb Cg)) hE]

open _root_.SiegelZeros.Complex.Hadamard

theorem source_hadamard_logDeriv_identity {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) {s : ℝ} (hs : 1 < s) :
    (-logDeriv (DirichletCharacter.LFunction χ) (s : ℂ)).re =
      Real.log ((q : ℝ) / Real.pi) / 2 +
        (logDeriv Complex.Gamma (((s + (1 - (χ (-1)).re) / 2) / 2 : ℝ) : ℂ)).re / 2 -
        ∑' p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ,
          (1 / ((s : ℂ) - divisorZeroIndex₀Val p)).re := by
  have hd := congrArg Complex.re
    (conductorCompletedL_logDeriv_decomposition χ hχ (s := (s : ℂ)) (by simpa using hs))
  rw [Complex.add_re] at hd
  have hg := conductor_gamma_correction_real (by omega : q ≠ 0) χ (by linarith : 0 < s)
  have hz := real_logDeriv_conductorCompletedL_eq_divisor_tsum_source χ hprim hχ
    ((RealCharacterAnalysis.real_values_iff_quadratic χ).mp hreal) hs
  rw [Complex.neg_re]
  linarith

theorem source_logDeriv_upper :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ, 0 < β → β < 1 →
      DirichletCharacter.LFunction χ (β : ℂ) = 0 → ∀ s : ℝ, 1 < s → s ≤ 2 →
      (-logDeriv riemannZeta (s : ℂ) -
        logDeriv (DirichletCharacter.LFunction χ) (s : ℂ)).re ≤
        K * Real.log q + 1 / (s - 1) - 1 / (s - β) := by
  obtain ⟨K, hK, hupper⟩ := logDeriv_upper_of_completedL_lower
  refine ⟨K, hK, ?_⟩
  intro q _ hq χ hprim hχ hreal β hβ0 _ hzero s hs hs2
  exact hupper q hq χ hχ s β hs hs2
    (real_zero_le_conductorCompletedL_logDeriv χ hprim hχ
      ((RealCharacterAnalysis.real_values_iff_quadratic χ).mp hreal) hβ0 hzero hs)

end

section

theorem logDeriv_real_of_complex {f : ℂ → ℂ} {s : ℝ}
    (hf : DifferentiableAt ℂ f (s : ℂ)) (hreal : (f (s : ℂ)).im = 0) :
    (logDeriv f (s : ℂ)).re = logDeriv (fun x : ℝ => (f (x : ℂ)).re) s := by
  have hderiv := hf.hasDerivAt.real_of_complex.deriv
  have hval : ((f (s : ℂ)).re : ℂ) = f (s : ℂ) := by
    apply Complex.ext <;> simp [hreal]
  rw [logDeriv_apply, logDeriv_apply, hderiv, ← hval, Complex.div_ofReal_re]
  simp

open _root_.SiegelZeros.Complex.Hadamard

theorem source_hadamard_logDeriv_identity_real {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, (χ a).im = 0) {s : ℝ} (hs : 1 < s) :
    -logDeriv (fun x : ℝ => (DirichletCharacter.LFunction χ (x : ℂ)).re) s =
      Real.log ((q : ℝ) / Real.pi) / 2 +
        logDeriv Real.Gamma ((s + (1 - (χ (-1)).re) / 2) / 2) / 2 -
        ∑' p : divisorZeroIndex₀ (conductorCompletedL χ) Set.univ,
          (1 / ((s : ℂ) - divisorZeroIndex₀Val p)).re := by
  have hL := logDeriv_real_of_complex
    (DirichletCharacter.differentiable_LFunction hχ (s : ℂ))
    (RealCharacterAnalysis.lFunction_real χ hχ hreal s)
  have harg : 0 < (s + (1 - (χ (-1)).re) / 2) / 2 := by
    rw [character_parity_parameter_real]
    split_ifs <;> linarith
  have hG := logDeriv_real_of_complex
    (analyticAt_Gamma_of_re_pos (s := (((s + (1 - (χ (-1)).re) / 2) / 2 : ℝ) : ℂ))
      (by simpa using harg)).differentiableAt
    (by rw [Complex.Gamma_ofReal]; rfl)
  simp only [Complex.Gamma_ofReal, Complex.ofReal_re] at hG
  rw [← hL, ← hG]
  simpa only [Complex.neg_re] using source_hadamard_logDeriv_identity hq χ hprim hχ hreal hs

end

theorem completedL_analyticOrderAt_eq_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (DirichletCharacter.completedLFunction χ) s =
      analyticOrderAt (DirichletCharacter.LFunction χ) s := by
  have hgn := gammaFactor_ne_zero_of_re_pos χ hs
  have hinv : Differentiable ℂ (fun z => (χ.gammaFactor z)⁻¹) := by
    rcases χ.even_or_odd with heven | hodd
    · convert Complex.differentiable_Gammaℝ_inv using 1
      funext z
      rw [heven.gammaFactor_def]
    · convert Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1) using 1
      funext z
      rw [hodd.gammaFactor_def]
      rfl
  have hgamma : AnalyticAt ℂ χ.gammaFactor s := by
    convert (hinv.analyticAt s).inv (inv_ne_zero hgn) using 1
    funext z
    exact (inv_inv (χ.gammaFactor z)).symm
  have heq : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      fun z => DirichletCharacter.LFunction χ z * χ.gammaFactor z := by
    have hU : {z : ℂ | 0 < z.re} ∈ nhds s :=
      (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hs
    filter_upwards [hU] with z hz using completedL_eq_mul_gammaFactor χ hz
  rw [analyticOrderAt_congr heq]
  change analyticOrderAt (DirichletCharacter.LFunction χ * χ.gammaFactor) s = _
  rw [analyticOrderAt_mul ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s) hgamma,
    hgamma.analyticOrderAt_eq_zero.mpr hgn, add_zero]

theorem conductorCompletedL_analyticOrderAt_eq_LFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt (conductorCompletedL χ) s =
      analyticOrderAt (DirichletCharacter.LFunction χ) s :=
  (conductorCompletedL_analyticOrderAt_eq χ hχ s).trans
    (completedL_analyticOrderAt_eq_LFunction χ hχ hs)

theorem exists_radius_LFunction_ne_zero {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ β : ℝ, |β - 1| < ε →
      DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  have hcont : ContinuousAt (fun β : ℝ => DirichletCharacter.LFunction χ (β : ℂ)) 1 :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous.continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  have hnonzero : DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ) ≠ 0 := by
    simpa using DirichletCharacter.LFunction_apply_one_ne_zero hχ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hcont.eventually_ne hnonzero)
  refine ⟨ε, hε, fun β hβ => hball ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hβ

theorem exists_radius_LFunction_ne_zero_fixed_modulus (q : ℕ) [NeZero q] :
    ∃ ε : ℝ, 0 < ε ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, |β - 1| < ε → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
  classical
  have h : ∀ᶠ β : ℝ in nhds 1, ∀ χ : DirichletCharacter ℂ q,
      χ ≠ 1 → DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
    apply Filter.eventually_all.mpr
    intro χ
    by_cases hχ : χ = 1
    · exact Filter.Eventually.of_forall fun _ hne => (hne hχ).elim
    · obtain ⟨ε, hε, hzero⟩ := exists_radius_LFunction_ne_zero χ hχ
      have hr : ∀ᶠ β : ℝ in nhds 1, |β - 1| < ε := by
        filter_upwards [Metric.ball_mem_nhds (1 : ℝ) hε] with β hβ
        simpa [Metric.mem_ball, Real.dist_eq] using hβ
      exact hr.mono fun β hβ _ => hzero β hβ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨ε, hε, fun χ hχ β hβ => hball ?_ χ hχ⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hβ

theorem exists_gap_fixed_modulus (q : ℕ) [NeZero q] (hq : 3 ≤ q) :
    ∃ c : ℝ, 0 < c ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) → c ≤ (1 - β) * Real.log (q : ℝ) := by
  obtain ⟨ε, hε, hne⟩ := exists_radius_LFunction_ne_zero_fixed_modulus q
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  refine ⟨ε * Real.log (q : ℝ), mul_pos hε hlog, ?_⟩
  intro χ hχ β hβ
  apply mul_le_mul_of_nonneg_right _ hlog.le
  by_contra! hlt
  have habs : |β - 1| = 1 - β := by
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hβ.2.1)]
  exact hne χ hχ β (by simpa [habs] using hlt) hβ.2.2

theorem exists_gap_bounded_moduli (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 3 ≤ q → q ≤ Q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ β : ℝ, (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) → c ≤ (1 - β) * Real.log (q : ℝ) := by
  induction Q with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    intro q _ hq hQ
    omega
  | succ Q ih =>
    obtain ⟨c, hc, hbound⟩ := ih
    by_cases hQ : 3 ≤ Q + 1
    · let : NeZero (Q + 1) := ⟨by omega⟩
      obtain ⟨d, hd, hlast⟩ := exists_gap_fixed_modulus (Q + 1) hQ
      refine ⟨min c d, lt_min hc hd, ?_⟩
      intro q _ hq hqQ χ hχ β hβ
      rcases Nat.lt_or_eq_of_le hqQ with hlt | rfl
      · exact (min_le_left _ _).trans (hbound q hq (by omega) χ hχ β hβ)
      · exact (min_le_right _ _).trans (hlast χ hχ β hβ)
    · refine ⟨1, zero_lt_one, ?_⟩
      intro q _ hq hqQ
      omega

theorem exists_small_gap_large_modulus (hnot : ¬ (∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
          (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
            (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
              c ≤ (1 - β) * Real.log (q : ℝ)))
    (Q : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, ∃ hq : NeZero q, 3 ≤ q ∧ Q < q ∧
      ∃ χ : DirichletCharacter ℂ q, χ.IsPrimitive ∧ χ ≠ 1 ∧ (∀ a : ZMod q, (χ a).im = 0) ∧
        ∃ β : ℝ, (0 < β ∧ β < 1 ∧ @DirichletCharacter.LFunction q hq χ (β : ℂ) = 0) ∧
          (1 - β) * Real.log (q : ℝ) < ε := by
  classical
  obtain ⟨c, hc, hbound⟩ := exists_gap_bounded_moduli Q
  have hfail : ¬ (∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
            min c ε ≤ (1 - β) * Real.log (q : ℝ)) := fun h =>
    hnot ⟨min c ε, lt_min hc hε, h⟩
  push Not at hfail
  obtain ⟨q, hq0, hq, χ, hprim, hχ, hreal, β, hβ, hsmall⟩ := hfail
  let := hq0
  have hQ : Q < q := by
    by_contra! hle
    exact (not_lt_of_ge (hbound q hq hle χ hχ β hβ))
      (hsmall.trans_le (min_le_left _ _))
  exact ⟨q, hq0, hq, hQ, χ, hprim, hχ, hreal, β, hβ,
    hsmall.trans_le (min_le_right _ _)⟩

theorem exists_contrary_sequence (hnot : ¬ (∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
        ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
          (∀ a : ZMod q, (χ a).im = 0) → ∀ β : ℝ,
            (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
              c ≤ (1 - β) * Real.log (q : ℝ))) :
    ∃ q : ℕ → ℕ, ∃ hq : ∀ n, NeZero (q n),
      ∃ χ : ∀ n, DirichletCharacter ℂ (q n), ∃ β : ℕ → ℝ,
        (∀ n, 3 ≤ q n ∧ (χ n).IsPrimitive ∧ χ n ≠ 1 ∧ (∀ a : ZMod (q n), (χ n a).im = 0) ∧
          (0 < β n ∧ β n < 1 ∧ @DirichletCharacter.LFunction (q n) (hq n) (χ n) (β n : ℂ) = 0)) ∧
        Filter.Tendsto q Filter.atTop Filter.atTop ∧
        Filter.Tendsto (fun n => (1 - β n) * Real.log (q n : ℝ))
          Filter.atTop (nhds 0) := by
  classical
  have hex (n : ℕ) := exists_small_gap_large_modulus hnot n
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose q hq hq3 hn χ hprim hχ hreal β hβ hsmall using hex
  refine ⟨q, hq, χ, β, fun n => ⟨hq3 n, hprim n, hχ n, hreal n, hβ n⟩,
    Filter.tendsto_atTop_mono (fun n => (hn n).le) Filter.tendsto_id, ?_⟩
  refine squeeze_zero (fun n => ?_) (fun n => (hsmall n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact mul_nonneg (sub_nonneg.mpr (hβ n).2.1.le) (Real.log_natCast_nonneg (q n))

end WeightedTorusJets

end SiegelZeros

end OAI

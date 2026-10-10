import OAI.NumberTheory.Ostmann.Dirichlet.PrimePowerRemainder
import OAI.NumberTheory.Ostmann.Dirichlet.RealLogDerivativeUpper

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet
open scoped BigOperators
open ArithmeticFunction DirichletCharacter

noncomputable def realPrimeSeriesTerm {q : ℕ} (chi : DirichletCharacter ℂ q)
    (sigma : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then (chi n).re * Real.log n / (n : ℝ) ^ sigma else 0

noncomputable def realHigherPrimePowerTerm {q : ℕ} (chi : DirichletCharacter ℂ q)
    (sigma : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then 0 else (chi n).re * vonMangoldt n / (n : ℝ) ^ sigma

lemma norm_realHigherPrimePowerTerm_le {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 ≤ sigma) (n : ℕ) :
    ‖realHigherPrimePowerTerm chi sigma n‖ ≤ higherPrimePowerWeight n := by
  by_cases hp : n.Prime
  · simp [realHigherPrimePowerTerm, higherPrimePowerWeight, hp]
  have hchi : |(chi n).re| ≤ 1 := (Complex.abs_re_le_norm _).trans (chi.norm_le_one n)
  have hnonneg : 0 ≤ vonMangoldt n / (n : ℝ) ^ sigma := by positivity
  calc
    _ = |(chi n).re| * (vonMangoldt n / (n : ℝ) ^ sigma) := by
      simp only [realHigherPrimePowerTerm, hp, ite_false, Real.norm_eq_abs, abs_div,
        abs_mul, abs_of_nonneg vonMangoldt_nonneg,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) sigma)]
      ring
    _ ≤ 1 * (vonMangoldt n / (n : ℝ) ^ sigma) := mul_le_mul_of_nonneg_right hchi hnonneg
    _ ≤ _ := by simpa only [hp, ite_false, one_mul] using higherPrimePower_rpow_le hs n

theorem summable_realHigherPrimePowerTerm {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 ≤ sigma) : Summable (realHigherPrimePowerTerm chi sigma) :=
  Summable.of_norm_bounded summable_higherPrimePowerWeight (norm_realHigherPrimePowerTerm_le chi hs)

theorem norm_tsum_realHigherPrimePowerTerm_le {q : ℕ} (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 ≤ sigma) :
    ‖∑' n, realHigherPrimePowerTerm chi sigma n‖ ≤ Erdos970.Mertens.E₁ := by
  exact (norm_tsum_le_tsum_norm (summable_realHigherPrimePowerTerm chi hs).norm).trans
    (((summable_realHigherPrimePowerTerm chi hs).norm.tsum_le_tsum
      (norm_realHigherPrimePowerTerm_le chi hs) summable_higherPrimePowerWeight).trans
        tsum_higherPrimePowerWeight_le)

lemma real_twist_vonMangoldt_term {q : ℕ} (chi : DirichletCharacter ℂ q)
    (sigma : ℝ) (n : ℕ) :
    (LSeries.term (fun k => chi k * (vonMangoldt k : ℂ)) (sigma : ℂ) n).re =
      (chi n).re * vonMangoldt n / (n : ℝ) ^ sigma := by
  by_cases hn : n = 0
  · simp [hn]
  rw [LSeries.term_of_ne_zero hn]
  change ((chi n * (vonMangoldt n : ℂ)) / (((n : ℝ) : ℂ) ^ (sigma : ℂ))).re = _
  rw [← Complex.ofReal_cpow (Nat.cast_nonneg n)]
  simp [Complex.div_ofReal_re, Complex.mul_re]

lemma real_vonMangoldt_split {q : ℕ} (chi : DirichletCharacter ℂ q)
    (sigma : ℝ) (n : ℕ) :
    (LSeries.term (fun k => chi k * (vonMangoldt k : ℂ)) (sigma : ℂ) n).re =
      realPrimeSeriesTerm chi sigma n + realHigherPrimePowerTerm chi sigma n := by
  rw [real_twist_vonMangoldt_term]
  by_cases hp : n.Prime
  · simp [realPrimeSeriesTerm, realHigherPrimePowerTerm, hp, vonMangoldt_apply_prime hp]
  · simp [realPrimeSeriesTerm, realHigherPrimePowerTerm, hp]

theorem primeSeries_hasSum {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) :
    HasSum (realPrimeSeriesTerm chi sigma)
      ((-deriv (LFunction chi) (sigma : ℂ) / LFunction chi (sigma : ℂ)).re -
        ∑' n, realHigherPrimePowerTerm chi sigma n) := by
  have hsum := (LSeriesSummable_twist_vonMangoldt chi (show 1 < (sigma : ℂ).re from hs)).hasSum
  have he : LSeries ((fun k : ℕ => chi k) * (fun k : ℕ => (vonMangoldt k : ℂ))) (sigma : ℂ) =
      -deriv (LFunction chi) (sigma : ℂ) / LFunction chi (sigma : ℂ) := by
    rw [LSeries_twist_vonMangoldt_eq chi (show 1 < (sigma : ℂ).re from hs),
      deriv_LFunction_eq_deriv_LSeries chi (show 1 < (sigma : ℂ).re from hs),
      LFunction_eq_LSeries chi (show 1 < (sigma : ℂ).re from hs)]
  change HasSum _ (LSeries _ (sigma : ℂ)) at hsum
  rw [he] at hsum
  have h := (Complex.hasSum_re hsum).sub (summable_realHigherPrimePowerTerm chi hs.le).hasSum
  convert h using 1
  funext n
  change realPrimeSeriesTerm chi sigma n =
    (LSeries.term (fun k => chi k * (vonMangoldt k : ℂ)) (sigma : ℂ) n).re -
      realHigherPrimePowerTerm chi sigma n
  rw [real_vonMangoldt_split]
  ring

theorem primeSeries_lower_bound {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma : ℝ} (hs : 1 < sigma) :
    -(deriv (LFunction chi) (sigma : ℂ) / LFunction chi (sigma : ℂ)).re - Erdos970.Mertens.E₁ ≤
      ∑' n, realPrimeSeriesTerm chi sigma n := by
  rw [(primeSeries_hasSum chi hs).tsum_eq]
  have h := (le_abs_self (∑' n, realHigherPrimePowerTerm chi sigma n)).trans
    (norm_tsum_realHigherPrimePowerTerm_le chi hs.le)
  rw [neg_div, Complex.neg_re]
  linarith

end Ostmann.Dirichlet

end OAI

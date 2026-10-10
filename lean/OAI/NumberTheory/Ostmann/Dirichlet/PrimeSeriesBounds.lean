import OAI.NumberTheory.Ostmann.Dirichlet.PrimeLogDerivative
import OAI.NumberTheory.Ostmann.Dirichlet.PrimeSeriesDefinitions

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

namespace Ostmann.Dirichlet

lemma realPrimeSeriesTerm_one (sigma : ℝ) :
    realPrimeSeriesTerm (1 : DirichletCharacter ℂ 1) sigma = ordinaryPrimeSeriesTerm sigma := by
  funext n
  have hchar : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 := by
    rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _]
    exact map_one _
  simp [realPrimeSeriesTerm, ordinaryPrimeSeriesTerm, hchar]

theorem ordinaryPrimeSeries_summable {sigma : ℝ} (hs : 1 < sigma) :
    Summable (ordinaryPrimeSeriesTerm sigma) := by
  rw [← realPrimeSeriesTerm_one]
  exact (primeSeries_hasSum (1 : DirichletCharacter ℂ 1) hs).summable

theorem exists_ordinaryPrimeSeries_lower :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      (sigma - 1)⁻¹ - B ≤ ∑' n, ordinaryPrimeSeriesTerm sigma n := by
  obtain ⟨C, hC, hbound⟩ := exists_regular_zeta_compact_bound
  have hE : 0 ≤ Erdos970.Mertens.E₁ := tsum_nonneg Erdos970.Mertens.E₁.summand_nonneg
  refine ⟨C + Erdos970.Mertens.E₁, by positivity, ?_⟩
  intro sigma hs hs2
  have hreg := (Complex.re_le_norm (logDeriv regularZeta (sigma : ℂ))).trans
    (hbound (sigma : ℂ) hs.le hs2 (by simp))
  have he := congrArg Complex.re
    (neg_logDeriv_zeta_pole_split (s := (sigma : ℂ)) hs)
  have hpole : (1 / ((sigma : ℂ) - 1)).re = (sigma - 1)⁻¹ := by
    rw [show (sigma : ℂ) - 1 = ((sigma - 1 : ℝ) : ℂ) by simp]
    simp only [one_div, ← Complex.ofReal_inv, Complex.ofReal_re]
  simp only [Complex.add_re, Complex.neg_re] at he
  rw [hpole] at he
  have hp := primeSeries_lower_bound (1 : DirichletCharacter ℂ 1) hs
  rw [realPrimeSeriesTerm_one, DirichletCharacter.LFunction_modOne_eq] at hp
  simp only [logDeriv_apply] at he hreg
  linarith

theorem exists_realPrimeSeries_lower :
    ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi ≠ 1 → ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
        -K * modulusHeight q 0 - Erdos970.Mertens.E₁ ≤ ∑' n, realPrimeSeriesTerm chi sigma n := by
  obtain ⟨K, hK, hbound⟩ := uniform_real_log_derivative_upper
  refine ⟨K, hK, ?_⟩
  intro q _ chi hchi sigma hs hs2
  have h := hbound q chi hchi sigma hs hs2
  have hp := primeSeries_lower_bound chi hs
  linarith

end Ostmann.Dirichlet

end OAI

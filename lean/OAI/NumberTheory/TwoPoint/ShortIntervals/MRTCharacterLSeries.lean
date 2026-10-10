import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterEulerShift
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace OAI

/-! The shifted finite character Euler factors are the actual Dirichlet
L-series factors. The logarithmic identity below uses the absolutely
convergent Euler product only in the half-plane Re(s)>1. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical LSeries.notation

lemma mrt_character_shifted_factor {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t eps : ℝ) {p : ℕ} (hp : p≠0) :
    χ p*(p:ℂ)^(-(1+(eps:ℂ)-(t:ℂ)*Complex.I)) =
      (characterTwist χ t p/(p:ℂ))*(Real.exp (-eps*Real.log (p:ℝ)):ℂ) := by
  have hpC : (p:ℂ)≠0 := by exact_mod_cast hp
  have he : -(1+(eps:ℂ)-(t:ℂ)*Complex.I) =
      -1+(-(eps:ℂ)+(t:ℂ)*Complex.I) := by ring
  rw [he,Complex.cpow_add _ _ hpC,Complex.cpow_neg_one,
    Complex.cpow_def_of_ne_zero hpC,← Complex.natCast_log]
  have hs : (Real.log (p:ℝ):ℂ)*(-(eps:ℂ)+(t:ℂ)*Complex.I) =
      (-eps*Real.log (p:ℝ):ℝ)+((t*Real.log (p:ℝ):ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [hs,Complex.exp_add,← Complex.ofReal_exp]
  unfold characterTwist
  ring

theorem mrt_character_shifted_euler_limit {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) {eps : ℝ} (heps : 0<eps) :
    Tendsto (fun N : ℕ => mrtCharacterShiftedEuler χ t eps (primesUpTo N)) atTop
      (nhds (L ↗χ (1+(eps:ℂ)-(t:ℂ)*Complex.I))) := by
  have hs : 1<(1+(eps:ℂ)-(t:ℂ)*Complex.I).re := by
    simpa using heps
  have hh := χ.LSeries_eulerProduct hs
  have hN : Tendsto (fun N : ℕ => N+1) atTop atTop := tendsto_add_atTop_nat 1
  convert hh.comp hN using 1
  funext N
  change (∏ p ∈ primesUpTo N,
    (1-(characterTwist χ t p/(p:ℂ))*(Real.exp (-eps*Real.log (p:ℝ)):ℂ))⁻¹) = _
  change _ = ∏ p ∈ primesUpTo N,
    (1-χ p*(p:ℂ)^(-(1+(eps:ℂ)-(t:ℂ)*Complex.I)))⁻¹
  apply prod_congr rfl
  intro p hp
  rw [mrt_character_shifted_factor χ t eps (mem_filter.mp hp).2.ne_zero]

theorem mrt_character_LSeries_log_norm {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1<s.re) :
    Summable (fun p : Nat.Primes => -Complex.log (1-χ p*(p:ℂ)^(-s))) ∧
    Real.log ‖L ↗χ s‖ =
      ∑' p : Nat.Primes, -(Complex.log (1-χ p*(p:ℂ)^(-s))).re := by
  have hsum := (summable_dirichletSummand χ hs).of_norm.clog_one_sub.neg.subtype Nat.Prime
  have heq : (fun p : Nat.Primes =>
      -Complex.log (1-dirichletSummandHom χ (Complex.ne_zero_of_one_lt_re hs) p)) =
      (fun p : Nat.Primes => -Complex.log (1-χ p*(p:ℂ)^(-s))) := rfl
  change Summable (fun p : Nat.Primes =>
    -Complex.log (1-dirichletSummandHom χ (Complex.ne_zero_of_one_lt_re hs) p)) at hsum
  rw [heq] at hsum
  refine ⟨hsum,?_⟩
  rw [← χ.LSeries_eulerProduct_exp_log hs,Complex.norm_exp,Real.log_exp,
    Complex.re_tsum hsum]
  congr 1

end TwoPointCorrelations

end OAI

import OAI.MeasureTheory.Falconer.Angular.LocalizedStationaryExpansion
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem complex_iteratedDeriv_conj {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    iteratedDeriv n (fun x => conj (f x)) = fun x => conj (iteratedDeriv n f x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hd := (hf.differentiable_iteratedDeriv n
      (by exact_mod_cast (ENat.natCast_lt_top n))).differentiableAt (x := x)
    have hh := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt
    change HasDerivAt (fun y => conj (iteratedDeriv n f y))
      (conj (deriv (iteratedDeriv n f) x)) x at hh
    simpa only [iteratedDeriv_succ] using hh.deriv

 theorem localizedCircleIntegral_neg (Λ : ℝ) (f : ℝ → ℂ) :
    localizedCircleIntegral (-Λ) f = conj (localizedCircleIntegral Λ (fun x => conj (f x))) := by
  unfold localizedCircleIntegral intervalIntegral
  rw [map_sub,← integral_conj,← integral_conj]
  congr 1 <;> apply integral_congr_ae <;> filter_upwards with θ
  all_goals
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_conj,← Complex.exp_conj,
      Complex.conj_I,Complex.ofReal_neg]
    congr 2
    ring_nf

 theorem localized_stationary_opposite_remainder (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
    ∀ {Λ C D : ℝ}, 0 < Λ → 0 ≤ C → 1 ≤ D →
    (∀ k ≤ 2*(n+1)+2, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
    ‖localizedCircleIntegral (-Λ) f -
      conj (Complex.exp (Complex.I*(Λ:ℂ)) * (fresnelCoefficient (Λ/2) *
        stationaryDerivativeExpansion (fun x => conj (f x)) n Λ))‖ ≤
    ((Real.pi/(Λ/2))^(1/2:ℝ) * ((Real.pi^2/(Λ/2))^(n+1)/(n.factorial:ℝ))) *
      (A*C*D^(2*(n+1)+2)) := by
  obtain ⟨A,hA,hh⟩ := localized_stationary_uniform_remainder n
  refine ⟨A,hA,?_⟩
  intro f hf Λ C D hΛ hC hD hb
  have hf' : ContDiff ℝ ∞ (fun x => conj (f x)) := Complex.conjCLE.contDiff.comp hf
  have hb' : ∀ k ≤ 2*(n+1)+2, ∀ x,
      ‖iteratedDeriv k (fun x => conj (f x)) x‖ ≤ C*D^k := by
    intro k hk x
    rw [complex_iteratedDeriv_conj hf]
    simpa only [Complex.norm_conj] using hb k hk x
  rw [localizedCircleIntegral_neg,← map_sub,Complex.norm_conj]
  exact hh hf' hΛ hC hD hb'

end PlanarFalconer

end OAI

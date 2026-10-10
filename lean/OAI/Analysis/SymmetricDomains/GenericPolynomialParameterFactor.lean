import Mathlib
import OAI.Analysis.SymmetricDomains.AnalyticZeroNull

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory

theorem complex_polynomial_real_witness {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    ∃ x : Fin n → ℝ, MvPolynomial.eval (fun i => (x i : ℂ)) P ≠ 0 := by
  classical
  by_contra! hz
  apply hP
  apply MvPolynomial.funext_set (fun _ => Set.range (fun t : ℝ => (t : ℂ)))
    (fun _ => Set.infinite_range_of_injective Complex.ofReal_injective)
  intro z hz'
  have hc : ∀ i, ∃ t : ℝ, (t : ℂ) = z i := fun i => hz' i (mem_univ i)
  choose x hx using hc
  have he : z = fun i => (x i : ℂ) := (funext hx).symm
  simpa only [he,map_zero] using hz x

theorem complex_polynomial_real_zero_null {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    volume {x : Fin n → ℝ | MvPolynomial.eval (fun i => (x i : ℂ)) P = 0} = 0 := by
  obtain ⟨x,hx⟩ := complex_polynomial_real_witness P hP
  have he (s : Fin n → ℝ) : AnalyticAt ℝ (fun y : Fin n → ℝ => fun i => (y i : ℂ)) s := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact (Complex.ofRealCLM.analyticAt _).comp
      ((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt s)
  have ha : AnalyticOnNhd ℝ (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => (x i : ℂ)) P) univ := by
    intro s _
    exact (((AnalyticOnNhd.eval_mvPolynomial P) _ (mem_univ _)).restrictScalars (𝕜 := ℝ)).comp (he s)
  simpa only [mem_univ,true_and] using analytic_zero_null volume isOpen_univ
    isPreconnected_univ ha (mem_univ x) hx

theorem analyticAt_parameter_polynomial {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) (a : (Fin n → ℂ) × ℂ) :
    AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ =>
      Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P) a := by
  have hpoly : ∀ j : ℕ, AnalyticAt ℂ
      (fun p : ((Fin n → ℂ) × ℂ) => MvPolynomial.eval p.1 (P.coeff j)) a := by
    intro j
    exact (AnalyticOnNhd.eval_mvPolynomial (P.coeff j) _ (Set.mem_univ _)).comp
      ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).analyticAt _)
  simp only [Polynomial.eval₂_eq_sum_range]
  exact Finset.analyticAt_fun_sum (Finset.range (P.natDegree + 1)) (fun j _ =>
    (hpoly j).mul (((ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).analyticAt _).pow j))

theorem generic_polynomial_parameter_factor {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) (hP : P ≠ 0) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∃ (k : ℕ) (g : ((Fin n → ℂ) × ℂ) → ℂ),
        AnalyticAt ℂ g ((fun i => (s i : ℂ)),0) ∧
        g ((fun i => (s i : ℂ)),0) ≠ 0 ∧
        (∀ p, Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P = p.2^k * g p) ∧
        ∀ᶠ p in 𝓝 ((fun i => (s i : ℂ)),(0 : ℂ)), g p ≠ 0 := by
  let k := P.natTrailingDegree
  have hc : P.coeff k ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hP
  let E : Set (Fin n → ℝ) := {s | MvPolynomial.eval (fun i => (s i : ℂ)) (P.coeff k) = 0}
  refine ⟨E,complex_polynomial_real_zero_null _ hc,?_⟩
  intro s hs
  obtain ⟨Q,hQ⟩ := Polynomial.X_pow_dvd_iff.mpr
    (fun d (hd : d < k) => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd)
  let g : ((Fin n → ℂ) × ℂ) → ℂ := fun p => Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 Q
  have hg := analyticAt_parameter_polynomial Q ((fun i => (s i : ℂ)),0)
  have hcoeff : Q.coeff 0 = P.coeff k := by
    rw [hQ]
    simpa only [zero_add] using (Polynomial.coeff_X_pow_mul Q k 0).symm
  have hgne : g ((fun i => (s i : ℂ)),0) ≠ 0 := by
    simpa only [g,Polynomial.eval₂_at_zero,hcoeff,E,Set.mem_ofPred_eq] using hs
  refine ⟨k,g,hg,hgne,?_,hg.continuousAt.eventually_ne hgne⟩
  intro p
  rw [hQ,Polynomial.eval₂_mul,Polynomial.eval₂_pow,Polynomial.eval₂_X]

end Release061

end

end OAI

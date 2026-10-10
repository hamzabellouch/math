import OAI.Geometry.IsometricImmersion.Taylor.ActualDarbouxFaa
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation

structure ChainWord where
  arity : ℕ
  order : Fin arity → ℕ

def ChainWord.prepend (w : ChainWord) : ChainWord :=
  ⟨w.arity + 1, Fin.cons 1 w.order⟩

def ChainWord.bump (w : ChainWord) (i : Fin w.arity) : ChainWord :=
  ⟨w.arity, Function.update w.order i (w.order i + 1)⟩

def ChainWord.total (w : ChainWord) : ℕ := ∑ i, w.order i

def ChainWord.Positive (w : ChainWord) : Prop := ∀ i, 0 < w.order i

def ChainWord.Bounded (w : ChainWord) (n : ℕ) : Prop := ∀ i, w.order i ≤ n

def chainTerm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (J : ℝ → E) (w : ChainWord) (t : ℝ) : ℝ :=
  iteratedFDeriv ℝ w.arity F (J t) (fun i => iteratedDeriv (w.order i) J t)

theorem iteratedDeriv_contDiffAt_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : ℝ → E} {t : ℝ} (hJ : ContDiffAt ℝ ∞ J t) :
    ∀ n, ContDiffAt ℝ ∞ (iteratedDeriv n J) t := by
  intro n
  induction n with
  | zero => simpa using hJ
  | succ n hn =>
    rw [iteratedDeriv_succ]
    exact hn.derivWithin (by simp)

theorem iteratedDeriv_hasDerivAt_infty
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : ℝ → E} {t : ℝ} (hJ : ContDiffAt ℝ ∞ J t) (n : ℕ) :
    HasDerivAt (iteratedDeriv n J) (iteratedDeriv (n + 1) J t) t := by
  rw [iteratedDeriv_succ]
  exact ((iteratedDeriv_contDiffAt_infty hJ n).differentiableAt (by simp)).hasDerivAt

theorem chainTerm_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {J : ℝ → E} {t : ℝ}
    (hF : ContDiffAt ℝ ∞ F (J t)) (hJ : ContDiffAt ℝ ∞ J t) (w : ChainWord) :
    HasDerivAt (chainTerm F J w)
      (chainTerm F J w.prepend t + ∑ i, chainTerm F J (w.bump i) t) t := by
  have hJ0 : HasDerivAt J (iteratedDeriv 1 J t) t := by
    simpa using iteratedDeriv_hasDerivAt_infty hJ 0
  have houter := (hF.differentiableAt_iteratedFDeriv (m := w.arity)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl w.arity)).hasFDerivAt
    |>.comp_hasDerivAt t hJ0
  have h := houter.hasFDerivAt.continuousMultilinearMap_apply
    (fun i => (iteratedDeriv_hasDerivAt_infty hJ (w.order i)).hasFDerivAt)
    |>.hasDerivAt
  convert h using 1 <;> try rfl
  simp only [chainTerm, ChainWord.prepend, ChainWord.bump,
    add_apply, ContinuousLinearMap.comp_apply,
    sum_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul,
    ContinuousMultilinearMap.apply_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change (iteratedFDeriv ℝ w.arity F (J t))
      (fun j => iteratedDeriv (Function.update w.order i (w.order i + 1) j) J t) =
    (iteratedFDeriv ℝ w.arity F (J t))
      (Function.update (fun j => iteratedDeriv (w.order j) J t) i (iteratedDeriv (w.order i + 1) J t))
  congr 1
  funext j
  by_cases hj : j = i
  · subst j; simp
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]

theorem ChainWord.prepend_positive {w : ChainWord} (hw : w.Positive) :
    w.prepend.Positive := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Nat.zero_lt_one
  · exact hw j

theorem ChainWord.bump_positive {w : ChainWord} (hw : w.Positive) (i : Fin w.arity) :
    (w.bump i).Positive := by
  change ∀ j : Fin w.arity, 0 < Function.update w.order i (w.order i + 1) j
  intro j
  by_cases hj : j = i
  · subst j; simp
  · rw [Function.update_of_ne hj]
    exact hw j

theorem ChainWord.prepend_total (w : ChainWord) : w.prepend.total = w.total + 1 := by
  change (∑ j : Fin (w.arity + 1), Fin.cons 1 w.order j) = (∑ j : Fin w.arity, w.order j) + 1
  simp [Fin.sum_univ_succ, Nat.add_comm]

theorem ChainWord.bump_total (w : ChainWord) (i : Fin w.arity) :
    (w.bump i).total = w.total + 1 := by
  classical
  have hi : i ∈ (Finset.univ : Finset (Fin w.arity)) := Finset.mem_univ i
  have hsum := Finset.sum_update_of_mem hi w.order (w.order i + 1)
  simp only [Finset.sdiff_singleton_eq_erase] at hsum
  change (∑ j : Fin w.arity, Function.update w.order i (w.order i + 1) j) =
    (∑ j : Fin w.arity, w.order j) + 1
  rw [hsum]
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin w.arity)) w.order hi
  omega

theorem ChainWord.prepend_bounded {w : ChainWord} {n : ℕ}
    (hn : 1 ≤ n) (hw : w.Bounded n) : w.prepend.Bounded n := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hn
  · exact hw j

theorem ChainWord.bump_bounded {w : ChainWord} {n : ℕ}
    (hw : w.Bounded n) (i : Fin w.arity) : (w.bump i).Bounded (n + 1) := by
  change ∀ j : Fin w.arity, Function.update w.order i (w.order i + 1) j ≤ n + 1
  intro j
  by_cases hj : j = i
  · subst j
    simpa [ChainWord.bump] using Nat.add_le_add_right (hw i) 1
  · rw [Function.update_of_ne hj]
    exact Nat.le_succ_of_le (hw j)

theorem actualP_chainTerm_hasDerivAt
    {g : SmoothLocal.Geometry.MetricField} {z : SmoothLocal.Geometry.Coord → ℝ}
    {U : Set SmoothLocal.Geometry.Coord} {x y : ℝ}
    (hg : SmoothLocal.Geometry.SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : (![x, y] : SmoothLocal.Geometry.Coord) ∈ U)
    (hyy : SmoothLocal.Geometry.covHessian g z ![x, y] 1 1 ≠ 0) (w : ChainWord) :
    HasDerivAt (chainTerm (sixVariableP g) (solutionJetCurve z x) w)
      (chainTerm (sixVariableP g) (solutionJetCurve z x) w.prepend y +
        ∑ i, chainTerm (sixVariableP g) (solutionJetCurve z x) (w.bump i) y) y := by
  exact chainTerm_hasDerivAt
    (sixVariableP_contDiffAt_solutionJet hg hU hp hyy)
    (solutionJetCurve_contDiffAt hU hz hp) w

end SmoothLocal.HighEquation

end

end OAI

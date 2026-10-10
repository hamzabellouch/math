import Mathlib
import OAI.Analysis.SymmetricDomains.PolynomialEmptyInterior
import OAI.Analysis.SymmetricDomains.RealPolynomialAnalyticRoot

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
open Polynomial Set Filter Topology

lemma continuousAt_real_parameter_eval {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℝ))
    {g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hg : ContinuousAt g x) :
    ContinuousAt (fun y => P.eval₂ (MvPolynomial.eval y) (g y)) x := by
  simp only [Polynomial.eval₂_eq_sum_range]
  exact tendsto_finsetSum _ (fun j _ =>
    (MvPolynomial.continuous_eval (P.coeff j)).continuousAt.mul (hg.pow j))

theorem polynomial_zero_persists_on_simple_sheet {n : ℕ}
    (P Q : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), ContinuousAt g x →
        (∀ᶠ y in 𝓝 x, P.eval₂ (MvPolynomial.eval y) (g y) = 0) →
        P.derivative.eval₂ (MvPolynomial.eval x) (g x) ≠ 0 →
        MvPolynomial.eval x D ≠ 0 → Q.eval₂ (MvPolynomial.eval x) (g x) = 0 →
        ∀ᶠ y in 𝓝 x, Q.eval₂ (MvPolynomial.eval y) (g y) = 0 := by
  obtain ⟨a,b,c,ha,hb,hc,A,B,C',U,V,h₁,h₂,h₃⟩ :=
    polynomial_gcd_specialization_data (K := FractionRing (MvPolynomial (Fin n) ℝ)) P Q
  refine ⟨a*b*c,mul_ne_zero (mul_ne_zero ha hb) hc,?_⟩
  intro g x hg hP hs hD hQ
  have ha' : MvPolynomial.eval x a ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,zero_mul]
  have hb' : MvPolynomial.eval x b ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hc' : MvPolynomial.eval x c ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero]
  have hPx : P.eval₂ (MvPolynomial.eval x) (g x) = 0 := hP.self_of_nhds
  have hAx : A.eval₂ (MvPolynomial.eval x) (g x) = 0 := by
    have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval x) (g x)) h₃
    simp only [eval₂_mul,eval₂_C,eval₂_add,hPx,hQ,zero_mul,zero_add] at he
    exact (mul_eq_zero.mp he).resolve_left hc'
  have hBx : B.eval₂ (MvPolynomial.eval x) (g x) ≠ 0 := by
    intro hz
    have hd := congrArg Polynomial.derivative h₁
    have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval x) (g x)) hd
    simp only [derivative_mul,derivative_C,zero_mul,zero_add,eval₂_mul,eval₂_C,
      eval₂_add,hAx,hz,zero_mul,mul_zero,zero_add] at he
    exact hs ((mul_eq_zero.mp he).resolve_left ha')
  have hBn := (continuousAt_real_parameter_eval B hg).eventually_ne hBx
  have hbn := (MvPolynomial.continuous_eval b).continuousAt.eventually_ne hb'
  filter_upwards [hP,hBn,hbn] with y hPy hBy hby
  have hAy : A.eval₂ (MvPolynomial.eval y) (g y) = 0 := by
    have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval y) (g y)) h₁
    simp only [eval₂_mul,eval₂_C,hPy,mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hBy
  have he := congrArg (Polynomial.eval₂ (MvPolynomial.eval y) (g y)) h₂
  simp only [eval₂_mul,eval₂_C,hAy,zero_mul] at he
  exact (mul_eq_zero.mp he).resolve_left hby

theorem PolynomialSignSet.regular_on_simple_sheet {n : ℕ}
    {S : Set (Option (Fin n) → ℝ)} (hS : PolynomialSignSet id S)
    (P : Polynomial (MvPolynomial (Fin n) ℝ)) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ), ContinuousAt g x →
        (∀ᶠ y in 𝓝 x, P.eval₂ (MvPolynomial.eval y) (g y) = 0) →
        P.derivative.eval₂ (MvPolynomial.eval x) (g x) ≠ 0 →
        MvPolynomial.eval x D ≠ 0 →
        (∀ᶠ y in 𝓝 x, (fun o => Option.elim o (g y) y) ∈ S) ∨
        (∀ᶠ y in 𝓝 x, (fun o => Option.elim o (g y) y) ∉ S) := by
  induction hS with
  | zero q =>
    let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) q
    obtain ⟨D,hD,hzero⟩ := polynomial_zero_persists_on_simple_sheet P Q
    refine ⟨D,hD,?_⟩
    intro g x hg hP hs hDx
    by_cases hz : Q.eval₂ (MvPolynomial.eval x) (g x) = 0
    · left
      simpa only [mem_ofPred,id_eq,MvPolynomial.optionEquivLeft_elim_eval,eval_map,Q] using
        hzero g x hg hP hs hDx hz
    · right
      simpa only [mem_ofPred,id_eq,MvPolynomial.optionEquivLeft_elim_eval,eval_map,Q] using
        (continuousAt_real_parameter_eval Q hg).eventually_ne hz
  | positive q =>
    let Q := MvPolynomial.optionEquivLeft ℝ (Fin n) q
    obtain ⟨D,hD,hzero⟩ := polynomial_zero_persists_on_simple_sheet P Q
    refine ⟨D,hD,?_⟩
    intro g x hg hP hs hDx
    by_cases hz : Q.eval₂ (MvPolynomial.eval x) (g x) = 0
    · right
      filter_upwards [hzero g x hg hP hs hDx hz] with y hy
      change ¬ 0 < MvPolynomial.eval (fun o => Option.elim o (g y) y) q
      rw [MvPolynomial.optionEquivLeft_elim_eval,eval_map]
      change ¬ 0 < Q.eval₂ (MvPolynomial.eval y) (g y)
      simp only [hy,lt_self_iff_false,not_false_eq_true]
    · rcases lt_or_gt_of_ne hz with hneg | hpos
      · right
        filter_upwards [(continuousAt_real_parameter_eval Q hg).eventually_lt_const hneg] with y hy
        change ¬ 0 < MvPolynomial.eval (fun o => Option.elim o (g y) y) q
        rw [MvPolynomial.optionEquivLeft_elim_eval,eval_map]
        exact not_lt_of_ge hy.le
      · left
        simpa only [mem_ofPred,id_eq,MvPolynomial.optionEquivLeft_elim_eval,eval_map,Q] using
          (continuousAt_real_parameter_eval Q hg).eventually_const_lt hpos
  | @compl S hS ih =>
    obtain ⟨D,hD,hreg⟩ := ih
    refine ⟨D,hD,?_⟩
    intro g x hg hP hs hDx
    simpa only [mem_compl_iff,not_not] using (hreg g x hg hP hs hDx).symm
  | @union S T hS hT ihS ihT =>
    obtain ⟨D,hD,hregD⟩ := ihS
    obtain ⟨E,hE,hregE⟩ := ihT
    refine ⟨D*E,mul_ne_zero hD hE,?_⟩
    intro g x hg hP hs hDE
    have hD' : MvPolynomial.eval x D ≠ 0 := fun hz => hDE (by simp only [map_mul,hz,zero_mul])
    have hE' : MvPolynomial.eval x E ≠ 0 := fun hz => hDE (by simp only [map_mul,hz,mul_zero])
    rcases hregD g x hg hP hs hD' with h | h
    · exact Or.inl (h.mono fun y hy => Or.inl hy)
    rcases hregE g x hg hP hs hE' with k | k
    · exact Or.inl (k.mono fun y hy => Or.inr hy)
    · right
      filter_upwards [h,k] with y hy ky
      exact fun h => h.elim hy ky

end Release061

end

end OAI

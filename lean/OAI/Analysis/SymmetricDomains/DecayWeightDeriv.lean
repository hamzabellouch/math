import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective
import OAI.Analysis.SymmetricDomains.PolynomialSignSetFinite

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
namespace Release061.SignElimination
open Polynomial Set Filter
open scoped Topology BigOperators Classical

noncomputable def criticalSampler (P : ℝ[X]) : ℝ[X] :=
  P.derivative + X * (X * P.derivative - C (P.natDegree+1 : ℝ) * P)

noncomputable def decayWeight (P : ℝ[X]) (x : ℝ) : ℝ :=
  (P.eval x)^2 / (1+x^2)^(P.natDegree+1)

lemma X_derivative_coeff (P : ℝ[X]) (n : ℕ) :
    (X * P.derivative).coeff n = (n : ℝ)*P.coeff n := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_X_mul,coeff_derivative,mul_comm]

lemma criticalSampler_top_coeff (P : ℝ[X]) :
    (criticalSampler P).coeff (P.natDegree+1) = -P.leadingCoeff := by
  rw [criticalSampler,coeff_add,coeff_X_mul,coeff_sub,X_derivative_coeff,coeff_C_mul]
  have hz : P.derivative.coeff (P.natDegree+1) = 0 := by
    rw [coeff_derivative,coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < P.natDegree+1+1),zero_mul]
  rw [hz,coeff_natDegree]
  ring

lemma criticalSampler_ne_zero {P : ℝ[X]} (hP : P ≠ 0) : criticalSampler P ≠ 0 := by
  intro hz
  have h := criticalSampler_top_coeff P
  rw [hz,coeff_zero,eq_comm,neg_eq_zero] at h
  exact leadingCoeff_ne_zero.mpr hP h

lemma decayWeight_continuous (P : ℝ[X]) : Continuous (decayWeight P) := by
  apply Continuous.div
  · exact P.continuous.pow 2
  · fun_prop
  · intro x
    exact pow_ne_zero _ (by positivity : (1:ℝ)+x^2 ≠ 0)

lemma decayWeight_tendsto (P : ℝ[X]) : Tendsto (decayWeight P) (cocompact ℝ) (𝓝 0) := by
  let A : ℝ[X] := P^2
  let B : ℝ[X] := (1+X^2)^(P.natDegree+1)
  have hd : A.degree < B.degree := by
    apply degree_lt_degree
    dsimp [A,B]
    rw [natDegree_pow,natDegree_pow]
    have hs : (1+X^2 : ℝ[X]).natDegree = 2 := by
      rw [natDegree_add_eq_right_of_natDegree_lt (by norm_num),natDegree_pow]
      simp
    rw [hs]
    omega
  have ht := Polynomial.div_tendsto_atTop_zero_of_degree_lt A B hd
  have hb := Polynomial.div_tendsto_atBot_zero_of_degree_lt A B hd
  change Tendsto (fun x => (P.eval x)^2 / (1+x^2)^(P.natDegree+1)) _ _
  rw [cocompact_eq_atBot_atTop]
  simpa only [A,B,eval_pow,eval_add,eval_one,eval_X] using hb.sup ht

lemma decayWeight_deriv (P : ℝ[X]) (x : ℝ) :
    HasDerivAt (decayWeight P)
      (2 * P.eval x * (criticalSampler P).eval x /
        (1+x^2)^(P.natDegree+2)) x := by
  have hpos : (1:ℝ)+x^2 ≠ 0 := by positivity
  have hden := ((hasDerivAt_id x).pow 2).const_add 1
  have hd := ((P.hasDerivAt x).pow 2).div
    (hden.pow (P.natDegree+1)) (pow_ne_zero _ hpos)
  apply hd.congr_deriv
  simp only [criticalSampler,eval_add,eval_mul,eval_X,eval_sub,eval_C,
    Pi.pow_apply,id_eq,Nat.add_sub_cancel,Nat.reduceSub,pow_one,
    Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,mul_one]
  rw [show P.natDegree+2 = (P.natDegree+1)+1 by omega]
  simp only [pow_succ]
  field_simp
  ring

end Release061.SignElimination

end

end OAI

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.ArithmeticSaving
open Finset Classical

variable {ι : Type*} [DecidableEq ι] {E : ℕ}

structure SquarefreeExpression (ι : Type*) [DecidableEq ι] (E : ℕ) where
  factors : Fin E → Finset ι
  coefficient : Fin E → ℤ

namespace SquarefreeExpression
variable (d : SquarefreeExpression ι E)

def eval (x : ι → ℤ) : ℤ := ∑ e, d.coefficient e * ∏ v ∈ d.factors e, x v

def support : Finset ι := univ.biUnion (fun e => if d.coefficient e=0 then ∅ else d.factors e)

def linearCoeff (q : ι) (x : ι → ℤ) : ℤ :=
  ∑ e, if q ∈ d.factors e then d.coefficient e * ∏ v ∈ (d.factors e).erase q, x v else 0

def constantTerm (q : ι) (x : ι → ℤ) : ℤ :=
  ∑ e, if q ∈ d.factors e then 0 else d.coefficient e * ∏ v ∈ d.factors e, x v

lemma mem_support {e : Fin E} (he : d.coefficient e ≠ 0) {v : ι} (hv : v ∈ d.factors e) :
    v ∈ d.support := mem_biUnion.mpr ⟨e,mem_univ _,by simpa [he] using hv⟩

lemma eval_affine (q : ι) (x : ι → ℤ) :
    d.eval x = d.linearCoeff q x * x q + d.constantTerm q x := by
  unfold eval linearCoeff constantTerm
  rw [sum_mul,←sum_add_distrib]
  apply sum_congr rfl
  intro e he
  by_cases hq : q ∈ d.factors e
  · simp only [hq,ite_true,add_zero]
    rw [←mul_prod_erase _ _ hq]
    ring
  · simp only [hq,ite_false,zero_mul,zero_add]

lemma eval_congr_on {x y : ι → ℤ} (hxy : ∀ v ∈ d.support, x v=y v) : d.eval x=d.eval y := by
  apply sum_congr rfl
  intro e he
  by_cases hc : d.coefficient e=0
  · simp only [hc,zero_mul]
  · congr 1
    apply prod_congr rfl
    intro v hv
    exact hxy v (d.mem_support hc hv)

lemma linearCoeff_congr_on (q : ι) {x y : ι → ℤ}
    (hxy : ∀ v ∈ d.support, v≠q → x v=y v) : d.linearCoeff q x=d.linearCoeff q y := by
  apply sum_congr rfl
  intro e he
  by_cases hq : q ∈ d.factors e
  · simp only [hq,ite_true]
    by_cases hc : d.coefficient e=0
    · simp only [hc,zero_mul]
    · congr 1
      apply prod_congr rfl
      intro v hv
      exact hxy v (d.mem_support hc (mem_erase.mp hv).2) (mem_erase.mp hv).1
  · simp only [hq,ite_false]

lemma constantTerm_congr_on (q : ι) {x y : ι → ℤ}
    (hxy : ∀ v ∈ d.support, v≠q → x v=y v) : d.constantTerm q x=d.constantTerm q y := by
  apply sum_congr rfl
  intro e he
  by_cases hq : q ∈ d.factors e
  · simp only [hq,ite_true]
  · simp only [hq,ite_false]
    by_cases hc : d.coefficient e=0
    · simp only [hc,zero_mul]
    · congr 1
      apply prod_congr rfl
      intro v hv
      exact hxy v (d.mem_support hc hv) (by rintro rfl; exact hq hv)

lemma eval_independent (q : ι) (hq : q ∉ d.support) {x y : ι → ℤ}
    (hxy : ∀ v, v≠q → x v=y v) : d.eval x=d.eval y := by
  apply d.eval_congr_on
  intro v hv
  exact hxy v (by rintro rfl; exact hq hv)

lemma abs_eval_le (J : ℕ) (B H : ℝ) (hB : 0 ≤ B) (hH : 0 ≤ H)
    (hvars : ∀ e, (d.factors e).card ≤ J)
    (hcoeff : ∀ e, |(d.coefficient e:ℝ)| ≤ H)
    (x : ι → ℤ) (hx : ∀ v ∈ d.support, |(x v:ℝ)| ≤ Real.exp B) :
    |(d.eval x:ℝ)| ≤ E*H*Real.exp (B*J) := by
  have hExp : 1 ≤ Real.exp B := Real.one_le_exp hB
  simp only [eval,Int.cast_sum,Int.cast_mul,Int.cast_prod]
  calc
    _ ≤ ∑ e : Fin E, |(d.coefficient e:ℝ)| * ∏ v ∈ d.factors e, |(x v:ℝ)| := by
      simpa only [abs_mul,abs_prod] using abs_sum_le_sum_abs
        (fun e : Fin E => (d.coefficient e:ℝ) * ∏ v ∈ d.factors e, (x v:ℝ)) univ
    _ ≤ ∑ _e : Fin E, H*Real.exp (B*J) := by
      apply sum_le_sum
      intro e he
      by_cases hc : d.coefficient e=0
      · simp only [hc,Int.cast_zero,abs_zero,zero_mul]
        exact mul_nonneg hH (Real.exp_pos _).le
      · apply mul_le_mul (hcoeff e) _ (prod_nonneg (fun v hv => abs_nonneg _)) hH
        calc
          _ ≤ ∏ _v ∈ d.factors e, Real.exp B := prod_le_prod₀
            (fun v hv => abs_nonneg _) (fun v hv => hx v (d.mem_support hc hv))
          _ = Real.exp B ^ (d.factors e).card := by rw [prod_const]
          _ ≤ Real.exp B ^ J := pow_le_pow_right₀ hExp (hvars e)
          _ = _ := by rw [←Real.exp_nat_mul]; congr 1; ring
    _ = _ := by simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end SquarefreeExpression
end OrdinaryCorrelations.ArithmeticSaving

end

end OAI

import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryWindowEuler

lemma powerset_first_moment {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w L : ι → ℝ) (hw : ∀i∈S,0≤w i) :
    (∑A∈S.powerset,(∏i∈A,w i)*(∑i∈A,L i)) =
      (∏i∈S,(1+w i))*(∑i∈S,w i*L i/(1+w i)) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hwa := hw a (mem_insert_self _ _)
    have hws : ∀i∈S,0≤w i := fun i hi => hw i (mem_insert_of_mem hi)
    have hn : 1+w a ≠ 0 := by linarith
    rw [sum_powerset_insert ha]
    have he : (∑A∈S.powerset,(∏i∈insert a A,w i)*(∑i∈insert a A,L i)) =
        w a*L a*(∑A∈S.powerset,∏i∈A,w i)+
        w a*(∑A∈S.powerset,(∏i∈A,w i)*(∑i∈A,L i)) := by
      rw [mul_sum,mul_sum,←sum_add_distrib]
      apply sum_congr rfl
      intro A hA
      have haA : a∉A := fun hh => ha (mem_powerset.mp hA hh)
      rw [prod_insert haA,sum_insert haA]
      ring
    rw [he,ih hws,←prod_one_add,prod_insert ha,sum_insert ha]
    field_simp
    ring

lemma truncated_mass {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (w L : ι → ℝ) (hw : ∀i∈S,0≤w i) (hL : ∀i∈S,0≤L i)
    {Z : ℝ} (hZ : 0<Z) (hm : 2*(∑i∈S,w i*L i/(1+w i))≤Z) :
    (∏i∈S,(1+w i))/2 ≤
      ∑A∈S.powerset,if (∑i∈A,L i)≤Z then ∏i∈A,w i else 0 := by
  let total : ℝ := ∏i∈S,(1+w i)
  let low : ℝ := ∑A∈S.powerset,if (∑i∈A,L i)≤Z then ∏i∈A,w i else 0
  have ht : 0≤total := prod_nonneg (fun i hi => by linarith [hw i hi])
  have hsum : ∑A∈S.powerset,∏i∈A,w i=total := (prod_one_add S).symm
  have hhigh : Z*(total-low)≤
      ∑A∈S.powerset,(∏i∈A,w i)*(∑i∈A,L i) := by
    dsimp only [low]
    rw [←hsum,←sum_sub_distrib,mul_sum]
    apply sum_le_sum
    intro A hA
    have hsub := mem_powerset.mp hA
    have hn : 0≤∏i∈A,w i := prod_nonneg (fun i hi => hw i (hsub hi))
    have hl : 0≤∑i∈A,L i := sum_nonneg (fun i hi => hL i (hsub hi))
    split_ifs with hh
    · simp only [sub_self,mul_zero]
      exact mul_nonneg hn hl
    · simp only [sub_zero]
      nlinarith [lt_of_not_ge hh]
  rw [powerset_first_moment S w L hw] at hhigh
  have hh := mul_le_mul_of_nonneg_left hm ht
  dsimp only [total] at *
  change _≤low
  nlinarith

def primeWeight (p : ℕ) : ℝ := ((p:ℝ)-1)⁻¹

lemma prime_weight_nonneg {p : ℕ} (hp : Nat.Prime p) : 0≤primeWeight p := by
  unfold primeWeight
  have : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  positivity

lemma prime_weight_moment {p : ℕ} (hp : Nat.Prime p) :
    primeWeight p*Real.log p/(1+primeWeight p)=Real.log p/p := by
  have h1 : (p:ℝ)-1 ≠ 0 := by
    have : (1:ℝ)<p := by exact_mod_cast hp.one_lt
    linarith
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast hp.ne_zero
  unfold primeWeight
  field_simp [h1,hp0]
  ring

lemma log_prod_primes (S : Finset ℕ) (hS : ∀p∈S,Nat.Prime p) :
    Real.log ((∏p∈S,p:ℕ):ℝ)=∑p∈S,Real.log p := by
  rw [Nat.cast_prod,Real.log_prod]
  intro p hp
  exact_mod_cast (hS p hp).ne_zero

theorem truncated_prime_mass (S : Finset ℕ) (hS : ∀p∈S,Nat.Prime p)
    {z : ℕ} (hz : 1<z) (hm : 2*(∑p∈S,Real.log p/p)≤Real.log z) :
    (∏p∈S,(1+primeWeight p))/2 ≤
      ∑A∈S.powerset,if (∏p∈A,p)≤z then ∏p∈A,primeWeight p else 0 := by
  have hzR : (1:ℝ)<z := by exact_mod_cast hz
  have h := truncated_mass S primeWeight (fun p => Real.log p)
    (fun p hp => prime_weight_nonneg (hS p hp))
    (fun p hp => Real.log_nonneg (by exact_mod_cast (hS p hp).one_lt.le))
    (Real.log_pos hzR)
    (by
      have he : (∑p∈S,primeWeight p*Real.log p/(1+primeWeight p))=
          ∑p∈S,Real.log p/p := sum_congr rfl (fun p hp => prime_weight_moment (hS p hp))
      rwa [he])
  convert h using 1
  apply sum_congr rfl
  intro A hA
  have hAp : ∀p∈A,Nat.Prime p := fun p hp => hS p (mem_powerset.mp hA hp)
  have hprod : (0:ℝ)<((∏p∈A,p:ℕ):ℝ) := by
    exact_mod_cast prod_pos (fun p hp => (hAp p hp).pos)
  rw [←log_prod_primes A hAp]
  have he : (∏p∈A,p)≤z ↔ Real.log ((∏p∈A,p:ℕ):ℝ)≤Real.log z := by
    rw [Real.log_le_log_iff hprod (by positivity)]
    exact Nat.cast_le.symm
  simp only [←he]

lemma prime_log_mass (S : Finset ℕ) (hS : ∀p∈S,Nat.Prime p) :
    Real.exp (∑p∈S,(p:ℝ)⁻¹) ≤ ∏p∈S,(1+primeWeight p) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact (Real.exp_pos _).le
  · intro p hp
    have hp1 : (1:ℝ)<p := by exact_mod_cast (hS p hp).one_lt
    have hp0 : (0:ℝ)<p := by linarith
    have hpinv : (p:ℝ)⁻¹<1 := (inv_lt_one₀ hp0).mpr hp1
    have he := Real.log_le_sub_one_of_pos (by linarith : 0<1-(p:ℝ)⁻¹)
    have hident : 1+primeWeight p=(1-(p:ℝ)⁻¹)⁻¹ := by
      unfold primeWeight
      have hn : (p:ℝ)-1≠0 := by linarith
      field_simp [hn,hp0.ne']
      ring
    rw [hident,←Real.exp_log (inv_pos.mpr (by linarith : 0<1-(p:ℝ)⁻¹))]
    apply Real.exp_le_exp.mpr
    rw [Real.log_inv]
    linarith

end OrdinaryWindowEuler

end

end OAI

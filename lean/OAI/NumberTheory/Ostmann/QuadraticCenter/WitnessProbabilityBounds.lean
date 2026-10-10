import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessEvent
import OAI.NumberTheory.Ostmann.QuadraticCenter.WitnessProbability

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem primeProductMean_add (P : Finset ℕ) (k : ℕ) (f g : ℕ → ℝ) :
    primeProductMean P k (fun q => f q+g q)=primeProductMean P k f+primeProductMean P k g := by
  simp only [primeProductMean,Finset.sum_add_distrib,add_div]

theorem primeProductMean_event_split (P : Finset ℕ) (k : ℕ)
    (E : ℕ → Prop) [DecidablePred E] (f : ℕ → ℝ) :
    primeProductMean P k f =
      primeProductMean P k (fun q => if E q then f q else 0)+
      primeProductMean P k (fun q => if E q then 0 else f q) := by
  rw [←primeProductMean_add]
  congr 1
  funext q
  split_ifs <;> simp

theorem primeProduct_event_mean_lower (P : Finset ℕ) (k : ℕ)
    (E : ℕ → Prop) [DecidablePred E] (full small large rest : ℕ → ℝ)
    {a total largeBound restBound offBound : ℝ}
    (hsplit : ∀q∈primeProductSamples P k,full q ≤ small q+large q+rest q)
    (hfull : total≤primeProductMean P k full)
    (hlarge : primeProductMean P k large≤largeBound)
    (hrest : primeProductMean P k rest≤restBound)
    (hoff : primeProductMean P k (fun q => if E q then 0 else small q)≤offBound)
    (hmargin : a+largeBound+restBound+offBound≤total) :
    a≤primeProductMean P k (fun q => if E q then small q else 0) := by
  have hm := primeProductMean_mono P k hsplit
  rw [primeProductMean_add,primeProductMean_add,primeProductMean_event_split P k E small] at hm
  linarith

theorem primeProductMean_le_of_even_moment {P : Finset ℕ}
    (hP : ∀p∈P,p.Prime) {k l : ℕ} (hk : k≤P.card) (hl : 0<l)
    (f : ℕ → ℝ) (hf : ∀q∈primeProductSamples P k,0≤f q) {M : ℝ} (hM : 0≤M)
    (hmoment : primeProductMean P k (fun q => (f q)^(2*l))≤M^(2*l)) :
    primeProductMean P k f≤M :=
  le_of_pow_le_pow_left₀ (by omega : 2*l≠0) hM
    ((primeProductMean_pow_le hP hk f hf (2*l)).trans hmoment)

theorem primeProductProbability_exp_lower {P : Finset ℕ}
    (hP : ∀p∈P,p.Prime) {k l : ℕ} (hk : k≤P.card) (hl : 0<l)
    (E : ℕ → Prop) [DecidablePred E] (f : ℕ → ℝ) (C K : ℝ)
    (hmean : 1≤primeProductMean P k (fun q => if E q then f q else 0))
    (hmoment : primeProductMean P k (fun q => (f q)^(2*l))≤
      (Real.exp (C*K))^(2*l)) :
    Real.exp (-(2*C)*K)≤primeProductProbability P k E := by
  have h := primeProductProbability_lower_of_moment hP hk hl E f
    (by norm_num : (0:ℝ)≤1) (Real.exp_pos (C*K)) hmean hmoment
  convert h using 1
  rw [one_pow,one_div,←Real.exp_nat_mul,←Real.exp_neg]
  congr 1
  ring

theorem eventually_witness_expectation_margin :
    ∀ᶠ K : ℝ in atTop,
      1+Real.exp ((7/1000:ℝ)*K)+1+1 ≤ Real.exp ((3/200:ℝ)*K) := by
  have hratio : Tendsto (fun K:ℝ => Real.exp ((8/1000:ℝ)*K)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  filter_upwards [hratio.eventually_ge_atTop 4,eventually_ge_atTop (0:ℝ)] with K hratio hK
  have hlarge : 1≤Real.exp ((7/1000:ℝ)*K) := Real.one_le_exp (by positivity)
  have hm := mul_le_mul_of_nonneg_right hratio (Real.exp_pos ((7/1000:ℝ)*K)).le
  have he : Real.exp ((8/1000:ℝ)*K)*Real.exp ((7/1000:ℝ)*K)=
      Real.exp ((3/200:ℝ)*K) := by rw [←Real.exp_add]; congr 1; ring
  rw [he] at hm
  linarith

theorem exists_primeProduct_event_of_mean_moment {P : Finset ℕ}
    (hP : ∀p∈P,p.Prime) {k l : ℕ} (hk : k≤P.card) (hl : 0<l)
    (E : ℕ → Prop) [DecidablePred E] (f : ℕ → ℝ) (C K : ℝ)
    (hmean : 1≤primeProductMean P k (fun q => if E q then f q else 0))
    (hmoment : primeProductMean P k (fun q => (f q)^(2*l))≤
      (Real.exp (C*K))^(2*l)) :
    ∃q∈primeProductSamples P k,E q :=
  exists_primeProduct_event_of_probability_pos ((Real.exp_pos _).trans_le
    (primeProductProbability_exp_lower hP hk hl E f C K hmean hmoment))

end Ostmann.QuadraticCenter

end

end OAI

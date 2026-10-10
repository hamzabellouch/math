import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualArrayMeanScales
import OAI.NumberTheory.Ostmann.QuadraticCenter.ActualWitnessMomentsBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem witness_family_exponential_moment {Z : ℕ} {K a : ℝ} {l : ℕ}
    (hZ : 0 < Z) (hK : 4000 ≤ K) (hKZ : K ≤ Real.log Z) (hl : 1 ≤ l) (ha : -1 ≤ a) :
    Real.exp (2*(l:ℝ)*(1/4000:ℝ)*K)*(Real.exp (a*K))^l+
      (Z:ℝ)^(-(20*(l:ℝ))) ≤ (Real.exp ((a/2+1/2000)*K))^(2*l) := by
  have hZr : (0:ℝ) < Z := by exact_mod_cast hZ
  have hlr : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hK0 : 0 ≤ K := by linarith
  have hmain : Real.exp (2*(l:ℝ)*(1/4000:ℝ)*K)*(Real.exp (a*K))^l =
      Real.exp ((l:ℝ)*(a+1/2000)*K) := by
    rw [←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring
  have herr : (Z:ℝ)^(-(20*(l:ℝ))) ≤ Real.exp ((l:ℝ)*(a+1/2000)*K) := by
    rw [Real.rpow_def_of_pos hZr]
    apply Real.exp_le_exp.mpr
    have h1 := mul_le_mul_of_nonneg_right hKZ (show 0 ≤ (20:ℝ)*l by positivity)
    have h2 := mul_le_mul_of_nonneg_right ha (show 0 ≤ (l:ℝ)*K by positivity)
    nlinarith
  have htwo : (2:ℝ) ≤ Real.exp ((l:ℝ)*K/2000) := by
    have hh := Real.add_one_le_exp ((l:ℝ)*K/2000)
    have hh' : K ≤ (l:ℝ)*K := by nlinarith
    linarith
  rw [hmain]
  calc
    _ ≤ 2*Real.exp ((l:ℝ)*(a+1/2000)*K) := by linarith
    _ ≤ Real.exp ((l:ℝ)*K/2000)*Real.exp ((l:ℝ)*(a+1/2000)*K) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add,←Real.exp_nat_mul]; congr 1; push_cast; ring

theorem witness_add_one_pow_le {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    (a+1)^n ≤ 2^n*(a^n+1) := by
  rcases le_total a 1 with h | h
  · calc
      _ ≤ (2:ℝ)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ ≤ _ := by have := pow_nonneg ha n; nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n]
  · calc
      _ ≤ (2*a)^n := pow_le_pow_left₀ (by positivity) (by linarith) n
      _ = 2^n*a^n := mul_pow _ _ _
      _ ≤ _ := by have := pow_nonneg (by norm_num : (0:ℝ) ≤ 2) n; nlinarith

theorem primeProductMean_mul_const (P : Finset ℕ) (k : ℕ) (f : ℕ → ℝ) (a : ℝ) :
    primeProductMean P k (fun q => a*f q)=a*primeProductMean P k f := by
  simp only [primeProductMean,←Finset.mul_sum]
  ring

theorem witness_mean_le_of_near {P : Finset ℕ} (hP : ∀p∈P,p.Prime) {k : ℕ}
    (hk : k ≤ P.card) {f g : ℕ → ℝ} {a e : ℝ}
    (hnear : ∀q∈primeProductSamples P k,f q ≤ g q+e)
    (hg : primeProductMean P k g ≤ a) : primeProductMean P k f ≤ a+e := by
  have hm := primeProductMean_mono P k hnear
  rw [primeProductMean_add,primeProductMean_const hP hk] at hm
  exact hm.trans (add_le_add hg (le_refl e))

theorem witness_shifted_moment {P : Finset ℕ} (hP : ∀p∈P,p.Prime) {k l : ℕ}
    (hk : k ≤ P.card) (hl : 1 ≤ l) {f g : ℕ → ℝ} (hf : ∀q∈primeProductSamples P k,0 ≤ f q)
    (hg : ∀q∈primeProductSamples P k,0 ≤ g q) {K : ℝ} (hK : 4 ≤ K)
    (hnear : ∀q∈primeProductSamples P k,f q ≤ g q+1)
    (hm : primeProductMean P k (fun q => (g q)^(2*l)) ≤ (Real.exp K)^(2*l)) :
    primeProductMean P k (fun q => (f q)^(2*l)) ≤ (Real.exp (3*K))^(2*l) := by
  have hp := primeProductMean_mono P k (fun q hq =>
    (pow_le_pow_left₀ (hf q hq) (hnear q hq) (2*l)).trans (witness_add_one_pow_le (hg q hq) (2*l)))
  rw [primeProductMean_mul_const,primeProductMean_add,primeProductMean_const hP hk] at hp
  have hExp : (1:ℝ) ≤ Real.exp K := Real.one_le_exp (by linarith)
  have h4 : (4:ℝ) ≤ Real.exp (2*K) := by linarith [Real.add_one_le_exp (2*K)]
  calc
    _ ≤ (2:ℝ)^(2*l)*((Real.exp K)^(2*l)+1) := hp.trans (by gcongr)
    _ ≤ (4:ℝ)^(2*l)*(Real.exp K)^(2*l) := by
      have he := one_le_pow₀ hExp (n:=2*l)
      have hn : (2:ℝ) ≤ (2:ℝ)^(2*l) := by
        simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ 2*l by omega)
      calc
        _ ≤ (2:ℝ)^(2*l)*(2*(Real.exp K)^(2*l)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ (2:ℝ)^(2*l)*((2:ℝ)^(2*l)*(Real.exp K)^(2*l)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn (by positivity)) (by positivity)
        _ = _ := by rw [←mul_assoc,←mul_pow]; norm_num
    _ ≤ (Real.exp (2*K))^(2*l)*(Real.exp K)^(2*l) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) h4 _) (by positivity)
    _ = _ := by rw [←mul_pow,←Real.exp_add]; congr 2; ring

end Ostmann.QuadraticCenter

end

end OAI

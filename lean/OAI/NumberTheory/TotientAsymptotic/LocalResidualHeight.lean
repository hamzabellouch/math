import OAI.NumberTheory.TotientAsymptotic.LocalPrimeSupport
import OAI.NumberTheory.TotientAsymptotic.PPTLocalValueEnvelope

namespace OAI

/-! A single geometric height controls each residual value and its dyadic layers. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

lemma local_residual_value_height {A : ℝ} (_hA : 0 ≤ A) (L h d : ℕ)
    (hd : 0 < d) :
    pptLocalValueHeight d h (localPrimeHeight A L h) ≤
      localPrimeHeight (A+Real.log d+2) L h := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d:ℝ) := Real.log_nonneg hd1
  let k := h+L+2
  have hk : (h:ℝ)+1 ≤ k := by dsimp [k]; push_cast; linarith
  have hk0 : (1:ℝ) ≤ k := by linarith only [hk,Nat.cast_nonneg (α:=ℝ) h]
  have hr : (1:ℝ) ≤ (rho^k)⁻¹ :=
    (one_le_inv₀ (pow_pos rho_pos _)).mpr (pow_le_one₀ rho_pos.le rho_lt_one.le)
  have ht : (k:ℝ) ≤ (k:ℝ)*(rho^k)⁻¹ := le_mul_of_one_le_right (by positivity) hr
  have hl := Real.log_le_self (show 0 ≤ Real.log (d:ℝ)+(h:ℝ)+1 by positivity)
  unfold pptLocalValueHeight localPrimeHeight
  change A*(k:ℝ)*(rho^k)⁻¹+2+Real.log (Real.log (d:ℝ)+(h:ℝ)+1) ≤
    (A+Real.log (d:ℝ)+2)*(k:ℝ)*(rho^k)⁻¹+2
  have hmul := mul_le_mul_of_nonneg_left (hk0.trans ht) hlogd
  nlinarith only [hl,hk,ht,hmul]

theorem local_residual_value_bound {A : ℝ} (hA : 0 ≤ A)
    (L h d n : ℕ) (hd : 0 < d) (hn : n ≤ h+1)
    (p : Fin n → ℕ) (hp : ∀ i,(p i).Prime)
    (hcoords : ∀ i,B (p i) ≤ localPrimeHeight A L h) :
    ((d*(∏ i,p i).totient:ℕ):ℝ) ≤
      Real.exp (Real.exp (localPrimeHeight (A+Real.log d+2) L h)) := by
  have hh := ppt_local_prime_product_value_bound hd
    (show 0 ≤ localPrimeHeight A L h from (by norm_num : (0:ℝ)≤2).trans
      (localPrimeHeight_ge_two hA L h)) hn p hp hcoords
  exact hh.trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr
    (local_residual_value_height hA L h d hd)))

theorem local_residual_log_bound {A : ℝ} (hA : 0 < A) (L : ℕ) :
    ∃ D : ℝ,0 < D ∧ ∀ᶠ h : ℕ in atTop,∀ z : ℝ,
      256 ≤ z → z ≤ Real.exp (Real.exp (localPrimeHeight A L h)) →
      Real.log (B z+4) ≤ D*h := by
  obtain ⟨D,hD,hbound⟩ := localPrimeHeight_log_bound hA L
  refine ⟨D,hD,?_⟩
  filter_upwards [hbound] with h hh
  intro z hz hzu
  have hz1 : 1 < z := by linarith only [hz]
  have hB := Real.log_le_log (Real.log_pos hz1)
    (Real.log_le_log (zero_lt_one.trans hz1) hzu)
  simp only [Real.log_exp] at hB
  change B z ≤ localPrimeHeight A L h at hB
  have hU := localPrimeHeight_ge_two hA.le L h
  have harg : B z+4 ≤ 6*localPrimeHeight A L h := by linarith only [hB,hU]
  have hB0 : 0 ≤ B z := by
    have he : Real.exp 1 ≤ z := (show Real.exp 1 ≤ 256 by
      have hh := Real.exp_one_lt_d9
      linarith).trans hz
    have hh := Real.log_le_log (Real.exp_pos 1) he
    simp only [Real.log_exp] at hh
    exact Real.log_nonneg hh
  exact (Real.log_le_log (by linarith only [hB0]) harg).trans hh

end TotientAsymptotic

end

end OAI

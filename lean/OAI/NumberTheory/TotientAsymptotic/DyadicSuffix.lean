import OAI.NumberTheory.TotientAsymptotic.CollisionTail

namespace OAI

/-! The integral comparison for reciprocal-weighted dyadic collision slices. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma suffix_power_sum_le {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, ((n+N+1 : ℕ) : ℝ)^(-1-σ)) ≤ (N : ℝ)^(-σ)/σ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : AntitoneOn (fun t : ℝ => t^(-1-σ)) (Set.Ici (N : ℝ)) := by
    intro s hs t _ hst
    exact Real.rpow_le_rpow_of_nonpos (hNR.trans_le hs) hst (by linarith)
  have hint := integrableOn_Ioi_rpow_of_lt (a := -1-σ) (by linarith) hNR
  have hh := ha.tsum_comp_add_le_integral N hint (fun t ht => Real.rpow_nonneg (hNR.trans ht).le _)
  rw [integral_Ioi_rpow_of_lt (by linarith : -1-σ < -1) hNR] at hh
  convert hh using 1; ring_nf

def dyadicSuffixWeight (σ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-σ*Real.log ((n : ℝ)*Real.log 2))/((n : ℝ)*Real.log 2)

lemma dyadicSuffixWeight_eq {σ : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    dyadicSuffixWeight σ n = (Real.log 2)^(-1-σ)*(n : ℝ)^(-1-σ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : 0 < (n : ℝ)*Real.log 2 := mul_pos hnR htwo
  rw [← Real.mul_rpow htwo.le hnR.le, mul_comm (Real.log 2), Real.rpow_def_of_pos hp]
  have he : Real.log ((n : ℝ)*Real.log 2)*(-1-σ) =
      -σ*Real.log ((n : ℝ)*Real.log 2)-Real.log ((n : ℝ)*Real.log 2) := by ring
  rw [he, Real.exp_sub, Real.exp_log hp]
  rfl

lemma dyadic_suffix_summable {σ : ℝ} (hσ : 0 < σ) (N : ℕ) :
    Summable (fun n : ℕ => dyadicSuffixWeight σ (n+N+1)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ)^(-1-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht := (hs.comp_injective (fun n m (he : n+N+1=m+N+1) => by omega)).mul_left
    ((Real.log 2)^(-1-σ))
  convert ht using 1
  ext n
  exact dyadicSuffixWeight_eq (by omega)

lemma dyadic_suffix_weight_sum {σ : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, dyadicSuffixWeight σ (n+N+1)) ≤
      ((N : ℝ)*Real.log 2)^(-σ)/(σ*Real.log 2) := by
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he (n : ℕ) : dyadicSuffixWeight σ (n+N+1) =
      (Real.log 2)^(-1-σ)*((n+N+1 : ℕ) : ℝ)^(-1-σ) :=
    dyadicSuffixWeight_eq (by omega)
  simp_rw [he]
  rw [tsum_mul_left]
  apply (mul_le_mul_of_nonneg_left (suffix_power_sum_le hσ hN)
    (Real.rpow_nonneg htwo.le _)).trans_eq
  rw [Real.mul_rpow hnR.le htwo.le,
    show -1-σ = -1+(-σ) by ring, Real.rpow_add htwo,
    Real.rpow_neg_one]
  field_simp

/-- In logarithmic height the total reciprocal collision mass decays like
`exp (-σ B)/σ`. No factor `exp B` is lost in the dyadic summation. -/
theorem dyadic_suffix_exponential_bound {σ B : ℝ} (hσ : 0 < σ) {N : ℕ} (hN : 1 ≤ N)
    (hNB : Real.exp B ≤ (N : ℝ)*Real.log 2) :
    (∑' n : ℕ, dyadicSuffixWeight σ (n+N+1)) ≤
      Real.exp (-σ*B)/(σ*Real.log 2) := by
  apply (dyadic_suffix_weight_sum hσ hN).trans
  apply div_le_div_of_nonneg_right _ (mul_pos hσ (Real.log_pos (by norm_num))).le
  have hh := Real.rpow_le_rpow_of_nonpos (Real.exp_pos B) hNB (by linarith : -σ ≤ 0)
  rw [Real.rpow_def_of_pos (Real.exp_pos B), Real.log_exp] at hh
  simpa only [mul_comm] using hh

end TotientAsymptotic

end

end OAI

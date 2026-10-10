import OAI.NumberTheory.TotientAsymptotic.FordPolynomialBudget
import OAI.NumberTheory.TotientAsymptotic.FordRawCount

namespace OAI

/-! The assembled counting bound has exactly the published Ford exponents. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma ford_comparison_budget {b D r : ℕ} {y S A M C K : ℝ} {Y U : ℕ → ℝ}
    (hp : FordComparisonParameters b y S D r Y U)
    (hy : 1 < y) (hA : 0 ≤ A) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hK : 1 ≤ K) (hAK : 216*A ≤ K) (hMK : M ≤ K) (hCK : C ≤ K) :
    ((216*A)*(y/(D*r:ℕ))*(B y)^5/(Real.log y)^2/Real.log (Y 1))*
      (∏ k ∈ Finset.Icc 2 b,fordBandCost C k y S Y U)*
      (M*(b+1:ℝ)^D.primeFactorsList.length*
        (Real.log (Y b))^(20*(b:ℝ)*Real.log b+1)) ≤
    fordComparisonBound K b y S D r Y U := by
  classical
  let P := ∏ k ∈ Finset.Icc 2 b,C*(k:ℝ)^2*(B y)^2
  let Q := ∏ k ∈ Finset.Icc 2 b,Real.exp (fordBandCap k y S Y*(Real.log k+1))/
    (Real.log (U (k-1)))^2
  let Z := (Real.log (Y b))^(20*(b:ℝ)*Real.log b+1)
  have hBy : 1 ≤ B y := by simpa only [hp.2.1] using ford_cutoff_B_one_le hp (k:=0) (by omega)
  have hy0 : 0 ≤ y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hY : 1 < Y 1 := by linarith [ford_cutoff_two_le hp hp.1]
  have hU (j : ℕ) (hj : j ∈ Finset.Icc 1 (b-1)) : 1 < U j := by
    have hjb : j < b := by obtain ⟨_,_⟩ := Finset.mem_Icc.mp hj; omega
    have hh := hp.2.2.2.2.1 j (Finset.mem_range.mpr hjb)
    linarith [ford_cutoff_two_le hp (show j+1 ≤ b by omega)]
  have hlogY : 0 < Real.log (Y 1) := Real.log_pos hY
  have hlogYb : 0 < Real.log (Y b) := Real.log_pos (by linarith [ford_cutoff_two_le hp (k:=b) le_rfl])
  have hQ : 0 ≤ (Real.log (Y 1))⁻¹*Q := by dsimp [Q]; positivity
  have hPbound : (216*A)*M*(B y)^5*P ≤ (K*B y)^(6*b) := by
    have hmono : P ≤ ∏ k ∈ Finset.Icc 2 b,K*(k:ℝ)^2*(B y)^2 := by
      apply Finset.prod_le_prod₀
      · intro k _; positivity
      · intro k _
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCK (sq_nonneg _)) (sq_nonneg _)
    exact (mul_le_mul_of_nonneg_left hmono (by positivity)).trans
      (ford_polynomial_budget hp.1 hBy (ford_band_count_le hp) hK hA hM hAK hMK (by linarith))
  have hQbound := ford_logarithmic_product_bound (y:=y) (S:=S) Y U hp.1 hy (by linarith)
    (by linarith [(ford_scale_bounds hp).2])
    (by linarith [ford_cutoff_B_one_le hp (k:=b) le_rfl]) hY hU
  have hprod : (∏ k ∈ Finset.Icc 2 b,fordBandCost C k y S Y U)=P*Q := by
    simp_rw [ford_band_cost_split]
    exact Finset.prod_mul_distrib
  have hinv : (Real.log y)^(-2:ℝ)=((Real.log y)^2)⁻¹ := by
    rw [Real.rpow_neg hlog.le]
    norm_num only [Real.rpow_ofNat]
  have heq :
      ((216*A)*(y/(D*r:ℕ))*(B y)^5/(Real.log y)^2/Real.log (Y 1))*
        (∏ k ∈ Finset.Icc 2 b,fordBandCost C k y S Y U)*
        (M*(b+1:ℝ)^D.primeFactorsList.length*Z)=
      (y/(D*r:ℕ))*((216*A)*M*(B y)^5*P)*
        (b+1:ℝ)^D.primeFactorsList.length*Z*(Real.log y)^(-2:ℝ)*
        ((Real.log (Y 1))⁻¹*Q) := by
    rw [hprod,hinv]
    ring
  change _ ≤ _ at hQbound
  rw [heq]
  have hout : 0 ≤ (y/(D*r:ℕ))*(b+1:ℝ)^D.primeFactorsList.length*Z*(Real.log y)^(-2:ℝ) := by
    dsimp [Z]; positivity
  have hh := mul_le_mul hPbound hQbound hQ (by positivity : 0 ≤ (K*B y)^(6*b))
  have hh' := mul_le_mul_of_nonneg_left hh hout
  convert hh' using 1
  · ring
  · unfold fordComparisonBound
    have hpowe : (Real.log y)^(-2+(∑ j ∈ Finset.Icc 1 (b-1),a j*(B (Y j)/B y))+
        comparisonError b y S Y U)=
        (Real.log y)^(-2:ℝ)*(Real.log y)^((∑ j ∈ Finset.Icc 1 (b-1),a j*(B (Y j)/B y))+
          comparisonError b y S Y U) := by
      rw [← Real.rpow_add hlog]
      congr 1
      ring
    rw [hpowe]
    push_cast
    dsimp [Z]
    ring

lemma ford_comparison_budget_one {D r : ℕ} {y S A M K : ℝ} {Y U : ℕ → ℝ}
    (hp : FordComparisonParameters 1 y S D r Y U) (hy : 1 < y)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hK : 1 ≤ K)
    (hAK : 216*A ≤ K) (hMK : M ≤ K) :
    ((216*A)*(y/(D*r:ℕ))*(B y)^5/(Real.log y)^2/Real.log (Y 1))*
      (M*(2:ℝ)^D.primeFactorsList.length*(Real.log (Y 1))^2) ≤
    fordComparisonBound K 1 y S D r Y U := by
  have hBy : 1 ≤ B y := by simpa only [hp.2.1] using ford_cutoff_B_one_le hp (k:=0) (by decide)
  have hy0 : 0 ≤ y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hlogY : 0 < Real.log (Y 1) := Real.log_pos (by linarith [ford_cutoff_two_le hp hp.1])
  have hpoly : (216*A)*M*(B y)^5 ≤ (K*B y)^6 := by
    simpa using ford_polynomial_budget (b:=1) (by decide) hBy (by simpa using hBy) hK hA hM hAK hMK (by linarith)
  have hfac : 0 ≤ (y/(D*r:ℕ))*(2:ℝ)^D.primeFactorsList.length*
      Real.log (Y 1)*((Real.log y)^2)⁻¹ := by positivity
  have hh := mul_le_mul_of_nonneg_left hpoly hfac
  have hinv : (Real.log y)^(-2:ℝ)=((Real.log y)^2)⁻¹ := by
    rw [Real.rpow_neg hlog.le]
    norm_num only [Real.rpow_ofNat]
  convert hh using 1
  · field_simp
  · norm_num [fordComparisonBound,comparisonError,hinv]
    ring

end TotientAsymptotic

end

end OAI

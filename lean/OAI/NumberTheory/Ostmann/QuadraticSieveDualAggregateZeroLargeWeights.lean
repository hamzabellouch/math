import OAI.NumberTheory.Ostmann.QuadraticSieveDualAggregateNormBlocks
import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrectionRows

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve
open ComplexConjugate MeasureTheory
open scoped SchwartzMap ArithmeticFunction.Moebius

def dualZeroCutoffWeight (Z : ℂ) (X : ℕ → ℝ) (d v : ℕ) : ℂ :=
  Z*(if (d:ℝ)≤X v then (μ d:ℂ) else 0)
def dualLargeCutoffWeight (Z : ℂ) (X : ℕ → ℝ) (d v : ℕ) : ℂ :=
  Z*(if X v<(d:ℝ) then (μ d:ℂ) else 0)

lemma dualZeroCutoffWeight_norm (Z : ℂ) (X : ℕ → ℝ) (d v : ℕ) :
    ‖dualZeroCutoffWeight Z X d v‖≤‖Z‖ := by
  unfold dualZeroCutoffWeight
  split_ifs
  · rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_moebius_complex_le_one d) (norm_nonneg Z)
  · simp
lemma dualLargeCutoffWeight_norm (Z : ℂ) (X : ℕ → ℝ) (d v : ℕ) :
    ‖dualLargeCutoffWeight Z X d v‖≤‖Z‖ := by
  unfold dualLargeCutoffWeight
  split_ifs
  · rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (norm_moebius_complex_le_one d) (norm_nonneg Z)
  · simp
lemma dualZeroCutoffWeight_support (Z : ℂ) (X : ℕ → ℝ) (d v : ℕ)
    (h : dualZeroCutoffWeight Z X d v≠0) : (d:ℝ)≤X v := by
  by_contra hn
  simp only [dualZeroCutoffWeight,ite_eq_right hn,mul_zero] at h
  exact h rfl
lemma dualLargeCutoffWeight_support (Z : ℂ) (X : ℕ → ℝ) (d v : ℕ)
    (h : dualLargeCutoffWeight Z X d v≠0) : X v<(d:ℝ) := by
  by_contra hn
  simp only [dualLargeCutoffWeight,ite_eq_right hn,mul_zero] at h
  exact h rfl

lemma dualWindowLower_le_upper (M H : ℝ) {T : ℝ} (hT : 1≤T) (e v : ℕ) :
    dualWindowLower M H T e v≤dualWindowUpper M H T e v := by
  unfold dualWindowLower dualWindowUpper
  apply (div_le_iff₀ (show 0<2*T by linarith)).mpr
  have h4 : 1≤(2*T)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_right h4
    (Real.sqrt_nonneg ((e:ℝ)*H^2/(M*squarefreeDyadicBase v)))
  nlinarith

lemma dual_correction_scalar_norm (e : ℕ) (Z : ℂ) :
    ‖-(1/2:ℂ)*(μ e:ℂ)*Z‖≤‖Z‖ := by
  rw [norm_mul,norm_mul]
  have hh : ‖-(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hh]
  calc
    _ ≤ (1/2:ℝ)*1*‖Z‖ := by gcongr; exact norm_moebius_complex_le_one e
    _ ≤ _ := by linarith [norm_nonneg Z]

theorem dualZeroDivisorRows_eq_weighted (W : 𝓢(ℝ,ℂ)) (M : ℝ) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (e : ℕ) (s : ℤ) (v : ℕ) (X : ℕ → ℕ → ℝ) :
    dualZeroDivisorRows W M N S a e s v X =
      ∑ d ∈ Finset.Icc 1 (N^2), ((M/e:ℝ):ℂ)*
        dualZeroCutoffWeight (-(1/2:ℂ)*(μ e:ℂ)*dualSignedSquareWeight W s 0) (X e) d v*
          gaussProductDivisorJacobiRow S S a (fun n => conj (a n)) ((e:ℤ)*s) d (v:ℤ) := by
  unfold dualZeroDivisorRows
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  unfold dualZeroCutoffWeight
  ring

theorem dualLargeDivisorRows_eq_weighted (W : 𝓢(ℝ,ℂ)) (M : ℝ) (N : ℕ)
    (S : Finset ℕ) (a : ℕ → ℂ) (e : ℕ) (s : ℤ) (v : ℕ) (X : ℕ → ℕ → ℝ) :
    dualLargeDivisorRows W M N S a e s v X =
      ∑ d ∈ Finset.Icc 1 (N^2), ((Real.sqrt (M/((e:ℝ)*v))/(d:ℝ):ℝ):ℂ)*
        dualLargeCutoffWeight (-(1/2:ℂ)*(μ e:ℂ)*(∫x:ℝ,dualSignedSquareWeight W s x)) (X e) d v*
          gaussProductDivisorJacobiRow S S (sqrtCoefficients a)
            (sqrtCoefficients (fun n => conj (a n))) ((e:ℤ)*s) d (v:ℤ) := by
  unfold dualLargeDivisorRows
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  unfold dualLargeCutoffWeight
  split_ifs <;> push_cast <;> ring

end Ostmann.QuadraticSieve

end

end OAI

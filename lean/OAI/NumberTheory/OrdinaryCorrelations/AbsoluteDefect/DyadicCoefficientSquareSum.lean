import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.E
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BinErrorWidth

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
open ArithmeticFunction

namespace OrdinaryChainScales
open OrdinaryCorrelations SourcePrimeFactor OrdinaryDirichletMeanSquare
open Finset Filter MeasureTheory

lemma dyadic_coefficient_square_sum {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {X : ℕ} (hX : 0<X) :
    (∑n∈Ioc X (2*X),‖characterModulation f χ n/(n:ℂ)‖^2)≤(X:ℝ)⁻¹ := by
  have hXr : (0:ℝ)<X := by exact_mod_cast hX
  calc
    _ ≤ ∑n∈Ioc X (2*X),((X:ℝ)⁻¹)^2 := by
      apply sum_le_sum
      intro n hn
      have hnX : (X:ℝ)≤n := by exact_mod_cast (mem_Ioc.mp hn).1.le
      have hnpos : (0:ℝ)<n := hXr.trans_le hnX
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      rw [norm_div,Complex.norm_natCast]
      exact (div_le_div_of_nonneg_right (characterModulation_bound hf χ n) hnpos.le).trans
        (by simpa only [one_div] using inv_le_inv₀ hnpos hXr |>.2 hnX)
    _ = (X:ℝ)⁻¹ := by
      simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul]
      have he : 2*X-X=X := by omega
      rw [he]
      field_simp

lemma dyadic_continuous (f : ℕ→ℂ) {d : ℕ} (χ : DirichletCharacter ℂ d) (X : ℕ) :
    Continuous (dyadicCharacterPolynomial f χ X) := by
  unfold dyadicCharacterPolynomial polynomial phase
  fun_prop

noncomputable def gaussianEnergyConstant : ℝ := 16*gaussianConstant*Real.exp (1/4)

lemma gaussianEnergyConstant_nonneg : 0≤gaussianEnergyConstant := by
  unfold gaussianEnergyConstant gaussianConstant
  positivity

lemma dyadic_gaussian_uniform {f : ℕ→ℂ} (hf : OneBounded f)
    {d : ℕ} (χ : DirichletCharacter ℂ d) {X : ℕ} (hX : 0<X)
    {D : ℝ} (hD : 1≤D) :
    Integrable (fun t : ℝ=>gaussian (D*t/(4*(X:ℝ)))*‖dyadicCharacterPolynomial f χ X t‖^2) ∧
    (∫t : ℝ,gaussian (D*t/(4*(X:ℝ)))*‖dyadicCharacterPolynomial f χ X t‖^2)≤gaussianEnergyConstant := by
  have hXr : (0:ℝ)<X := by exact_mod_cast hX
  have hDp : 0<D := by linarith
  have hT : 0<4*(X:ℝ)/D := by positivity
  have he (t : ℝ) : D*t/(4*(X:ℝ))=t/(4*(X:ℝ)/D) := by field_simp
  simp_rw [he]
  refine ⟨logarithmic_scaled_integrable _ _ hT.ne',?_⟩
  have hh := logarithmic_scaled_energy (Ioc X (2*X))
    (fun n=>characterModulation f χ n/(n:ℂ))
    (N:=2*(X:ℝ)) (T:=4*(X:ℝ)/D) (by positivity) hT (by
      intro n hn
      obtain ⟨hn,hhi⟩ := mem_Ioc.mp hn
      constructor
      · exact_mod_cast (hX.trans hn)
      · exact_mod_cast hhi)
  have hcoef := dyadic_coefficient_square_sum hf χ hX
  have hnon : 0≤gaussianConstant*Real.exp (1/4)*(2*(4*(X:ℝ)/D)+4*(2*(X:ℝ))) := by
    unfold gaussianConstant
    positivity
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hcoef hnon)
  apply hh'.trans
  have hdiv : 4*(X:ℝ)/D≤4*(X:ℝ) := div_le_self (by positivity) hD
  have hlin := mul_le_mul_of_nonneg_left (show 2*(4*(X:ℝ)/D)+4*(2*(X:ℝ))≤16*(X:ℝ) by linarith)
    (show 0≤gaussianConstant*Real.exp (1/4) by unfold gaussianConstant; positivity)
  have hb := mul_le_mul_of_nonneg_right hlin (inv_nonneg.mpr hXr.le)
  convert hb using 1
  unfold gaussianEnergyConstant
  field_simp

lemma gaussian_tail_geometric (K : ℕ) {x : ℝ} (hx : 2*((K:ℝ)+1)≤|x|) :
    gaussian x≤(1/2:ℝ)^K*gaussian (x/2) := by
  have hK : 0≤(K:ℝ) := Nat.cast_nonneg K
  have hsq : (2*((K:ℝ)+1))^2≤x^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0≤2*((K:ℝ)+1)) hx 2
    simpa only [sq_abs] using hh
  have hex : -x^2≤ -(K:ℝ)-(x/2)^2 := by nlinarith only [hsq,hK,sq_nonneg (K:ℝ)]
  have hl : Real.log 2≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh]
  have hklog := mul_le_mul_of_nonneg_left hl hK
  have hExp : Real.exp (-(K:ℝ))≤(1/2:ℝ)^K := by
    apply (Real.exp_le_exp.mpr (show -(K:ℝ)≤ -(K:ℝ)*Real.log 2 by nlinarith only [hklog])).trans_eq
    rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [div_pow,one_pow,one_div]
  calc
    gaussian x ≤ Real.exp (-(K:ℝ))*gaussian (x/2) := by
      unfold gaussian
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr hex
    _ ≤ _ := mul_le_mul_of_nonneg_right hExp (gaussian_nonneg _)

lemma gaussian_split_bound (F : ℝ→ℂ) (hF : Continuous F) {c T : ℝ} (hc : 0<c)
    (hT : 0≤T) (K : ℕ) (hcut : 2*((K:ℝ)+1)≤c*T)
    (hi : Integrable (fun t : ℝ=>gaussian (c*t/2)*‖F t‖^2)) :
    Integrable (fun t : ℝ=>gaussian (c*t)*‖F t‖^2) ∧
    (∫t : ℝ,gaussian (c*t)*‖F t‖^2)≤
      (∫t in -T..T,‖F t‖^2)+(1/2:ℝ)^K*(∫t : ℝ,gaussian (c*t/2)*‖F t‖^2) := by
  have hlow : Integrable (Set.Icc (-T) T |>.indicator (fun t=>‖F t‖^2)) := by
    exact (hF.norm.pow 2).integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hbound (t : ℝ) : gaussian (c*t)*‖F t‖^2≤
      (Set.Icc (-T) T |>.indicator (fun t=>‖F t‖^2)) t+
        (1/2:ℝ)^K*(gaussian (c*t/2)*‖F t‖^2) := by
    by_cases ht : t∈Set.Icc (-T) T
    · rw [Set.indicator_of_mem ht]
      have hg : gaussian (c*t)≤1 := by
        unfold gaussian
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
      have hh := mul_le_mul_of_nonneg_right hg (sq_nonneg ‖F t‖)
      have hn : 0≤(1/2:ℝ)^K*(gaussian (c*t/2)*‖F t‖^2) := by
        have := gaussian_nonneg (c*t/2)
        positivity
      nlinarith only [hh,hn]
    · rw [Set.indicator_of_notMem ht,zero_add]
      have ht' : T < |t| := lt_of_not_ge (by
        intro hh
        exact ht (abs_le.mp hh))
      have hx : 2*((K:ℝ)+1)≤|c*t| := by
        rw [abs_mul,abs_of_pos hc]
        exact hcut.trans (mul_le_mul_of_nonneg_left ht'.le hc.le)
      have hh := mul_le_mul_of_nonneg_right (gaussian_tail_geometric K hx) (sq_nonneg ‖F t‖)
      nlinarith only [hh]
  have hdom := hlow.add (hi.const_mul ((1/2:ℝ)^K))
  have hint : Integrable (fun t : ℝ=>gaussian (c*t)*‖F t‖^2) := by
    apply Integrable.mono' hdom (by unfold gaussian; fun_prop)
    filter_upwards [] with t
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (gaussian_nonneg _) (sq_nonneg _))]
    exact hbound t
  refine ⟨hint,?_⟩
  have hh := integral_mono hint hdom hbound
  simp only [Pi.add_apply] at hh
  rw [integral_add hlow (hi.const_mul ((1/2:ℝ)^K)),MeasureTheory.integral_const_mul,
    MeasureTheory.integral_indicator measurableSet_Icc] at hh
  simpa only [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by linarith : -T≤T)] using hh

end OrdinaryChainScales

end

end OAI

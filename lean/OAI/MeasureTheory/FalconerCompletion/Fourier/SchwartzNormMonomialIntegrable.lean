import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.ImaginaryExponential
import OAI.MeasureTheory.FalconerCompletion.Fourier.QuadraticKernel

namespace OAI

/-! Fourier kernels and oscillatory estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open MeasureTheory Set
open scoped FourierTransform SchwartzMap
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma schwartz_norm_monomialND_integrable (φ : 𝓢(V,ℂ)) (p : ℕ) :
    Integrable (fun x : V => (‖x‖:ℂ)^p * φ x) := by
  apply (φ.integrable_pow_mul volume p).mono' (by fun_prop)
  filter_upwards with x
  simp [norm_pow]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma imaginaryTaylor_quadraticND_eq (φ : 𝓢(V,ℂ)) (n : ℕ) (β : ℝ) :
    (fun x => imaginaryTaylor n (β*‖x‖^2)*φ x) =
      fun x : V => ∑ k ∈ Finset.range (n+1),
        ((((k.factorial:ℝ)⁻¹*β^k):ℝ):ℂ)*Complex.I^k * ((‖x‖:ℂ)^(2*k)*φ x) := by
  funext x
  unfold imaginaryTaylor
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,mul_pow,pow_mul]
  ring

lemma imaginaryTaylor_quadraticND_integrable (φ : 𝓢(V,ℂ)) (n : ℕ) (β : ℝ) :
    Integrable (fun x => imaginaryTaylor n (β*‖x‖^2) * φ x) := by
  rw [imaginaryTaylor_quadraticND_eq]
  apply integrable_finsetSum
  intro k _
  exact (schwartz_norm_monomialND_integrable φ (2*k)).const_mul _

lemma imaginaryExponential_quadraticND_integrable (φ : 𝓢(V,ℂ)) (β : ℝ) :
    Integrable (fun x => imaginaryExponential (β*‖x‖^2)*φ x) := by
  apply φ.integrable.norm.mono' (by unfold imaginaryExponential; fun_prop)
  filter_upwards with x
  have h := imaginaryExponential_derivative_norm 0 (β*‖x‖^2)
  simp only [iteratedDeriv_zero] at h
  rw [norm_mul,h,one_mul]

lemma quadraticND_taylor_integral_bound (φ : 𝓢(V,ℂ)) (n : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    ‖(∫ x, imaginaryExponential (β*‖x‖^2)*φ x) -
        (∫ x, imaginaryTaylor n (β*‖x‖^2)*φ x)‖ ≤
      (β^(n+1)/(n.factorial:ℝ)) * ∫ x : V, ‖x‖^(2*(n+1))*‖φ x‖ := by
  rw [← integral_sub (imaginaryExponential_quadraticND_integrable φ β)
    (imaginaryTaylor_quadraticND_integrable φ n β),← integral_const_mul]
  apply norm_integral_le_of_norm_le
    ((φ.integrable_pow_mul volume (2*(n+1))).const_mul _) _
  filter_upwards with x
  rw [← sub_mul,norm_mul]
  have ht : 0 ≤ β*‖x‖^2 := mul_nonneg hβ (sq_nonneg ‖x‖)
  calc
    _ ≤ ((β*‖x‖^2)^(n+1)/(n.factorial:ℝ))*‖φ x‖ :=
      mul_le_mul_of_nonneg_right (imaginaryExponential_taylor_bound n ht) (norm_nonneg _)
    _ = _ := by rw [pow_mul,mul_pow]; ring

lemma imaginaryTaylor_quadraticND_integral (φ : 𝓢(V,ℂ)) (n : ℕ) (β : ℝ) :
    (∫ x, imaginaryTaylor n (β*‖x‖^2)*φ x) =
      ∑ k ∈ Finset.range (n+1),
        ((((k.factorial:ℝ)⁻¹*β^k):ℝ):ℂ)*Complex.I^k * ∫ x : V, (‖x‖:ℂ)^(2*k)*φ x := by
  rw [imaginaryTaylor_quadraticND_eq,integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    exact integral_const_mul _ _
  · intro k _
    exact (schwartz_norm_monomialND_integrable φ (2*k)).const_mul _

noncomputable def quadraticExpansionND (φ : 𝓢(V,ℂ)) (n : ℕ) (b : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1),
    ((((k.factorial:ℝ)⁻¹*(Real.pi^2/b)^k):ℝ):ℂ)*Complex.I^k *
      ∫ ξ : V, (‖ξ‖:ℂ)^(2*k)*𝓕⁻ φ ξ

theorem quadratic_stationaryND_expansion {b : ℝ} (hb : 0 < b) (φ : 𝓢(V,ℂ)) (n : ℕ) :
    ‖(∫ x : V, Complex.exp (-((b:ℂ)*Complex.I)*(‖x‖:ℂ)^2)*φ x) -
      fresnelCoefficientND V b * quadraticExpansionND φ n b‖ ≤
    (Real.pi/b)^(Module.finrank ℝ V/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ)) *
      ∫ ξ : V, ‖ξ‖^(2*(n+1))*‖𝓕⁻ φ ξ‖ := by
  have he : (∫ x, imaginaryTaylor n ((Real.pi^2/b)*‖x‖^2)*𝓕⁻ φ x) =
      quadraticExpansionND φ n b := imaginaryTaylor_quadraticND_integral _ _ _
  rw [quadratic_stationaryND_identity hb φ]
  change ‖fresnelCoefficientND V b * _ - fresnelCoefficientND V b * _‖ ≤ _
  rw [← mul_sub,norm_mul,fresnelCoefficientND_norm hb,← he]
  have hh := quadraticND_taylor_integral_bound (𝓕⁻ φ) n (div_nonneg (sq_nonneg Real.pi) hb.le)
  calc
    _ ≤ (Real.pi/b)^(Module.finrank ℝ V/2:ℝ) * (((Real.pi^2/b)^(n+1)/(n.factorial:ℝ)) *
      ∫ ξ : V, ‖ξ‖^(2*(n+1))*‖𝓕⁻ φ ξ‖) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open MeasureTheory Set
open scoped FourierTransform SchwartzMap
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

noncomputable def fourierDerivativeND_L1 (φ : 𝓢(V,ℂ)) (n : ℕ) : ℝ :=
  2^n * ∑ j ∈ Finset.range (n+1), ∫ x : V, ‖iteratedFDeriv ℝ j φ x‖

lemma fourierDerivativeND_L1_nonneg (φ : 𝓢(V,ℂ)) (n : ℕ) :
    0 ≤ fourierDerivativeND_L1 φ n := by
  unfold fourierDerivativeND_L1
  positivity

lemma schwartz_fourierND_weighted_pointwise (φ : 𝓢(V,ℂ)) (n : ℕ) (ξ : V) :
    ‖ξ‖^n * ‖𝓕 φ ξ‖ ≤ fourierDerivativeND_L1 φ n := by
  have hh := Real.pow_mul_norm_iteratedFDeriv_fourier_le (f := (φ : V → ℂ))
    (K := (⊤ : ℕ∞)) (N := (⊤ : ℕ∞)) (φ.smooth ⊤)
    (fun k j _ _ => φ.integrable_pow_mul_iteratedFDeriv volume k j)
    (k := 0) (n := n) (by simp) (by simp) ξ
  rw [Finset.sum_product] at hh
  simpa [fourierDerivativeND_L1,norm_iteratedFDeriv_zero,SchwartzMap.fourier_coe] using hh

lemma schwartz_fourierND_weighted_decay (φ : 𝓢(V,ℂ)) (n m : ℕ) (ξ : V) :
    ‖ξ‖^n * ‖𝓕 φ ξ‖ ≤
      (2^m*(fourierDerivativeND_L1 φ n+fourierDerivativeND_L1 φ (n+m))) *
        ((1+‖ξ‖)^m)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1+‖ξ‖)^m)).mpr
  by_cases hx : ‖ξ‖ ≤ 1
  · have hp : (1+‖ξ‖)^m ≤ (2:ℝ)^m := pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ ≤ (‖ξ‖^n*‖𝓕 φ ξ‖)*2^m := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ fourierDerivativeND_L1 φ n*2^m :=
        mul_le_mul_of_nonneg_right (schwartz_fourierND_weighted_pointwise φ n ξ) (by positivity)
      _ ≤ _ := by nlinarith [fourierDerivativeND_L1_nonneg φ (n+m),pow_nonneg (by norm_num : (0:ℝ)≤2) m]
  · have hx' : 1 ≤ ‖ξ‖ := (lt_of_not_ge hx).le
    have hp : (1+‖ξ‖)^m ≤ (2*‖ξ‖)^m := pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ ≤ (‖ξ‖^n*‖𝓕 φ ξ‖)*(2*‖ξ‖)^m := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = 2^m*(‖ξ‖^(n+m)*‖𝓕 φ ξ‖) := by rw [mul_pow,pow_add]; ring
      _ ≤ 2^m*fourierDerivativeND_L1 φ (n+m) :=
        mul_le_mul_of_nonneg_left (schwartz_fourierND_weighted_pointwise φ (n+m) ξ) (by positivity)
      _ ≤ _ := by nlinarith [fourierDerivativeND_L1_nonneg φ n,pow_nonneg (by norm_num : (0:ℝ)≤2) m]

lemma schwartz_fourierND_moment_bound (φ : 𝓢(V,ℂ)) (n : ℕ) {m : ℕ}
    (hm : Module.finrank ℝ V < m) :
    (∫ ξ : V, ‖ξ‖^n*‖𝓕 φ ξ‖) ≤
      (2^m*(fourierDerivativeND_L1 φ n+fourierDerivativeND_L1 φ (n+m))) *
        ∫ ξ : V, ((1+‖ξ‖)^m)⁻¹ := by
  have hi : Integrable (fun ξ : V => ((1+‖ξ‖)^m)⁻¹) := by
    convert integrable_one_add_norm (E := V) (μ := volume)
      (show (Module.finrank ℝ V:ℝ) < (m:ℝ) by exact_mod_cast hm) using 1
    ext ξ
    simp [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1+‖ξ‖)]
  rw [← integral_const_mul]
  exact integral_mono ((𝓕 φ).integrable_pow_mul volume n) (hi.const_mul _)
    (schwartz_fourierND_weighted_decay φ n m)

lemma schwartz_inverseND_moment_bound (φ : 𝓢(V,ℂ)) (n : ℕ) {m : ℕ}
    (hm : Module.finrank ℝ V < m) :
    (∫ ξ : V, ‖ξ‖^n*‖𝓕⁻ φ ξ‖) ≤
      (2^m*(fourierDerivativeND_L1 φ n+fourierDerivativeND_L1 φ (n+m))) *
        ∫ ξ : V, ((1+‖ξ‖)^m)⁻¹ := by
  have hpoint (ξ : V) : 𝓕⁻ φ ξ = 𝓕 φ (-ξ) := rfl
  simp_rw [hpoint]
  have he := integral_neg_eq_self (fun ξ : V => ‖ξ‖^n*‖𝓕 φ ξ‖) volume
  simp only [norm_neg] at he
  rw [he]
  exact schwartz_fourierND_moment_bound φ n hm

theorem quadratic_stationaryND_expansion_L1 {b : ℝ} (hb : 0 < b) (φ : 𝓢(V,ℂ))
    (n : ℕ) {m : ℕ} (hm : Module.finrank ℝ V < m) :
    ‖(∫ x : V, Complex.exp (-((b:ℂ)*Complex.I)*(‖x‖:ℂ)^2)*φ x) -
      fresnelCoefficientND V b * quadraticExpansionND φ n b‖ ≤
    ((Real.pi/b)^(Module.finrank ℝ V/2:ℝ) * ((Real.pi^2/b)^(n+1)/(n.factorial:ℝ))) *
      ((2^m*(fourierDerivativeND_L1 φ (2*(n+1))+fourierDerivativeND_L1 φ (2*(n+1)+m))) *
        ∫ ξ : V, ((1+‖ξ‖)^m)⁻¹) := by
  apply (quadratic_stationaryND_expansion hb φ n).trans
  apply mul_le_mul_of_nonneg_left (schwartz_inverseND_moment_bound φ (2*(n+1)) hm)
  positivity

end Attempt4FullFar
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open MeasureTheory Set Laplacian LineDeriv
open scoped FourierTransform SchwartzMap RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

lemma schwartz_fourierInv_laplacianND (φ : 𝓢(V,ℂ)) (ξ : V) :
    𝓕⁻ (Δ φ) ξ = (-(2*(Real.pi:ℂ))^2)*(‖ξ‖:ℂ)^2 * 𝓕⁻ φ ξ := by
  let b := stdOrthonormalBasis ℝ V
  rw [SchwartzMap.laplacian_eq_sum b]
  rw [FourierTransform.fourierInv_sum,sum_apply]
  have he (i) : 𝓕⁻ (∂_{b i} (∂_{b i} φ)) ξ =
      (-(2*(Real.pi:ℂ))^2) * ((inner ℝ ξ (b i):ℝ):ℂ)^2 * 𝓕⁻ φ ξ := by
    have hi : (fun x : V => inner ℝ x (b i)).HasTemperateGrowth := by fun_prop
    simp only [SchwartzMap.fourierInv_lineDerivOp_eq,smul_apply,
      SchwartzMap.smulLeftCLM_apply hi,smul_eq_mul,Complex.real_smul]
    ring_nf
    rw [Complex.I_sq]
    ring
  change (∑ i, 𝓕⁻ (∂_{b i} (∂_{b i} φ)) ξ) = _
  simp_rw [he]
  rw [← Finset.sum_mul,← Finset.mul_sum]
  congr 2
  have hh := b.sum_sq_norm_inner_left ξ
  have hh' : ∑ i, (inner ℝ ξ (b i))^2 = ‖ξ‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using hh
  exact_mod_cast hh'

noncomputable def iteratedLaplacianND (φ : 𝓢(V,ℂ)) : ℕ → 𝓢(V,ℂ)
  | 0 => φ
  | n+1 => Δ (iteratedLaplacianND φ n)

lemma schwartz_fourierInv_iteratedLaplacianND (φ : 𝓢(V,ℂ)) (n : ℕ) (ξ : V) :
    𝓕⁻ (iteratedLaplacianND φ n) ξ =
      (-(2*(Real.pi:ℂ))^2)^n * (‖ξ‖:ℂ)^(2*n) * 𝓕⁻ φ ξ := by
  induction n with
  | zero => simp [iteratedLaplacianND]
  | succ n ih =>
    rw [iteratedLaplacianND,schwartz_fourierInv_laplacianND,ih]
    simp only [pow_succ,mul_add,pow_mul]
    ring

lemma schwartz_inverseND_even_moment (φ : 𝓢(V,ℂ)) (n : ℕ) :
    (∫ ξ : V, (‖ξ‖:ℂ)^(2*n)*𝓕⁻ φ ξ) =
      ((-(2*(Real.pi:ℂ))^2)^n)⁻¹ * iteratedLaplacianND φ n 0 := by
  have hh : (∫ ξ : V, 𝓕⁻ (iteratedLaplacianND φ n) ξ) = iteratedLaplacianND φ n 0 := by
    have hi := congrArg (fun f : 𝓢(V,ℂ) => f 0)
      (show (𝓕 (𝓕⁻ (iteratedLaplacianND φ n)) : 𝓢(V,ℂ)) = iteratedLaplacianND φ n from
        FourierTransform.fourier_fourierInv_eq _)
    simpa only [SchwartzMap.fourier_coe,Real.fourier_eq,inner_zero_right,neg_zero,
      AddChar.map_zero_eq_one,one_smul] using hi
  simp_rw [schwartz_fourierInv_iteratedLaplacianND,mul_assoc] at hh
  rw [integral_const_mul] at hh
  have hn : (-(2*(Real.pi:ℂ))^2)^n ≠ 0 := by
    apply pow_ne_zero
    exact neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  rw [← hh,← mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem quadraticExpansionND_eq_local (φ : 𝓢(V,ℂ)) (n : ℕ) (b : ℝ) :
    quadraticExpansionND φ n b =
      ∑ k ∈ Finset.range (n+1),
        ((((k.factorial:ℝ)⁻¹*(Real.pi^2/b)^k):ℝ):ℂ)*Complex.I^k *
          (((-(2*(Real.pi:ℂ))^2)^k)⁻¹ * iteratedLaplacianND φ k 0) := by
  unfold quadraticExpansionND
  simp only [schwartz_inverseND_even_moment]

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI

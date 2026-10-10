import OAI.Analysis.FreeEntropy.PolynomialFunctions

namespace OAI

universe u1 u2 u3 u4

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 def IsComplexPolynomial (f : (ι → ℝ) → ℂ) : Prop :=
  IsRealPolynomial (fun x => (f x).re) ∧ IsRealPolynomial (fun x => (f x).im)
 def complexCoordinateDerivative (f : (ι → ℝ) → ℂ) (i : ι) (x : ι → ℝ) : ℂ :=
  deriv (fun t => f (Function.update x i t)) (x i)
 theorem complex_integral_re {Ω : Type u2} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := (integral_re hf).symm
 theorem complex_integral_im {Ω : Type u3} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ := (integral_im hf).symm
 namespace IsComplexPolynomial
 theorem const (z : ℂ) : IsComplexPolynomial (fun _ : ι → ℝ => z) :=
  ⟨IsRealPolynomial.const _,IsRealPolynomial.const _⟩
 theorem ofReal {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) :
    IsComplexPolynomial (fun x => (f x : ℂ)) := by
  exact ⟨hf, IsRealPolynomial.const 0⟩
 theorem coord (i : ι) : IsComplexPolynomial (fun x : ι → ℝ => (x i : ℂ)) := ofReal (IsRealPolynomial.coord i)
 theorem add {f g : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) :
    IsComplexPolynomial (fun x => f x+g x) := ⟨hf.1.add hg.1,hf.2.add hg.2⟩
 theorem sub {f g : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) :
    IsComplexPolynomial (fun x => f x-g x) := ⟨hf.1.sub hg.1,hf.2.sub hg.2⟩
 theorem mul {f g : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (hg : IsComplexPolynomial g) :
    IsComplexPolynomial (fun x => f x*g x) :=
  ⟨(hf.1.mul hg.1).sub (hf.2.mul hg.2),(hf.1.mul hg.2).add (hf.2.mul hg.1)⟩
 theorem const_mul {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (z : ℂ) :
    IsComplexPolynomial (fun x => z*f x) := (const z).mul hf
 theorem mul_const {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (z : ℂ) :
    IsComplexPolynomial (fun x => f x*z) := hf.mul (const z)
 theorem finset_sum {κ : Type u4} (s : Finset κ) {f : κ → (ι → ℝ) → ℂ}
    (hf : ∀ k ∈ s, IsComplexPolynomial (f k)) : IsComplexPolynomial (fun x => ∑ k ∈ s, f k x) := by
  constructor
  · simpa using IsRealPolynomial.finset_sum s (fun k hk => (hf k hk).1)
  · simpa using IsRealPolynomial.finset_sum s (fun k hk => (hf k hk).2)
 theorem continuous {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) : Continuous f := by
  have hc := (Complex.continuous_ofReal.comp hf.1.continuous).add ((Complex.continuous_ofReal.comp hf.2.continuous).mul (continuous_const (y := Complex.I)))
  convert hc using 1
  funext x
  exact (Complex.re_add_im (f x)).symm
 theorem integrable {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) : Integrable f (productGaussian ι) := by
  have hi := hf.1.integrable.ofReal.add (hf.2.integrable.ofReal.mul_const Complex.I)
  convert hi using 1 ; try rfl
  funext x
  exact (Complex.re_add_im (f x)).symm
 theorem normSq {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) :
    IsRealPolynomial (fun x => Complex.normSq (f x)) := by
  simpa only [Complex.normSq_apply, pow_two] using (hf.1.pow 2).add (hf.2.pow 2)
 theorem norm_sq {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) :
    IsRealPolynomial (fun x => ‖f x‖^2) := by simpa only [Complex.sq_norm] using hf.normSq
 theorem hasCoordinateDeriv {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => f (Function.update x i t))
      ((coordinateDerivative (fun y => (f y).re) i x : ℂ) +
        (coordinateDerivative (fun y => (f y).im) i x : ℂ)*Complex.I) (x i) := by
  have hd := (hf.1.hasDerivAt i x).ofReal_comp.add ((hf.2.hasDerivAt i x).ofReal_comp.mul_const Complex.I)
  convert hd using 1 ; try rfl
  funext t
  exact (Complex.re_add_im (f (Function.update x i t))).symm
 theorem coordinateDerivative_eq {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (i : ι) (x : ι → ℝ) :
    complexCoordinateDerivative f i x =
      (coordinateDerivative (fun y => (f y).re) i x : ℂ) +
        (coordinateDerivative (fun y => (f y).im) i x : ℂ)*Complex.I :=
  (hf.hasCoordinateDeriv i x).deriv
 theorem derivative {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (i : ι) :
    IsComplexPolynomial (complexCoordinateDerivative f i) := by
  have he : complexCoordinateDerivative f i = fun x =>
      (coordinateDerivative (fun y => (f y).re) i x : ℂ) +
        (coordinateDerivative (fun y => (f y).im) i x : ℂ)*Complex.I := by
    funext x; exact hf.coordinateDerivative_eq i x
  rw [he]
  exact (ofReal (hf.1.derivative i)).add ((ofReal (hf.2.derivative i)).mul_const Complex.I)
 theorem hasDerivAt {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => f (Function.update x i t)) (complexCoordinateDerivative f i x) (x i) := by
  rw [hf.coordinateDerivative_eq]
  exact hf.hasCoordinateDeriv i x
 theorem stein {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) (i : ι) :
    (∫ x, (x i : ℂ)*f x ∂productGaussian ι) = ∫ x, complexCoordinateDerivative f i x ∂productGaussian ι := by
  have hi := ((coord i).mul hf).integrable
  have hd := (hf.derivative i).integrable
  apply Complex.ext
  · rw [complex_integral_re hi, complex_integral_re hd]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hf.coordinateDerivative_eq, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_add, add_zero] using hf.1.stein i
  · rw [complex_integral_im hi, complex_integral_im hd]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      hf.coordinateDerivative_eq, Complex.add_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add] using hf.2.stein i
 theorem poincare {f : (ι → ℝ) → ℂ} (hf : IsComplexPolynomial f) :
    (∫ x, ‖f x-∫ y, f y ∂productGaussian ι‖^2 ∂productGaussian ι) ≤
      ∑ i, ∫ x, ‖complexCoordinateDerivative f i x‖^2 ∂productGaussian ι := by
  have hi := hf.integrable
  have hnorm (z : ℂ) : ‖z‖^2 = z.re^2+z.im^2 := by rw [Complex.sq_norm]; simp only [Complex.normSq_apply,pow_two]
  have hr := ((hf.1.sub (IsRealPolynomial.const (∫ y, (f y).re ∂productGaussian ι))).pow 2).integrable
  have hm := ((hf.2.sub (IsRealPolynomial.const (∫ y, (f y).im ∂productGaussian ι))).pow 2).integrable
  have he : (∫ x, ‖f x-∫ y, f y ∂productGaussian ι‖^2 ∂productGaussian ι) =
      (∫ x, ((f x).re-∫ y, (f y).re ∂productGaussian ι)^2 ∂productGaussian ι) +
      ∫ x, ((f x).im-∫ y, (f y).im ∂productGaussian ι)^2 ∂productGaussian ι := by
    simp only [hnorm, Complex.sub_re, Complex.sub_im, complex_integral_re hi, complex_integral_im hi]
    exact integral_add hr hm
  rw [he]
  calc
    _ ≤ (∑ i, ∫ x, (coordinateDerivative (fun y => (f y).re) i x)^2 ∂productGaussian ι) +
        ∑ i, ∫ x, (coordinateDerivative (fun y => (f y).im) i x)^2 ∂productGaussian ι :=
      add_le_add hf.1.poincare hf.2.poincare
    _ = _ := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro i hi
      rw [← integral_add ((hf.1.derivative i).pow 2).integrable ((hf.2.derivative i).pow 2).integrable]
      apply integral_congr_ae
      filter_upwards [] with x
      simp [hnorm, hf.coordinateDerivative_eq]
 end IsComplexPolynomial
end FiniteEntropySeparation

end

end OAI

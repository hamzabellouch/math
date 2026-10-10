import OAI.Analysis.LipschitzHilbert.Fourier.SincMaskFourier

namespace OAI

/-! Finite powers of the exact sinc mask preserve a Fourier annulus
with its explicitly accumulated bandwidth. -/

noncomputable section
open MeasureTheory Set
open scoped FourierTransform
namespace LipschitzHilbert

 theorem integrable_affine_sinc_pow_mul {f : ℝ → ℂ} (hf : Integrable f)
    (a b : ℝ) (n : ℕ) : Integrable (fun x => (Real.sinc (a*x+b):ℂ)^n*f x) := by
  apply hf.bdd_mul (c := 1)
  · exact (by fun_prop : Continuous (fun x : ℝ => (Real.sinc (a*x+b):ℂ)^n)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      rw [norm_pow]
      exact (pow_le_one₀ (norm_nonneg _) (by
        simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_sinc_le_one (a*x+b))))

/-- The radius adds once for each factor; the affine offset never
contributes to the support radius. -/
theorem fourier_affine_sinc_pow_mul_eq_zero (a b : ℝ) (n : ℕ)
    {f : ℝ → ℂ} (hf : Integrable f) (xi : ℝ)
    (hzero : ∀ eta : ℝ, |eta-xi| ≤ (n:ℝ)*(|a|/(2*Real.pi)) → 𝓕 f eta = 0) :
    𝓕 (fun x => (Real.sinc (a*x+b):ℂ)^n*f x) xi = 0 := by
  induction n generalizing f xi with
  | zero =>
      simpa only [pow_zero,one_mul] using hzero xi (by simp)
  | succ n ih =>
      have hid : (fun x => (Real.sinc (a*x+b):ℂ)^(n+1)*f x) =
          (fun x => (Real.sinc (a*x+b):ℂ)*((Real.sinc (a*x+b):ℂ)^n*f x)) := by
        funext x
        rw [pow_succ]
        ring
      rw [hid]
      apply fourier_affine_sinc_mul_eq_zero (integrable_affine_sinc_pow_mul hf a b n) a b xi
      intro eta heta
      apply ih hf eta
      intro z hz
      apply hzero z
      calc
        |z-xi| ≤ |z-eta|+|eta-xi| := by
          rw [show z-xi = (z-eta)+(eta-xi) by ring]
          exact abs_add_le _ _
        _ ≤ (n:ℝ)*(|a|/(2*Real.pi))+|a|/(2*Real.pi) := add_le_add hz heta
        _ = ((n+1:ℕ):ℝ)*(|a|/(2*Real.pi)) := by push_cast; ring

theorem fourier_sinc_pair_pow_mul_eq_zero (a b c d : ℝ) (n : ℕ)
    {f : ℝ → ℂ} (hf : Integrable f) (xi : ℝ)
    (hzero : ∀ eta : ℝ, |eta-xi| ≤ (n:ℝ)*((|a|+|c|)/(2*Real.pi)) → 𝓕 f eta = 0) :
    𝓕 (fun x => ((Real.sinc (a*x+b)*Real.sinc (c*x+d):ℝ):ℂ)^n*f x) xi = 0 := by
  have hid : (fun x => ((Real.sinc (a*x+b)*Real.sinc (c*x+d):ℝ):ℂ)^n*f x) =
      (fun x => (Real.sinc (a*x+b):ℂ)^n*((Real.sinc (c*x+d):ℂ)^n*f x)) := by
    funext x
    rw [Complex.ofReal_mul,mul_pow,mul_assoc]
  rw [hid]
  apply fourier_affine_sinc_pow_mul_eq_zero a b n
    (integrable_affine_sinc_pow_mul hf c d n) xi
  intro eta heta
  apply fourier_affine_sinc_pow_mul_eq_zero c d n hf eta
  intro z hz
  apply hzero z
  calc
    |z-xi| ≤ |z-eta|+|eta-xi| := by
      rw [show z-xi = (z-eta)+(eta-xi) by ring]
      exact abs_add_le _ _
    _ ≤ (n:ℝ)*(|c|/(2*Real.pi))+(n:ℝ)*(|a|/(2*Real.pi)) := add_le_add hz heta
    _ = (n:ℝ)*((|a|+|c|)/(2*Real.pi)) := by ring

/-- An explicit annulus statement for the even sinc product. -/
theorem sincProductMask_fourier_annulus {f : ℝ → ℂ} (hf : Integrable f)
    (n : ℕ) (a b c d lo hi : ℝ)
    (hlow : ∀ xi, |xi| < lo → 𝓕 f xi = 0)
    (hhigh : ∀ xi, hi < |xi| → 𝓕 f xi = 0) :
    let B := (2*(n:ℝ))*((|a|+|c|)/(2*Real.pi))
    (∀ xi, |xi| < lo-B →
      𝓕 (fun x => (sincProductMask n (a*x+b) (c*x+d):ℂ)*f x) xi = 0) ∧
    (∀ xi, hi+B < |xi| →
      𝓕 (fun x => (sincProductMask n (a*x+b) (c*x+d):ℂ)*f x) xi = 0) := by
  dsimp only
  constructor
  · intro xi hxi
    change 𝓕 (fun x => (((Real.sinc (a*x+b)*Real.sinc (c*x+d))^(2*n):ℝ):ℂ)*f x) xi = 0
    simp only [Complex.ofReal_pow]
    apply fourier_sinc_pair_pow_mul_eq_zero a b c d (2*n) hf xi
    intro eta heta
    apply hlow eta
    have habs : |eta| ≤ |eta-xi|+|xi| := by
      calc
        |eta| = |(eta-xi)+xi| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    push_cast at heta
    linarith
  · intro xi hxi
    change 𝓕 (fun x => (((Real.sinc (a*x+b)*Real.sinc (c*x+d))^(2*n):ℝ):ℂ)*f x) xi = 0
    simp only [Complex.ofReal_pow]
    apply fourier_sinc_pair_pow_mul_eq_zero a b c d (2*n) hf xi
    intro eta heta
    apply hhigh eta
    have habs : |xi| ≤ |eta-xi|+|eta| := by
      calc
        |xi| = |(xi-eta)+eta| := by congr 1; ring
        _ ≤ _ := by simpa only [abs_sub_comm xi eta] using abs_add_le (xi-eta) eta
    push_cast at heta
    linarith

end LipschitzHilbert

end

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitPullback

namespace OAI

/-! The physical complex one-electron quadratic form splits exactly into
its real and imaginary parts. Finite real-orbital penalties split as well. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem complex_norm_sq_parts (z : ℂ) : ‖z‖^2 = z.re^2+z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem complex_mass_parts {f : Position → ℂ} (hf : MemLp f 2) :
    (∫ x, ‖f x‖^2) = (∫ x, (f x).re^2)+(∫ x, (f x).im^2) := by
  simp_rw [complex_norm_sq_parts]
  exact integral_add hf.re.integrable_sq hf.im.integrable_sq

theorem complex_real_orbital_parts {f : Position → ℂ} {ψ : Position → ℝ}
    (hf : MemLp f 2) (hψ : MemLp ψ 2) :
    ‖∫ x, f x*(ψ x : ℂ)‖^2 =
      (∫ x, (f x).re*ψ x)^2+(∫ x, (f x).im*ψ x)^2 := by
  have hi : Integrable (fun x => f x*(ψ x : ℂ)) := hf.integrable_mul hψ.ofReal
  have hr := integral_re hi
  have hm := integral_im hi
  change (∫ x, (f x*(ψ x : ℂ)).re) = (∫ x, f x*(ψ x : ℂ)).re at hr
  change (∫ x, (f x*(ψ x : ℂ)).im) = (∫ x, f x*(ψ x : ℂ)).im at hm
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add] at hr hm
  rw [complex_norm_sq_parts,← hr,← hm]

theorem realPart_partial {f : Position → ℂ} (hf : ContDiff ℝ 1 f) (x e : Position) :
    fderiv ℝ (fun y => (f y).re) x e = (fderiv ℝ f x e).re := by
  exact congrArg (fun L : Position →L[ℝ] ℝ => L e)
    (Complex.reCLM.hasFDerivAt.comp x (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv

theorem imagPart_partial {f : Position → ℂ} (hf : ContDiff ℝ 1 f) (x e : Position) :
    fderiv ℝ (fun y => (f y).im) x e = (fderiv ℝ f x e).im := by
  exact congrArg (fun L : Position →L[ℝ] ℝ => L e)
    (Complex.imCLM.hasFDerivAt.comp x (hf.differentiable (by norm_num) x).hasFDerivAt).fderiv

def positionComplexKinetic (f : Position → ℂ) : ℝ :=
  (1/2:ℝ)*∑ a : Fin 3, ∫ x, ‖fderiv ℝ f x (EuclideanSpace.single a 1)‖^2

def positionComplexForm (V : Position → ℝ) (f : Position → ℂ) : ℝ :=
  positionComplexKinetic f+∫ x, V x*‖f x‖^2

theorem positionComplexForm_parts {f : Position → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (V : Position → ℝ) (hV : Continuous V) :
    positionComplexForm V f = positionRealForm V (fun x => (f x).re) +
      positionRealForm V (fun x => (f x).im) := by
  have hr : ContDiff ℝ 1 (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have hi : ContDiff ℝ 1 (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have hrc : HasCompactSupport (fun x => (f x).re) := hc.comp_left (g := Complex.re) rfl
  have hic : HasCompactSupport (fun x => (f x).im) := hc.comp_left (g := Complex.im) rfl
  have hkr (a : Fin 3) := compact_directional_square_integrable volume hr hrc (EuclideanSpace.single a 1)
  have hki (a : Fin 3) := compact_directional_square_integrable volume hi hic (EuclideanSpace.single a 1)
  have hrr : HasCompactSupport (fun x => (f x).re^2) :=
    hrc.comp_left (g := fun t : ℝ => t^2) (by simp)
  have hii : HasCompactSupport (fun x => (f x).im^2) :=
    hic.comp_left (g := fun t : ℝ => t^2) (by simp)
  have hprc : HasCompactSupport (fun x => V x*(f x).re^2) := hrr.mul_left
  have hpic : HasCompactSupport (fun x => V x*(f x).im^2) := hii.mul_left
  have hpr : Integrable (fun x => V x*(f x).re^2) :=
    (hV.mul (hr.continuous.pow 2)).integrable_of_hasCompactSupport
      hprc
  have hpi : Integrable (fun x => V x*(f x).im^2) :=
    (hV.mul (hi.continuous.pow 2)).integrable_of_hasCompactSupport
      hpic
  have hk (a : Fin 3) : (∫ x, ‖fderiv ℝ f x (EuclideanSpace.single a 1)‖^2) =
      (∫ x, (fderiv ℝ (fun y => (f y).re) x (EuclideanSpace.single a 1))^2)+
      (∫ x, (fderiv ℝ (fun y => (f y).im) x (EuclideanSpace.single a 1))^2) := by
    rw [← integral_add (hkr a) (hki a)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [realPart_partial hf, imagPart_partial hf, complex_norm_sq_parts]
  have hp : (∫ x, V x*‖f x‖^2) = (∫ x, V x*(f x).re^2)+(∫ x, V x*(f x).im^2) := by
    rw [← integral_add hpr hpi]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [complex_norm_sq_parts,mul_add]
  unfold positionComplexForm positionComplexKinetic positionRealForm positionRealKinetic
  simp_rw [hk]
  rw [Finset.sum_add_distrib,hp]
  ring

/-- Real-valued orbitals give the same finite-rank lower estimate for
arbitrary complex test functions, without a reality restriction on states. -/
theorem real_form_lower_to_complex {ι : Type*} [Fintype ι]
    (V : Position → ℝ) (hV : Continuous V) (ψ : ι → Position → ℝ)
    (hψ : ∀ i, MemLp (ψ i) 2) (E κ : ℝ)
    (hbound : ∀ g : Position → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
      E*(∫ x, g x^2)-κ*(∑ i, (∫ x, g x*ψ i x)^2) ≤ positionRealForm V g)
    (f : Position → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    E*(∫ x, ‖f x‖^2)-κ*(∑ i, ‖∫ x, f x*(ψ i x : ℂ)‖^2) ≤ positionComplexForm V f := by
  have hr : ContDiff ℝ 1 (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have hi : ContDiff ℝ 1 (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have hrc : HasCompactSupport (fun x => (f x).re) := hc.comp_left (g := Complex.re) rfl
  have hic : HasCompactSupport (fun x => (f x).im) := hc.comp_left (g := Complex.im) rfl
  have hfr := hbound _ hr hrc
  have hfi := hbound _ hi hic
  have hL2 : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hc
  rw [complex_mass_parts hL2,positionComplexForm_parts hf hc V hV]
  simp_rw [complex_real_orbital_parts hL2 (hψ _)]
  rw [Finset.sum_add_distrib]
  nlinarith

end ContinuumCoulomb

end

end OAI

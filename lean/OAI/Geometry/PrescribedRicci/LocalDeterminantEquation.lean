import Mathlib
import OAI.Geometry.PrescribedRicci.CofactorBilin
import OAI.Geometry.PrescribedRicci.DeterminantJet
import OAI.Geometry.PrescribedRicci.SchwartzHessianWords

namespace OAI

/-! Local Determinant Equation. -/

section

 

noncomputable section
open Set Filter Topology Matrix LineDeriv
open scoped ContDiff SchwartzMap Classical Matrix.Norms.Elementwise BoundedContinuousFunction
namespace TameInterpolation
open SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : Type*}
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cword_eventuallyEq (e : ι → E) (ws : List ι) {f g : E → ℂ} {x : E}
    (h : f =ᶠ[𝓝 x] g) : cword e f ws =ᶠ[𝓝 x] cword e g ws := by
  induction ws with
  | nil => exact h
  | cons a ws ih =>
    filter_upwards [ih.fderiv (𝕜:=ℝ)] with y hy
    exact congrArg (fun L : E →L[ℝ] ℂ => L (e a)) hy
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cword_add (e : ι → E) (ws : List ι) (f g : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    cword e (fun x => f x+g x) ws = fun x => cword e f ws x+cword e g ws x := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change cdir (e a) (cword e (fun x => f x+g x) ws) = _
    rw [ih]
    funext x
    unfold cdir
    rw [fderiv_fun_add ((cword_smooth e hf ws).differentiable (by simp) x)
      ((cword_smooth e hg ws).differentiable (by simp) x)]
    rfl
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cwordSchwartz_general (e : ι → E) (f : 𝓢(E,ℂ)) (ws : List ι) :
    cword e f ws = (schwartzWord (ws.map e) f : E → ℂ) := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change cdir (e a) (cword e f ws) = _
    rw [ih,cdir_schwartz]
    rfl
end TameInterpolation
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart FrozenPoisson MetricLocalization TameInterpolation
variable {d : ℕ}
lemma cofactorBilin_inverse_det (H : Matrix (Fin d) (Fin d) ℂ) (h : IsUnit H.det) :
    cofactorBilin H.det⁻¹ H = traceBilin H := by
  ext B
  rw [cofactorBilin_apply,NonlinearHessian.detDifferential,MongeAmpere.real_fderiv_det_apply H _ h]
  rw [← mul_assoc,inv_mul_cancel₀ h.ne_zero,one_mul]
  rfl

lemma schwartz_real_trace_expression (H : Matrix (Fin d) (Fin d) ℂ) (h : IsUnit H.det)
    (f : 𝓢(EC d,ℂ)) (hr : ∀ x, (f x).im = 0) (y : EC d) :
    ∑ i, ∑ j, (traceBilin H (rankTwo (stdOrthonormalBasis ℝ (EC d) i)
      (stdOrthonormalBasis ℝ (EC d) j)) : ℂ) *
      fderiv ℝ (fderiv ℝ f) y (stdOrthonormalBasis ℝ (EC d) i) (stdOrthonormalBasis ℝ (EC d) j) =
      (((H⁻¹ * (show Matrix (Fin d) (Fin d) ℂ from fun i j => hessianEntrySchwartz i j f y)).trace).re : ℂ) := by
  have he : (f : EC d → ℂ) =ᶠ[𝓝 y] Complex.ofRealCLM ∘ (fun x => (f x).re) := by
    filter_upwards [] with x
    exact Complex.ext rfl (by simpa using hr x)
  have hh := cofactor_smooth_expression (Complex.reCLM.contDiff.comp f.smooth').contDiffAt f he H.det⁻¹ H
  rw [cofactorBilin_inverse_det H h,NonlinearHessian.detDifferential] at hh
  erw [MongeAmpere.real_fderiv_det_apply H _ h,
    ← mul_assoc,inv_mul_cancel₀ h.ne_zero,one_mul] at hh
  exact hh.symm

lemma wordHessian_trace_cutoff (κ f : 𝓢(EC d,ℂ)) (ws : List (EC d))
    (G H : Fin d → Fin d → 𝓢(EC d,ℂ)) (y : EC d)
    (he : ∀ i j, (H i j : EC d → ℂ) =ᶠ[𝓝 y]
      (fun x => G i j x+hessianEntrySchwartz i j f x)) :
    (show Matrix (Fin d) (Fin d) ℂ from fun i j => hessianEntrySchwartz i j (SchwartzMap.smulLeftCLM ℂ κ (schwartzWord ws f)) y) =
      κ y • (show Matrix (Fin d) (Fin d) ℂ from fun i j => schwartzWord ws (H i j) y) +
        (show Matrix (Fin d) (Fin d) ℂ from fun i j => wordHessianError κ ws i j f y-κ y*schwartzWord ws (G i j) y) := by
  ext i j
  change _ = κ y * schwartzWord ws (H i j) y + (wordHessianError κ ws i j f y-κ y*schwartzWord ws (G i j) y)
  rw [wordHessianError_identity]
  simp only [_root_.add_apply,SchwartzMap.smulLeftCLM_apply_apply κ.hasTemperateGrowth,
    smul_eq_mul]
  have hh := (cword_eventuallyEq id ws (he i j)).eq_of_nhds
  erw [cword_add id ws (G i j : EC d → ℂ) (hessianEntrySchwartz i j f : EC d → ℂ) (G i j).smooth' (hessianEntrySchwartz i j f).smooth'] at hh
  simp only [cwordSchwartz_general,List.map_id] at hh
  rw [hh]
  ring

 

theorem determinant_word_cutoff_trace
    {ι : Type*} (e : ι → EC d) (ws : List ι) (hw : ws ≠ [])
    (κ f : 𝓢(EC d,ℂ)) (G H : Fin d → Fin d → 𝓢(EC d,ℂ))
    (ρ : 𝓢(EC d,ℂ)) (y : EC d)
    (he : ∀ i j, (H i j : EC d → ℂ) =ᶠ[𝓝 y]
      (fun x => G i j x+hessianEntrySchwartz i j f x))
    (hρ : (fun x => (show Matrix (Fin d) (Fin d) ℂ from fun i j => H i j x).det) =ᶠ[𝓝 y] ρ)
    (hinv : IsUnit (show Matrix (Fin d) (Fin d) ℂ from fun i j => H i j y).det) :
    (((show Matrix (Fin d) (Fin d) ℂ from fun i j => H i j y)⁻¹) *
      (show Matrix (Fin d) (Fin d) ℂ from fun i j => hessianEntrySchwartz i j (SchwartzMap.smulLeftCLM ℂ κ (schwartzWord (ws.map e) f)) y)).trace =
      κ y * (show Matrix (Fin d) (Fin d) ℂ from fun i j => H i j y).det⁻¹ *
        (schwartzWord (ws.map e) ρ y-detJetRemainder e (fun x i j => H i j x) ws y) +
      (((show Matrix (Fin d) (Fin d) ℂ from fun i j => H i j y)⁻¹) *
        (show Matrix (Fin d) (Fin d) ℂ from fun i j => wordHessianError κ (ws.map e) i j f y-κ y*schwartzWord (ws.map e) (G i j) y)).trace := by
  let M : Matrix (Fin d) (Fin d) ℂ := fun i j => H i j y
  have hd := cword_det_trace e (fun x i j => H i j x) (fun i j => (H i j).smooth') ws hw y hinv
  have hdρ := (cword_eventuallyEq e ws hρ).eq_of_nhds
  rw [cwordSchwartz_general] at hdρ
  rw [hdρ] at hd
  simp only [cwordSchwartz_general] at hd
  have ht : ((M⁻¹ * (show Matrix (Fin d) (Fin d) ℂ from fun i j => schwartzWord (ws.map e) (H i j) y)).trace) =
      M.det⁻¹ * (schwartzWord (ws.map e) ρ y-detJetRemainder e (fun x i j => H i j x) ws y) := by
    have hh := congrArg (fun z : ℂ => M.det⁻¹*z) (sub_eq_iff_eq_add.mpr hd)
    simpa only [M,← mul_assoc,inv_mul_cancel₀ hinv.ne_zero,one_mul] using hh.symm
  rw [wordHessian_trace_cutoff κ f (ws.map e) G H y he]
  rw [Matrix.mul_add,Matrix.mul_smul,trace_add,trace_smul]
  change κ y * (M⁻¹ * _).trace + _ = _
  rw [ht]
  ring
end GlobalElliptic

end
end

end OAI

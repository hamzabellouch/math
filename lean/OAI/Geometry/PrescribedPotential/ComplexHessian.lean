import Mathlib
import OAI.Geometry.PrescribedPotential.CoreBounds

namespace OAI

/-! Complex Hessian. -/

section

 

noncomputable section
open Set Filter Topology MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartzCoord_smul (s : ℝ) (c : ℂ) (f : 𝓢(E, ℂ)) :
    schwartzCoord s (c • f) = c • schwartzCoord s f := by
  apply realize_injective s
  rw [map_smul, realize_schwartzCoord, realize_schwartzCoord]
  exact (SchwartzMap.toTemperedDistributionCLM E ℂ volume).map_smul c f

lemma CoreBound.smul {s t : ℝ} {T : 𝓢(E, ℂ) → 𝓢(E, ℂ)}
    (hT : CoreBound s t T) (c : ℂ) : CoreBound s t (fun f => c • T f) := by
  obtain ⟨C,hC,h⟩ := hT
  refine ⟨‖c‖*C,mul_nonneg (norm_nonneg _) hC,fun f => ?_⟩
  rw [schwartzCoord_smul, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h f) (norm_nonneg c)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma complex_smooth_second_deriv (f : 𝓢(E, ℂ)) (v w x : E) :
    (∂_{v} (∂_{w} f)) x = fderiv ℝ (fderiv ℝ f) x v w := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  exact PotentialKaehler.fderiv_eval_derivative f.smooth'.contDiffAt v w

end SobolevChart
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart

lemma second_postcomp_general {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ ∞ f x) (p : F →L[ℝ] G) (v w : E) :
    fderiv ℝ (fderiv ℝ (p ∘ f)) x v w = p (fderiv ℝ (fderiv ℝ f) x v w) := by
  have hN : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y := by
    filter_upwards [(hf.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).eventually (by simp)] with y hy
    exact hy.differentiableAt (by simp)
  have he : fderiv ℝ (p ∘ f) =ᶠ[𝓝 x] (fun y => p.comp (fderiv ℝ f y)) := by
    filter_upwards [hN] with y hy
    exact (p.hasFDerivAt.comp y hy.hasFDerivAt).fderiv
  rw [he.fderiv_eq, fderiv_clm_comp (differentiableAt_const p)
    ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))]
  simp

variable {d : ℕ}
def hessianDirection (i : Fin d) : EC d := (coordinateEquiv d).symm (Pi.single i 1)
def hessianIDirection (i : Fin d) : EC d := (coordinateEquiv d).symm (Complex.I • Pi.single i 1)

def hessianEntrySchwartz (i j : Fin d) : 𝓢(EC d, ℂ) →L[ℂ] 𝓢(EC d, ℂ) :=
  (1/4 : ℂ) •
    ((lineDerivOpCLM ℂ 𝓢(EC d, ℂ) (hessianDirection i) ∘L
      lineDerivOpCLM ℂ 𝓢(EC d, ℂ) (hessianDirection j)) +
    (lineDerivOpCLM ℂ 𝓢(EC d, ℂ) (hessianIDirection i) ∘L
      lineDerivOpCLM ℂ 𝓢(EC d, ℂ) (hessianIDirection j)) +
    Complex.I • ((lineDerivOpCLM ℂ 𝓢(EC d, ℂ) (hessianIDirection i) ∘L
      lineDerivOpCLM ℂ 𝓢(EC d, ℂ) (hessianDirection j)) +
    (-1 : ℂ) • (lineDerivOpCLM ℂ 𝓢(EC d, ℂ) (hessianDirection i) ∘L
      lineDerivOpCLM ℂ 𝓢(EC d, ℂ) (hessianIDirection j))))

lemma hessianEntrySchwartz_apply (i j : Fin d) (f : 𝓢(EC d, ℂ)) (x : EC d) :
    hessianEntrySchwartz i j f x = (1/4 : ℂ) *
      (fderiv ℝ (fderiv ℝ f) x (hessianDirection i) (hessianDirection j) +
       fderiv ℝ (fderiv ℝ f) x (hessianIDirection i) (hessianIDirection j) +
       Complex.I * (fderiv ℝ (fderiv ℝ f) x (hessianIDirection i) (hessianDirection j) -
         fderiv ℝ (fderiv ℝ f) x (hessianDirection i) (hessianIDirection j))) := by
  simp only [hessianEntrySchwartz, smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply,
    smul_eq_mul, complex_smooth_second_deriv]
  ring

lemma hessianEntrySchwartz_bound (s : ℝ) (i j : Fin d) :
    CoreBound (s+2) s (hessianEntrySchwartz i j) := by
  have hb (v w : EC d) : CoreBound (s+2) s (fun f : 𝓢(EC d, ℂ) => ∂_{v} (∂_{w} f)) :=
    (coreBound_deriv v (s := s+1) (t := s) (by linarith)).comp
      (coreBound_deriv w (s := s+2) (t := s+1) (by linarith))
  exact ((hb _ _).add (hb _ _) |>.add (((hb _ _).add ((hb _ _).smul (-1))).smul Complex.I)).smul (1/4)

lemma hessianEntrySchwartz_real {u : EC d → ℝ} {x : EC d} (hu : ContDiffAt ℝ ∞ u x)
    (f : 𝓢(EC d, ℂ)) (he : (f : EC d → ℂ) =ᶠ[𝓝 x] Complex.ofRealCLM ∘ u) (i j : Fin d) :
    hessianEntrySchwartz i j f x =
      PotentialKaehler.hermitianPartMatrix (pullBilin (fderiv ℝ (fderiv ℝ u) x)) i j := by
  rw [hessianEntrySchwartz_apply]
  have he2 : fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ (Complex.ofRealCLM ∘ u)) x :=
    (he.fderiv (𝕜 := ℝ)).fderiv_eq
  rw [he2]
  simp only [second_postcomp_general hu, Complex.ofRealCLM_apply,
    PotentialKaehler.hermitianPartMatrix_apply, PotentialKaehler.hermitianPart,
    pullBilin_apply, hessianDirection, hessianIDirection]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

end GlobalElliptic

end
end

end OAI

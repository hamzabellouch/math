import Mathlib
import OAI.Analysis.Conductivity.Variational.CompactRegularCorrection

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma cube_fderiv_expansion (f : Box3 → ℝ) (p w : Box3) :
    fderiv ℝ f p w=cubePartial f ((1,0),0) p*w.1.1+
      cubePartial f ((0,1),0) p*w.1.2+cubePartial f ((0,0),1) p*w.2 := by
  have hw : w=w.1.1 • ((1,0),0)+w.1.2 • ((0,1),0)+w.2 • ((0,0),1) := by
    ext <;> simp
  calc
    _ = fderiv ℝ f p (w.1.1 • ((1,0),0)+w.1.2 • ((0,1),0)+w.2 • ((0,0),1)) := congrArg _ hw
    _ = _ := by simp only [map_add,map_smul,smul_eq_mul,cubePartial]; ring

theorem cube_weak_divergence {F₁ F₂ F₃ r : Box3 → ℝ}
    (h₁ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₁) (h₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₂)
    (h₃ : ContDiff ℝ (↑(⊤ : ℕ∞)) F₃)
    (hs₁ : HasCompactSupport F₁) (hs₂ : HasCompactSupport F₂) (hs₃ : HasCompactSupport F₃)
    (hd : ∀ p,cubePartial F₁ ((1,0),0) p+cubePartial F₂ ((0,1),0) p+
      cubePartial F₃ ((0,0),1) p=r p)
    (φ : Box3 → ℝ) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) :
    (∫ p,fderiv ℝ φ p ((F₁ p,F₂ p),F₃ p))=-(∫ p,φ p*r p) := by
  have hi₁ : Integrable (fun p => cubePartial φ ((1,0),0) p*F₁ p) :=
    ((cubePartial_smooth hφ _).continuous.mul h₁.continuous).integrable_of_hasCompactSupport hs₁.mul_left
  have hi₂ : Integrable (fun p => cubePartial φ ((0,1),0) p*F₂ p) :=
    ((cubePartial_smooth hφ _).continuous.mul h₂.continuous).integrable_of_hasCompactSupport hs₂.mul_left
  have hi₃ : Integrable (fun p => cubePartial φ ((0,0),1) p*F₃ p) :=
    ((cubePartial_smooth hφ _).continuous.mul h₃.continuous).integrable_of_hasCompactSupport hs₃.mul_left
  simp_rw [cube_fderiv_expansion]
  have hi₁₂ : Integrable (fun p => cubePartial φ ((1,0),0) p*F₁ p+cubePartial φ ((0,1),0) p*F₂ p) := hi₁.add hi₂
  rw [integral_add hi₁₂ hi₃,integral_add hi₁ hi₂]
  linarith [cube_coordinate_divergence_moment h₁ h₂ h₃ hs₁ hs₂ hs₃ hd hφ]

end ScalarConductivity

end

end OAI

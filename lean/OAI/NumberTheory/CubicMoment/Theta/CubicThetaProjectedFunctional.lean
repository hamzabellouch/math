import OAI.NumberTheory.CubicMoment.Theta.CubicThetaProjectedDirichlet
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAngularGammaEquation

namespace OAI

/-! The actual primary-projector pair has the published archimedean
Gamma quotient before finite arithmetic averaging. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaProjectedDirichlet_complete (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) (s : ℂ)
    (h₁ : Complex.Gamma (s+(k:ℂ)/2+1/6)≠0)
    (h₂ : Complex.Gamma (s+(k:ℂ)/2-1/6)≠0) :
    cubicThetaProjectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)=
      cubicThetaAngularCompletion (g 1 0) k s*cubicThetaProjectedDirichlet g hc rev k s := by
  rw [cubicThetaProjectedDirichlet,←mul_assoc,
    cubicThetaAngular_completion_cancel hc k s h₁ h₂,one_mul]

lemma cubicThetaSelectedDirichlet_complete (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) (k : ℕ) (s : ℂ)
    (h₁ : Complex.Gamma (s+(k:ℂ)/2+1/6)≠0)
    (h₂ : Complex.Gamma (s+(k:ℂ)/2-1/6)≠0) :
    cubicThetaSelectedAngularCompleted g hc rev k (2*s+(k:ℂ)-1)=
      cubicThetaAngularCompletion (g 1 0) k s*cubicThetaSelectedDirichlet g hc rev k s := by
  rw [cubicThetaSelectedDirichlet,←mul_assoc,
    cubicThetaAngular_completion_cancel hc k s h₁ h₂,one_mul]

lemma cubicThetaGamma_dual_halfplane {s : ℂ} {k : ℕ} (hs : s.re<5/6+(k:ℝ)/2) :
    Complex.Gamma (1-s+(k:ℂ)/2+1/6)≠0 ∧
      Complex.Gamma (1-s+(k:ℂ)/2-1/6)≠0 := by
  constructor <;> apply Complex.Gamma_ne_zero_of_re_pos <;>
    simp only [Complex.add_re,Complex.sub_re,Complex.div_ofNat_re,Complex.natCast_re,Complex.one_re] <;>
    linarith

theorem cubicThetaSelectedDirichlet_gamma (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : s.re<5/6+(k:ℝ)/2) :
    cubicThetaSelectedDirichlet g hc rev k s=
      (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*
        (cubicThetaLevelScale (g 1 0):ℂ)^(4*s-2)*((2*Real.pi:ℝ):ℂ)^(4*s-2)*
          metaplecticGammaQuotient (cubicThetaCircleOrder (!rev) k) s*
            cubicThetaProjectedDirichlet g hc rev k (1-s) := by
  obtain ⟨h₁,h₂⟩ := cubicThetaGamma_dual_halfplane hs
  have he : ((2*k:ℕ):ℂ)-(2*s+(k:ℂ)-1)=2*(1-s)+(k:ℂ)-1 := by push_cast; ring
  rw [cubicThetaSelectedDirichlet,cubicThetaSelectedAngularCompleted_functional g hc rev hk,he,
    cubicThetaProjectedDirichlet_complete g hc rev k (1-s) h₁ h₂]
  calc
    _ = (cubicThetaLevelAngularRoot (g 1 0) rev k)⁻¹*
        (cubicThetaAngularUncompletion (g 1 0) k s*cubicThetaAngularCompletion (g 1 0) k (1-s))*
          cubicThetaProjectedDirichlet g hc rev k (1-s) := by ring
    _ = _ := by rw [cubicThetaAngular_archimedean_ratio hc (!rev) k s]; ring

theorem cubicThetaProjectedDirichlet_gamma (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (rev : Bool) {k : ℕ} (hk : 0<k)
    {s : ℂ} (hs : s.re<5/6+(k:ℝ)/2) :
    cubicThetaProjectedDirichlet g hc rev k s=
      cubicThetaLevelAngularRoot (g 1 0) rev k*
        (cubicThetaLevelScale (g 1 0):ℂ)^(4*s-2)*((2*Real.pi:ℝ):ℂ)^(4*s-2)*
          metaplecticGammaQuotient (cubicThetaCircleOrder rev k) s*
            cubicThetaSelectedDirichlet g hc rev k (1-s) := by
  obtain ⟨h₁,h₂⟩ := cubicThetaGamma_dual_halfplane hs
  have he : ((2*k:ℕ):ℂ)-(2*s+(k:ℂ)-1)=2*(1-s)+(k:ℂ)-1 := by push_cast; ring
  rw [cubicThetaProjectedDirichlet,cubicThetaProjectedAngularCompleted_functional g hc rev hk,he,
    (cubicThetaSelectedAngular_mellin g hc rev hk _).2,
    cubicThetaSelectedDirichlet_complete g hc rev k (1-s) h₁ h₂]
  calc
    _ = cubicThetaLevelAngularRoot (g 1 0) rev k*
        (cubicThetaAngularUncompletion (g 1 0) k s*cubicThetaAngularCompletion (g 1 0) k (1-s))*
          cubicThetaSelectedDirichlet g hc rev k (1-s) := by ring
    _ = _ := by rw [cubicThetaAngular_archimedean_ratio hc rev k s]; ring

end CubicFirstMoment

end

end OAI

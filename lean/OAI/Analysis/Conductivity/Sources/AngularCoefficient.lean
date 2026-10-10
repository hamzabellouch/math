import Mathlib
import OAI.Analysis.Conductivity.Variational.CentralSmoothTrace
import OAI.Analysis.Conductivity.Variational.SmoothCompactParameter

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

local instance angularCoefficientMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance angularCoefficientProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma contDiff_sourceAngularPolynomial_joint :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : ℝ × (Fin 4 → ℝ) => sourceAngularPolynomial z.1 z.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [sourceAngularPolynomial] <;> fun_prop

def sourceAngularCoefficient (f : (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (h : TorusModes) (t : ℝ) : ℂ :=
  mFourierCoeff (fun θ => (f (sourceAngularCollar (a*t+b) θ) : ℂ)) h

lemma sourceAngularCoefficient_smooth {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) (h : TorusModes) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (sourceAngularCoefficient f a b h) := by
  let F : ℝ × ((Fin 4 → ℝ) × ℂ) → ℂ := fun z =>
    z.2.2 * (f (sourceAngularPolynomial (a*z.1+b) z.2.1) : ℂ)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F := by
    apply ContDiff.mul (contDiff_snd.comp contDiff_snd)
    exact Complex.ofRealCLM.contDiff.comp (hf.comp
      (contDiff_sourceAngularPolynomial_joint.comp
        ((contDiff_const.mul contDiff_fst |>.add contDiff_const).prodMk
          (contDiff_fst.comp contDiff_snd))))
  have hr : Continuous (fun θ : UnitAddTorus (Fin 2) =>
      (sourceRayCoordinates θ,mFourier (-h) θ)) :=
    continuous_sourceRayCoordinates.prodMk (mFourier (-h)).continuous
  exact contDiff_compact_parameter hF hr

def sourceAngularAxial (f : (Fin 3 → ℝ) → ℝ) (a b t : ℝ)
    (θ : UnitAddTorus (Fin 2)) : ℂ :=
  ((deriv (fun u => f (sourceAngularCollar (a*u+b) θ)) t : ℝ) : ℂ)

lemma continuous_sourceAngularAxial {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) :
    Continuous (fun z : ℝ × UnitAddTorus (Fin 2) => sourceAngularAxial f a b z.1 z.2) := by
  let F : ℝ × (Fin 4 → ℝ) → ℝ := fun z =>
    f (sourceAngularPolynomial (a*z.1+b) z.2)
  have hF : ContDiff ℝ (↑(⊤ : ℕ∞)) F :=
    hf.comp (contDiff_sourceAngularPolynomial_joint.comp
      ((contDiff_const.mul contDiff_fst |>.add contDiff_const).prodMk contDiff_snd))
  have he (t : ℝ) (θ : UnitAddTorus (Fin 2)) :
      sourceAngularAxial f a b t θ =
        (fderiv ℝ F (t,sourceRayCoordinates θ) (1,0) : ℂ) := by
    have h := (hF.differentiable (by simp)).differentiableAt.hasFDerivAt
      (x:=(t,sourceRayCoordinates θ))
    have hg := h.comp_hasDerivAt t ((hasDerivAt_id t).prodMk
      (hasDerivAt_const t (sourceRayCoordinates θ)))
    simpa only [sourceAngularAxial,sourceAngularCollar,F,Function.comp_def,id_eq] using
      congrArg (fun u : ℝ => (u:ℂ)) hg.deriv
  simp_rw [he]
  exact Complex.continuous_ofReal.comp
    ((hF.continuous_fderiv (by simp)).comp
      (continuous_fst.prodMk (continuous_sourceRayCoordinates.comp continuous_snd))
      |>.clm_apply continuous_const)

lemma sourceAngularCoefficient_hasDerivAt {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) (h : TorusModes) (t : ℝ) :
    HasDerivAt (sourceAngularCoefficient f a b h)
      (mFourierCoeff (sourceAngularAxial f a b t) h) t := by
  have hF : Continuous (fun z : ℝ × UnitAddTorus (Fin 2) =>
      mFourier (-h) z.2 * (f (sourceAngularCollar (a*z.1+b) z.2) : ℂ)) := by
    apply ((mFourier (-h)).continuous.comp continuous_snd).mul
    exact Complex.continuous_ofReal.comp (hf.continuous.comp
      (contDiff_sourceAngularPolynomial_joint.continuous.comp
        ((continuous_const.mul continuous_fst |>.add continuous_const).prodMk
          (continuous_sourceRayCoordinates.comp continuous_snd))))
  have hD := ((mFourier (-h)).continuous.comp continuous_snd).mul
    (continuous_sourceAngularAxial hf a b)
  apply hasDerivAt_compact_parameter hF hD
  intro u θ
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v => f (sourceAngularCollar (a*v+b) θ)) :=
    hf.comp (contDiff_sourceAngularPolynomial_joint.comp
      ((contDiff_const.mul contDiff_id |>.add contDiff_const).prodMk contDiff_const))
  simpa only [sourceAngularAxial,Function.comp_def,Pi.mul_apply] using
    (((hg.differentiable (by simp)).differentiableAt (x:=u)).hasDerivAt.ofReal_comp).const_mul
      (mFourier (-h) θ)

end ScalarConductivity

end
end

end OAI

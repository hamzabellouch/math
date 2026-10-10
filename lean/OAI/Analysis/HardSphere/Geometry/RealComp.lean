import Mathlib
import OAI.Analysis.HardSphere.Geometry.InnerClmRealRight
import OAI.Analysis.HardSphere.Geometry.TorusLiftBox

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def SmoothMultiplier.realComp {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) φ) : SmoothMultiplier n L :=
  .ofSmooth (fun X ↦ (φ (f.toFun X).re : ℂ))
    (Complex.ofRealCLM.contDiff.comp (hφ.comp (Complex.reCLM.contDiff.comp f.smooth)))

lemma SmoothMultiplier.partial_realComp {n : ℕ} {L : Length} (f : SmoothMultiplier n L)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) φ)
    (hf : ∀ X, conj (f.toFun X)=f.toFun X) (p : Direction n) (X : Configuration n L) :
    coordDerivative n L (f.realComp φ hφ).toFun p X=
      ((deriv φ (f.toFun X).re : ℝ) : ℂ)*coordDerivative n L f.toFun p X := by
  let R := representative n L X
  let v : LiftedConfiguration n := Pi.single p.1 (Pi.single p.2 (1:ℝ))
  have hline : HasDerivAt (fun t : ℝ ↦ R+t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add R
  have hdf := (f.smooth.differentiable (by simp) R).hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hdφ := (hφ.differentiable (by simp) (f.toFun (project n L R)).re).hasDerivAt
  have hreal := Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hdf
  have hchain := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hdφ.comp_of_eq 0 hreal (by simp))
  have hnew := ((f.realComp φ hφ).smooth.differentiable (by simp) R).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hline (by simp)
  have he := hnew.unique hchain
  change coordDerivative n L (f.realComp φ hφ).toFun p X = _ at he
  simp only [Complex.ofRealCLM_apply,Complex.reCLM_apply] at he
  rw [show project n L R=X from project_representative n L X] at he
  have hder : ((coordDerivative n L f.toFun p X).re : ℂ)=coordDerivative n L f.toFun p X := by
    apply Complex.ext
    · rfl
    · have h := congrArg Complex.im (f.partial_real hf p X)
      simp only [Complex.conj_im] at h
      simp only [Complex.ofReal_im]
      linarith
  change _ = ((deriv φ (f.toFun X).re * (coordDerivative n L f.toFun p X).re : ℝ) : ℂ) at he
  rw [Complex.ofReal_mul,hder] at he
  exact he

end HardSphere

end

end OAI

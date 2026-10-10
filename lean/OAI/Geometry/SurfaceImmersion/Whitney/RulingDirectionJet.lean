import OAI.Geometry.SurfaceImmersion.Whitney.TransverseRuledSurface
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace OAI

/-! Transverse ruling preserves the full derivative-direction jet along
its axis, including the mixed second derivative at each crosscap. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma transverseRuling_vertical {f : Base → V} (hf : ContDiff ℝ ∞ f) (x : Base) :
    fderiv ℝ (transverseRuling f) x (![0,1] : Base) =
      fderiv ℝ f (crosscapAxis (x 1)) (![0,1] : Base) +
        (x 0) • deriv (axisTransverse f) (x 1) := by
  rw [transverseRuling_fderiv hf,axisValue_deriv hf]
  simp

lemma transverseRuling_second_vertical {f : Base → V} (hf : ContDiff ℝ ∞ f)
    (t : ℝ) (v : Base) :
    fderiv ℝ (fderiv ℝ (transverseRuling f)) (crosscapAxis t) v (![0,1] : Base) =
      fderiv ℝ (fderiv ℝ f) (crosscapAxis t) v (![0,1] : Base) := by
  let p := crosscapAxis t
  let P : Base →L[ℝ] Base := crosscapAxis.comp (ContinuousLinearMap.proj 1)
  have hD : DifferentiableAt ℝ (fun x => fderiv ℝ f x (![0,1] : Base)) p := ((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).differentiable (by simp) p
  have hfirst := hD.hasFDerivAt.comp p P.hasFDerivAt
  have hder : ContDiff ℝ ∞ (deriv (axisTransverse f)) :=
    (axisTransverse_smooth hf).deriv'
  have hsecond := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) p).smul
    ((hder.differentiable (by simp) _).hasDerivAt.hasFDerivAt.comp p
      (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) p))
  have hd := hfirst.add hsecond
  have he : (fun x : Base => fderiv ℝ f (P x) (![0,1] : Base) +
      (x 0) • deriv (axisTransverse f) (x 1)) =
      (fun x => fderiv ℝ (transverseRuling f) x (![0,1] : Base)) := by
    funext x
    exact (transverseRuling_vertical hf x).symm
  change HasFDerivAt (fun x : Base => fderiv ℝ f (P x) (![0,1] : Base) +
    (x 0) • deriv (axisTransverse f) (x 1)) _ p at hd
  rw [he] at hd
  rw [← SphericalJets.secondDerivative_apply (transverseRuling_smooth hf).contDiffAt,
    hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,
    smul_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]
  have hp0 : p 0 = 0 := by simp [p,crosscapAxis_apply]
  rw [hp0,zero_smul,zero_add,Function.comp_apply]
  have hp1 : p 1 = t := by simp [p,crosscapAxis_apply]
  rw [hp1,axisTransverse_deriv hf,SphericalJets.secondDerivative_apply hf.contDiffAt]
  have hP : P v = (v 1) • (![0,1] : Base) := by
    ext i; fin_cases i <;> simp [P,crosscapAxis_apply]
  rw [hP,map_smul,smul_apply]
  have hs := (hf.contDiffAt (x := crosscapAxis t)).isSymmSndFDerivAt (by simp) (![0,1] : Base) (![1,0] : Base)
  rw [hs]
  have hv : v = (v 0) • (![1,0] : Base) + (v 1) • (![0,1] : Base) := by
    ext i; fin_cases i <;> simp
  conv_rhs => rw [hv,map_add,map_smul,map_smul]
  simp only [add_apply,smul_apply]
  exact add_comm _ _

lemma transverseRuling_direction_jet {f : Base → V} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    axisDirectionJet (transverseRuling f) (crosscapAxis t) =
      axisDirectionJet f (crosscapAxis t) := by
  apply ContinuousLinearMap.ext
  intro z
  rw [axisDirectionJet_apply,axisDirectionJet_apply,transverseRuling_first_jet hf,
    transverseRuling_second_vertical hf]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.CollarFieldJets

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def angularLift {E : Type*} (f : Angle → E) : Point → E := fun x => f (angularProjection x)

lemma angularProjection_basis_zero : angularProjection (basis 0) = 0 := by
  ext a
  simp [angularProjection,basis]

lemma D_angularLift {f : Angle → ℝ} {x : Point}
    (hf : DifferentiableAt ℝ f (angularProjection x)) : D (basis 0) (angularLift f) x = 0 := by
  unfold D angularLift
  change (fderiv ℝ (f ∘ angularProjection) x) (basis 0) = 0
  rw [fderiv_comp x hf angularProjection.differentiableAt,angularProjection.fderiv]
  simp only [ContinuousLinearMap.comp_apply,angularProjection_basis_zero,map_zero]

lemma angularLift_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Angle → E} {x : Point} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f (angularProjection x)) :
    ContDiffAt ℝ n (angularLift f) x := hf.comp x angularProjection.contDiff.contDiffAt

lemma radialMatrixD_angularLift {f : Angle → Mat} {x : Point}
    (hf : ContDiffAt ℝ 1 f (angularProjection x)) : radialMatrixD (angularLift f) x = 0 := by
  funext i k
  exact D_angularLift ((contDiffAt_pi.mp (contDiffAt_pi.mp hf i) k).differentiableAt (by norm_num))

lemma logGammaRadial_actual {f : MassFields} {x : Point} (hf : f.RegularAt x)
    (hs : radialMatrixD f.sigma x = 0) (hm : radialMatrixD f.mg x = 0) :
    logGammaRadial f x = (1/Real.exp (x 0)) • radialMatrixD (logGamma f) x := by
  funext i k
  have hσ := (component_diff hf.sigma i k).differentiableAt (by norm_num)
  have hmg := (component_diff hf.mg i k).differentiableAt (by norm_num)
  have heg := (component_diff hf.eg i k).differentiableAt (by norm_num)
  have hp := (radiusPower_diff 2 1 x).differentiableAt (by norm_num)
  have hz := (radiusPower_diff (-1) 1 x).differentiableAt (by norm_num)
  have hfun : (fun y => logGamma f y i k) = fun y =>
      radiusPower 2 y*f.sigma y i k+radiusPower (-1) y*f.mg y i k+f.eg y i k := by
    funext y
    simp [logGamma,radiusPower_two,radiusPower_inverse]
  have hσ0 : D (basis 0) (fun y => f.sigma y i k) x = 0 := congrArg (fun a : Mat => a i k) hs
  have hm0 : D (basis 0) (fun y => f.mg y i k) x = 0 := congrArg (fun a : Mat => a i k) hm
  change (2*Real.exp (x 0))*f.sigma x i k-(1/Real.exp (x 0)^2)*f.mg x i k+
    (1/Real.exp (x 0))*D (basis 0) (fun y => f.eg y i k) x =
      (1/Real.exp (x 0))*D (basis 0) (fun y => logGamma f y i k) x
  erw [hfun,D_add _ ((hp.mul hσ).add (hz.mul hmg)) heg,D_add _ (hp.mul hσ) (hz.mul hmg),
    D_mul _ hp hσ,D_mul _ hz hmg,hσ0,hm0,D_radiusPower,D_radiusPower]
  simp only [basis,Pi.single_eq_same,mul_one,radiusPower_two,radiusPower_inverse]
  have hr := Real.exp_ne_zero (x 0)
  field_simp
  ring

end
end CKSMixedGeometry

end

end OAI

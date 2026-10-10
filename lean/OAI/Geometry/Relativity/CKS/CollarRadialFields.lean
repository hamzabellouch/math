import OAI.Geometry.Relativity.CKS.CollarSourceParams
import OAI.Geometry.Relativity.CKS.SourcePhysicalTensor

namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open CKSMixedGeometry (basis radiusPower)
open CKSBending
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma paddingDensity_rpow {r : ℝ} (hr : 0 < r) :
    paddingDensity r=r^(-(3:ℝ)/2) := by
  rw [show -(3:ℝ)/2=-(1+1/2) by norm_num,Real.rpow_neg hr.le,
    Real.rpow_add hr,Real.rpow_one,← Real.sqrt_eq_rpow]
  simp [paddingDensity,one_div]

 def radialLift (h : ℝ → ℝ) : MP → ℝ := fun y => h (Real.exp (y 0))

lemma radialLift_diff {h : ℝ → ℝ} {y : MP} (hh : DifferentiableAt ℝ h (Real.exp (y 0))) :
    DifferentiableAt ℝ (radialLift h) y := hh.comp y (by fun_prop)

lemma radialLift_D {h : ℝ → ℝ} {y : MP} (hh : DifferentiableAt ℝ h (Real.exp (y 0))) :
    D (basis 0) (radialLift h) y=Real.exp (y 0)*deriv h (Real.exp (y 0)) := by
  unfold radialLift
  rw [D_comp_real (g := fun y : MP => Real.exp (y 0)) _ hh (by fun_prop)]
  have he : (fun y : MP => Real.exp (y 0))=radiusPower 1 := by
    funext y; simp [radiusPower]
  rw [he,CKSMixedGeometry.D_radiusPower]
  simp [basis,radiusPower]
  ring

def collarQ (R : ℝ) (f : LogCollarData) (y : MP) : AMat :=
  f.sigma y+(1-radialLift (roundingWeight R) y) • f.metricError y

def collarShift (R : ℝ) (f : LogCollarData) (y : MP) : AP :=
  (1-radialLift (roundingWeight R) y) • f.shift y

def collarT (R : ℝ) (f : LogCollarData) (y : MP) : ℝ :=
  1+(1-radialLift (roundingWeight R) y)*f.tError y

def collarLb (R : ℝ) (f : LogCollarData) (y : MP) : ℝ :=
  1+(1-radialLift (roundingWeight R) y)*f.LError y

def collarL (R : ℝ) (f : LogCollarData) (y : MP) : ℝ :=
  collarLb R f y+paddingWeight R (Real.exp (y 0))/Real.exp (y 0)^2

def collarF (R : ℝ) (f : LogCollarData) (y : MP) : ℝ :=
  f.fstar y+(1-radialLift (roundingWeight R) y)*f.massError y+radialLift (paddingMass R) y

def collarEtaDivR (R : ℝ) (f : LogCollarData) (y : MP) : AP :=
  (1-radialLift (roundingWeight R) y) • f.etaDivR y

lemma collarQ_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    collarQ R f (slice ρ x)=CKSAngularGeometry.fieldQ (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  ext a b
  simp [collarQ,radialLift,CKSAngularGeometry.fieldQ,collarParams,LogCollarData.angular]
  field_simp

lemma collarShift_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    Real.exp ρ^5 • collarShift R f (slice ρ x)=
      CKSAngularGeometry.fieldS (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  ext a
  simp [collarShift,radialLift,CKSAngularGeometry.fieldS,collarParams,LogCollarData.angular]
  ring

lemma collarT_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    Real.exp ρ^3*(collarT R f (slice ρ x)-1)=
      CKSAngularGeometry.fieldT (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  simp [collarT,radialLift,CKSAngularGeometry.fieldT,collarParams,LogCollarData.angular]
  ring

lemma collarLb_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    Real.exp ρ^3*(collarLb R f (slice ρ x)-1)=
      CKSAngularGeometry.fieldL (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  simp [collarLb,radialLift,CKSAngularGeometry.fieldL,collarParams,LogCollarData.angular]
  ring

lemma collarF_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    collarF R f (slice ρ x)=CKSAngularGeometry.fieldF (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  simp [collarF,radialLift,CKSAngularGeometry.fieldF,collarParams,LogCollarData.angular]
  ring

lemma collarEta_slice (R ρ : ℝ) (f : LogCollarData) (x : AP) :
    Real.exp ρ^3 • collarEtaDivR R f (slice ρ x)=
      CKSAngularGeometry.fieldEta (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  ext a
  simp [collarEtaDivR,radialLift,CKSAngularGeometry.fieldEta,collarParams,LogCollarData.angular]
  ring

lemma collarQ_radial (R ρ : ℝ) {f : LogCollarData} {x : AP}
    (hf : f.RegularAt (slice ρ x))
    (hσ : ∀ a b, D (basis 0) (fun y => f.sigma y a b) (slice ρ x)=0) (a b : Fin 2) :
    Real.exp ρ^3*D (basis 0) (fun y => collarQ R f y a b) (slice ρ x)=
      CKSAngularGeometry.fieldQr (collarParams R (Real.exp ρ)) (f.angular ρ) x a b := by
  have he := radialLift_diff ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt (y := slice ρ x)
  have hs := (CKSMixedGeometry.component_diff hf.sigma a b).differentiableAt (by norm_num)
  have hm := (CKSMixedGeometry.component_diff hf.metricError a b).differentiableAt (by norm_num)
  change Real.exp ρ^3*D (basis 0) (fun y => f.sigma y a b+
    (1-radialLift (roundingWeight R) y)*f.metricError y a b) (slice ρ x)=_
  erw [D_add _ hs (((differentiableAt_const (1:ℝ)).sub he).mul hm),D_mul _ ((differentiableAt_const (1:ℝ)).sub he) hm,
    D_sub _ (differentiableAt_const (1:ℝ)) he,D_const,hσ,
    radialLift_D ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt]
  change _ = (1-roundingWeight R (Real.exp ρ))*(Real.exp ρ^3*
    D (basis 0) (fun y => f.metricError y a b) (slice ρ x))-
      (Real.exp ρ*deriv (roundingWeight R) (Real.exp ρ))*(Real.exp ρ^3*f.metricError (slice ρ x) a b)
  dsimp only [Pi.sub_apply,radialLift]
  simp only [slice_zero]
  ring

lemma collarT_radial (R ρ : ℝ) {f : LogCollarData} {x : AP}
    (hf : f.RegularAt (slice ρ x)) :
    Real.exp ρ^3*D (basis 0) (collarT R f) (slice ρ x)=
      CKSAngularGeometry.fieldTr (collarParams R (Real.exp ρ)) (f.angular ρ) x := by
  have he := radialLift_diff ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt (y := slice ρ x)
  have ht := hf.tError.differentiableAt (by norm_num)
  unfold collarT
  erw [D_add _ (differentiableAt_const (1:ℝ)) (((differentiableAt_const (1:ℝ)).sub he).mul ht),D_const,
    D_mul _ ((differentiableAt_const (1:ℝ)).sub he) ht,D_sub _ (differentiableAt_const (1:ℝ)) he,D_const,
    radialLift_D ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt]
  simp [CKSAngularGeometry.fieldTr,collarParams,LogCollarData.angular,radialLift]
  ring

lemma collarF_radial {R : ℝ} (hR : 0 < R) (ρ : ℝ) {f : LogCollarData} {x : AP}
    (hf : f.RegularAt (slice ρ x)) (hstar : D (basis 0) f.fstar (slice ρ x)=0) :
    D (basis 0) (collarF R f) (slice ρ x)=
      (1/Real.exp ρ)*((1-roundingWeight R (Real.exp ρ))*(f.angular ρ).massRadial x-
        (Real.exp ρ*deriv (roundingWeight R) (Real.exp ρ))*(f.angular ρ).massGap x)+
      Real.exp ρ*(paddingWeight R (Real.exp ρ)*(Real.exp ρ)^(-(3:ℝ)/2)) := by
  have he := radialLift_diff ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt (y := slice ρ x)
  have hpad := paddingMass_hasDerivAt hR (Real.exp_pos ((slice ρ x) 0))
  have hc := radialLift_diff hpad.differentiableAt
  have hm := hf.massError.differentiableAt (by norm_num)
  have hs := hf.fstar.differentiableAt (by norm_num)
  unfold collarF
  erw [D_add _ (hs.add (((differentiableAt_const (1:ℝ)).sub he).mul hm)) hc,
    D_add _ hs (((differentiableAt_const (1:ℝ)).sub he).mul hm),hstar,
    D_mul _ ((differentiableAt_const (1:ℝ)).sub he) hm,D_sub _ (differentiableAt_const (1:ℝ)) he,D_const,
    radialLift_D ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt,
    radialLift_D hpad.differentiableAt,hpad.deriv]
  dsimp only [Pi.sub_apply,radialLift]
  simp only [LogCollarData.angular,slice_zero]
  rw [paddingDensity_rpow (Real.exp_pos ρ)]
  field_simp
  ring

lemma collarEta_radial (R ρ : ℝ) {f : LogCollarData} {x : AP}
    (hf : f.RegularAt (slice ρ x)) (a : Fin 2) :
    Real.exp ρ^3*(collarEtaDivR R f (slice ρ x) a+
      D (basis 0) (fun y => collarEtaDivR R f y a) (slice ρ x))=
      CKSAngularGeometry.fieldEr (collarParams R (Real.exp ρ)) (f.angular ρ) x a := by
  have he := radialLift_diff ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt (y := slice ρ x)
  have ht := (contDiffAt_pi.mp hf.etaDivR a).differentiableAt (by norm_num)
  change Real.exp ρ^3*((1-radialLift (roundingWeight R) (slice ρ x))*f.etaDivR (slice ρ x) a+
    D (basis 0) (fun y => (1-radialLift (roundingWeight R) y)*f.etaDivR y a) (slice ρ x))=_
  erw [D_mul _ ((differentiableAt_const (1:ℝ)).sub he) ht,D_sub _ (differentiableAt_const (1:ℝ)) he,D_const,
    radialLift_D ((roundingWeight_smooth R).differentiable (by norm_num)).differentiableAt]
  simp [CKSAngularGeometry.fieldEr,collarParams,LogCollarData.angular,radialLift]
  ring

end
end CKSAngularSlice

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open Matrix CKSAngularGeometry

def sourceTensor (f : SourceTensorFields) (y : Point) : AmbientMat :=
  metricBlock (sourceRadialK f y) (f.kb y) (sourceTangentialK f.base y)
end
end CKSMixedGeometry

end

end OAI

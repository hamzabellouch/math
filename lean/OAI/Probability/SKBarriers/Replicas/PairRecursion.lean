import Mathlib
import OAI.Probability.SKBarriers.Scalar.VectorHierarchy
import OAI.Probability.SKBarriers.Scalar.ScalarTiltedExpectation

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianStep_half_double (m : ℝ) (f : E × ℝ → ℝ) :
    gaussianStep (m/2) (fun z => 2*f z)=fun x => 2*gaussianStep m f x := by
  funext x
  by_cases hm : m=0
  · subst m
    simp only [zero_div,gaussianStep,ite_true,integral_const_mul]
  · have hm2 : m/2≠0 := div_ne_zero hm (by norm_num)
    simp only [gaussianStep,ite_eq_right hm,ite_eq_right hm2,positiveGaussianLogStep]
    simp only [show ∀ y, m/2*(2*f (x,y))=m*f (x,y) by intro y; ring]
    ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianAverage_half_double (m : ℝ) (f g : E × ℝ → ℝ) :
    gaussianAverage (m/2) (fun z => 2*f z) g=gaussianAverage m f g := by
  unfold gaussianAverage gaussianStepLaw
  simp only [show ∀ z : E × ℝ, m/2*(2*f z)=m*f z by intro z; ring]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem gaussianAverage_add_prefix (m : ℝ) (f g : E × ℝ → ℝ) (c : E → ℝ) :
    gaussianAverage m (fun z => f z+c z.1) g=gaussianAverage m f g := by
  funext x
  have htilt : (gaussianReal 0 1).tilted (fun y => m*(f (x,y)+c x))=
      (gaussianReal 0 1).tilted (fun y => m*f (x,y)) := by
    have H := tilted_tilted (μ:=gaussianReal 0 1)
      (f:=fun _ : ℝ => m*c x) (integrable_const _) (fun y => m*f (x,y))
    rw [tilted_const] at H
    rw [H]
    congr 1
    funext y
    simp only [Pi.add_apply]
    ring
  exact congrArg (fun μ => ∫ y, g (x,y) ∂μ) htilt

def vectorStepAverage (m : ℝ) (v : E) (f g : E → ℝ) : E → ℝ :=
  gaussianAverage m (fun z : E × ℝ => f (z.1+z.2 • v)) (fun z => g (z.1+z.2 • v))
end Generic

def pairIndependentStep (m v : ℝ) (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  vectorStep m (v,0) (vectorStep m (0,v) f)

def pairIndependentAverage (m v : ℝ) (f g : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  vectorStepAverage m (v,0) (vectorStep m (0,v) f) (vectorStepAverage m (0,v) f g)

theorem vectorStep_pair_right {f g : ℝ → ℝ} (hg : BoundedDerivs g) (m v : ℝ) :
    vectorStep m (0,v) (fun p : ℝ × ℝ => f p.1+g p.2)=
      fun p => f p.1+scalarStep m v g p.2 := by
  let L : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+
      v • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hL : (fun z : (ℝ × ℝ) × ℝ => g (z.1.2+v*z.2))=g ∘ L := rfl
  have H := gaussianStep_add_prefix (hL.symm ▸ hg.compCLM L) (fun p : ℝ × ℝ => f p.1) m
  have he : (fun z : (ℝ × ℝ) × ℝ =>
      (fun p : ℝ × ℝ => f p.1+g p.2) (z.1+z.2 • (0,v)))=
      fun z => g (z.1.2+v*z.2)+f z.1.1 := by
    funext z
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,add_zero,mul_comm z.2 v,add_comm]
  rw [← hL] at H
  rw [vectorStep,he,H]
  funext p
  rw [add_comm]
  rfl

theorem vectorStep_pair_left {f g : ℝ → ℝ} (hf : BoundedDerivs f) (m v : ℝ) :
    vectorStep m (v,0) (fun p : ℝ × ℝ => f p.1+g p.2)=
      fun p => scalarStep m v f p.1+g p.2 := by
  let L : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+
      v • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  have hL : (fun z : (ℝ × ℝ) × ℝ => f (z.1.1+v*z.2))=f ∘ L := rfl
  have H := gaussianStep_add_prefix (hL.symm ▸ hf.compCLM L) (fun p : ℝ × ℝ => g p.2) m
  have he : (fun z : (ℝ × ℝ) × ℝ =>
      (fun p : ℝ × ℝ => f p.1+g p.2) (z.1+z.2 • (v,0)))=
      fun z => f (z.1.1+v*z.2)+g z.1.2 := by
    funext z
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,add_zero,mul_comm z.2 v]
  rw [← hL] at H
  rw [vectorStep,he,H]
  rfl

theorem pairIndependentStep_separate {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) (m v : ℝ) :
    pairIndependentStep m v (fun p => f p.1+g p.2)=
      fun p => scalarStep m v f p.1+scalarStep m v g p.2 := by
  rw [pairIndependentStep,vectorStep_pair_right hg,vectorStep_pair_left hf]

theorem vectorStepAverage_pair_right (f g a b : ℝ → ℝ) (m v : ℝ) :
    vectorStepAverage m (0,v) (fun p : ℝ × ℝ => f p.1+g p.2)
      (fun p => a p.1*b p.2)=fun p => a p.1*scalarStepAverage m v g b p.2 := by
  have he : (fun z : (ℝ × ℝ) × ℝ =>
      (fun p : ℝ × ℝ => f p.1+g p.2) (z.1+z.2 • (0,v)))=
      fun z => g (z.1.2+v*z.2)+f z.1.1 := by
    funext z
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,add_zero,mul_comm z.2 v,add_comm]
  rw [vectorStepAverage,he,gaussianAverage_add_prefix m (fun z : (ℝ × ℝ) × ℝ => g (z.1.2+v*z.2)) _ (fun p => f p.1)]
  funext p
  simp only [gaussianAverage,gaussianStepLaw,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
    mul_zero,add_zero,integral_const_mul,scalarStepAverage,mul_comm _ v]

theorem vectorStepAverage_pair_left (f g a b : ℝ → ℝ) (m v : ℝ) :
    vectorStepAverage m (v,0) (fun p : ℝ × ℝ => f p.1+g p.2)
      (fun p => a p.1*b p.2)=fun p => scalarStepAverage m v f a p.1*b p.2 := by
  have he : (fun z : (ℝ × ℝ) × ℝ =>
      (fun p : ℝ × ℝ => f p.1+g p.2) (z.1+z.2 • (v,0)))=
      fun z => f (z.1.1+v*z.2)+g z.1.2 := by
    funext z
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,mul_zero,add_zero,mul_comm z.2 v]
  rw [vectorStepAverage,he,gaussianAverage_add_prefix m (fun z : (ℝ × ℝ) × ℝ => f (z.1.1+v*z.2)) _ (fun p => g p.2)]
  funext p
  simp only [gaussianAverage,gaussianStepLaw,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
    mul_zero,add_zero,integral_mul_const,scalarStepAverage,mul_comm _ v]

theorem pairIndependentAverage_product {f g : ℝ → ℝ} (hg : BoundedDerivs g)
    (a b : ℝ → ℝ) (m v : ℝ) :
    pairIndependentAverage m v (fun p => f p.1+g p.2) (fun p => a p.1*b p.2)=
      fun p => scalarStepAverage m v f a p.1*scalarStepAverage m v g b p.2 := by
  rw [pairIndependentAverage,vectorStep_pair_right hg,vectorStepAverage_pair_right,
    vectorStepAverage_pair_left]

theorem vectorStep_pair_diagonal (F : ℝ × ℝ → ℝ) (f : ℝ → ℝ)
    (h : ∀ x, F (x,x)=2*f x) (m v x : ℝ) :
    vectorStep (m/2) (v,v) F (x,x)=2*scalarStep m v f x := by
  simp only [vectorStep,gaussianStep,positiveGaussianLogStep,Prod.mk_add_mk,Prod.smul_mk,
    smul_eq_mul,h,mul_comm _ v]
  by_cases hm : m=0
  · simp [hm,integral_const_mul,scalarStep,gaussianStep]
  · have hm2 : m/2≠0 := div_ne_zero hm (by norm_num)
    simp only [ite_eq_right hm2,scalarStep,gaussianStep,positiveGaussianLogStep,ite_eq_right hm]
    simp only [show ∀ y, m/2*(2*f (x+v*y))=m*f (x+v*y) by intro y; ring]
    ring

theorem vectorStepAverage_pair_diagonal (F G : ℝ × ℝ → ℝ) (f g : ℝ → ℝ)
    (h : ∀ x, F (x,x)=2*f x) (hg : ∀ x, G (x,x)=g x) (m v x : ℝ) :
    vectorStepAverage (m/2) (v,v) F G (x,x)=scalarStepAverage m v f g x := by
  change (∫ y, G (x+y*v,x+y*v) ∂(gaussianReal 0 1).tilted
    (fun y => (m/2)*F (x+y*v,x+y*v)))=
    ∫ y, g (x+v*y) ∂(gaussianReal 0 1).tilted (fun y => m*f (x+v*y))
  simp only [h,hg,mul_comm _ v]
  simp only [show ∀ y, m/2*(2*f (x+v*y))=m*f (x+v*y) by intro y; ring]

end SK.Analytic

end
end

end OAI

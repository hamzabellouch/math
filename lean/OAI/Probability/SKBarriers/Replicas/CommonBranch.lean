import Mathlib
import OAI.Probability.SKBarriers.Scalar.VectorAverage

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Generic
variable {E : Type}

theorem gaussianStep_div_scale (m c : ℝ) (hc : c≠0) (f : E × ℝ → ℝ) :
    gaussianStep (m/c) (fun z => c*f z)=fun x => c*gaussianStep m f x := by
  funext x
  by_cases hm : m=0
  · subst m; simp only [zero_div,gaussianStep,ite_true,integral_const_mul]
  · have hm2 : m/c≠0 := div_ne_zero hm hc
    have he : ∀ y, m/c*(c*f (x,y))=m*f (x,y) := by intro y; field_simp
    simp only [gaussianStep,ite_eq_right hm,ite_eq_right hm2,positiveGaussianLogStep,he]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring

theorem gaussianAverage_div_scale (m c : ℝ) (hc : c≠0) (f g : E × ℝ → ℝ) :
    gaussianAverage (m/c) (fun z => c*f z) g=gaussianAverage m f g := by
  unfold gaussianAverage gaussianStepLaw
  simp only [show ∀ z, m/c*(c*f z)=m*f z by intro z; field_simp]
end Generic
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStep_div_scale (m c : ℝ) (hc : c≠0) (v : E) (f : E → ℝ) :
    vectorStep (m/c) v (fun x => c*f x)=fun x => c*vectorStep m v f x :=
  gaussianStep_div_scale m c hc _

theorem vectorStepAverage_div_scale (m c : ℝ) (hc : c≠0) (v : E) (f g : E → ℝ) :
    vectorStepAverage (m/c) v (fun x => c*f x) g=vectorStepAverage m v f g :=
  gaussianAverage_div_scale m c hc _ _

theorem vectorHierarchy_div_scale (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (c : ℝ) (hc : c≠0) (f : E → ℝ) :
    vectorHierarchy n (fun i => m i/c) v (fun x => c*f x)=fun x => c*vectorHierarchy n m v f x := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [vectorHierarchy,vectorStep_div_scale _ c hc,ih]; rfl

theorem vectorHierarchyAverage_div_scale (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E)
    (c : ℝ) (hc : c≠0) (f g : E → ℝ) :
    vectorHierarchyAverage n (fun i => m i/c) v (fun x => c*f x) g=vectorHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    rw [vectorHierarchyAverage,vectorStep_div_scale _ c hc,vectorStepAverage_div_scale _ c hc,ih]
    rfl
end Vector

theorem vectorStep_real (m v : ℝ) (f : ℝ → ℝ) : vectorStep m v f=scalarStep m v f := by
  simp only [vectorStep,scalarStep,smul_eq_mul,mul_comm]

theorem vectorStepAverage_real (m v : ℝ) (f g : ℝ → ℝ) : vectorStepAverage m v f g=scalarStepAverage m v f g := by
  funext x
  simp only [vectorStepAverage,scalarStepAverage,gaussianAverage,gaussianStepLaw,smul_eq_mul,mul_comm]

theorem vectorHierarchy_real (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ) :
    vectorHierarchy n m v f=scalarHierarchy n m v f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [vectorHierarchy,vectorStep_real,ih]; rfl

theorem vectorHierarchyAverage_real (n : ℕ) (m v : Fin n → ℝ) (f g : ℝ → ℝ) :
    vectorHierarchyAverage n m v f g=scalarHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => rw [vectorHierarchyAverage,vectorStep_real,vectorStepAverage_real,ih]; rfl

def commonBranchEmbedding : ℝ →L[ℝ] (ℝ × ℝ) × ℝ :=
  ((ContinuousLinearMap.id ℝ ℝ).prod 0).prod (ContinuousLinearMap.id ℝ ℝ)

@[simp] theorem commonBranchEmbedding_apply (x : ℝ) : commonBranchEmbedding x=((x,0),x) := rfl

theorem commonBranch_value (n : ℕ) (m v : Fin n → ℝ) (f : ℝ → ℝ) (x : ℝ) :
    vectorHierarchy n (fun i => m i/3) (fun i => ((v i,0),v i))
      (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2) ((x,0),x)=3*scalarHierarchy n m v f x := by
  have H := congrFun (vectorHierarchy_pullback commonBranchEmbedding n (fun i => m i/3) v
    (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2)) x
  have he : (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2) ∘ commonBranchEmbedding=fun x => 3*f x := by
    funext x; simp only [Function.comp_apply,commonBranchEmbedding_apply]; ring
  rw [he,vectorHierarchy_div_scale n m v 3 (by norm_num),vectorHierarchy_real] at H
  exact H.symm

theorem commonBranch_average (n : ℕ) (m v : Fin n → ℝ) (f b : ℝ → ℝ) (a : ℝ × ℝ → ℝ) (x : ℝ) :
    vectorHierarchyAverage n (fun i => m i/3) (fun i => ((v i,0),v i))
      (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2)
      (fun p => a p.1*b p.2) ((x,0),x)=scalarHierarchyAverage n m v f (fun y => a (y,0)*b y) x := by
  have H := congrFun (vectorHierarchyAverage_pullback commonBranchEmbedding n (fun i => m i/3) v
    (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2) (fun p => a p.1*b p.2)) x
  have he : (fun p : (ℝ × ℝ) × ℝ => f p.1.1+2*f p.2) ∘ commonBranchEmbedding=fun x => 3*f x := by
    funext x; simp only [Function.comp_apply,commonBranchEmbedding_apply]; ring
  rw [he,vectorHierarchyAverage_div_scale n m v 3 (by norm_num),vectorHierarchyAverage_real] at H
  exact H.symm

end SK.Analytic

end
end

end OAI

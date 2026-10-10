import Mathlib
import OAI.Probability.SKBarriers.Scalar.VectorAverage

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorTranslation (v : E) : (E × ℝ) →L[ℝ] E :=
  ContinuousLinearMap.fst ℝ E ℝ + (ContinuousLinearMap.snd ℝ E ℝ).smulRight v

theorem vectorStep_regular {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) (v : E) :
    BoundedDerivs (vectorStep m v f) :=
  (hf.compCLM (vectorTranslation v)).gaussianStep m

def vectorIncrementChain : List (ℝ × E) → (E → ℝ) → E → ℝ
  | [], f => f
  | p::l, f => vectorStep p.1 p.2 (vectorIncrementChain l f)

def vectorIncrementAverage : List (ℝ × E) → (E → ℝ) → (E → ℝ) → E → ℝ
  | [], _, g => g
  | p::l, f, g => vectorStepAverage p.1 p.2 (vectorIncrementChain l f)
      (vectorIncrementAverage l f g)

theorem vectorIncrementChain_regular (l : List (ℝ × E)) {f : E → ℝ}
    (hf : BoundedDerivs f) : BoundedDerivs (vectorIncrementChain l f) := by
  induction l with
  | nil => exact hf
  | cons p l ih => exact vectorStep_regular ih p.1 p.2

theorem vectorIncrementChain_append (l r : List (ℝ × E)) (f : E → ℝ) :
    vectorIncrementChain (l++r) f=vectorIncrementChain l (vectorIncrementChain r f) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,vectorIncrementChain,ih]

theorem vectorIncrementAverage_append (l r : List (ℝ × E)) (f g : E → ℝ) :
    vectorIncrementAverage (l++r) f g=
      vectorIncrementAverage l (vectorIncrementChain r f) (vectorIncrementAverage r f g) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.cons_append,vectorIncrementAverage,vectorIncrementChain_append,ih]

theorem vectorIncrementChain_ofFn (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E) (f : E → ℝ) :
    vectorIncrementChain (List.ofFn (fun i => (m i,v i))) f=vectorHierarchy n m v f := by
  induction n generalizing f with
  | zero => simp [vectorIncrementChain,vectorHierarchy]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,vectorIncrementChain_append]
    exact ih _ _ _

theorem vectorIncrementAverage_ofFn (n : ℕ) (m : Fin n → ℝ) (v : Fin n → E) (f g : E → ℝ) :
    vectorIncrementAverage (List.ofFn (fun i => (m i,v i))) f g=vectorHierarchyAverage n m v f g := by
  induction n generalizing f g with
  | zero => simp [vectorIncrementAverage,vectorHierarchyAverage]
  | succ n ih =>
    rw [List.ofFn_succ',List.concat_eq_append,vectorIncrementAverage_append]
    exact ih _ _ _ _

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vectorStep_prod_left {f : E → ℝ} (hf : BoundedDerivs f) (g : F → ℝ) (m : ℝ) (v : E) :
    vectorStep m (v,0) (fun p : E × F => f p.1+g p.2)=
      fun p => vectorStep m v f p.1+g p.2 := by
  let L : ((E × F) × ℝ) →L[ℝ] E :=
    (ContinuousLinearMap.fst ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) ℝ)+
      (ContinuousLinearMap.snd ℝ (E × F) ℝ).smulRight v
  have H := gaussianStep_add_prefix (hf.compCLM L) (fun p : E × F => g p.2) m
  simpa only [vectorStep,Function.comp_def,L,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd',Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero,gaussianStep,positiveGaussianLogStep] using H

theorem vectorStep_prod_right (f : E → ℝ) {g : F → ℝ} (hg : BoundedDerivs g) (m : ℝ) (v : F) :
    vectorStep m (0,v) (fun p : E × F => f p.1+g p.2)=
      fun p => f p.1+vectorStep m v g p.2 := by
  let L : ((E × F) × ℝ) →L[ℝ] F :=
    (ContinuousLinearMap.snd ℝ E F).comp (ContinuousLinearMap.fst ℝ (E × F) ℝ)+
      (ContinuousLinearMap.snd ℝ (E × F) ℝ).smulRight v
  have H := gaussianStep_add_prefix (hg.compCLM L) (fun p : E × F => f p.1) m
  simpa only [vectorStep,Function.comp_def,L,add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd',Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero,add_comm,gaussianStep,positiveGaussianLogStep] using H

theorem vectorStepAverage_prod_left (f a : E → ℝ) (g b : F → ℝ) (m : ℝ) (v : E) :
    vectorStepAverage m (v,0) (fun p : E × F => f p.1+g p.2) (fun p => a p.1*b p.2)=
      fun p => vectorStepAverage m v f a p.1*b p.2 := by
  unfold vectorStepAverage
  simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero]
  rw [gaussianAverage_add_prefix m (fun z : (E × F) × ℝ => f (z.1.1+z.2 • v)) _ (fun p => g p.2)]
  funext p
  simp only [gaussianAverage,gaussianStepLaw,integral_mul_const]

theorem vectorStepAverage_prod_right (f a : E → ℝ) (g b : F → ℝ) (m : ℝ) (v : F) :
    vectorStepAverage m (0,v) (fun p : E × F => f p.1+g p.2) (fun p => a p.1*b p.2)=
      fun p => a p.1*vectorStepAverage m v g b p.2 := by
  unfold vectorStepAverage
  simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero]
  simp_rw [add_comm (f _) (g _)]
  rw [gaussianAverage_add_prefix m (fun z : (E × F) × ℝ => g (z.1.2+z.2 • v)) _ (fun p => f p.1)]
  funext p
  simp only [gaussianAverage,gaussianStepLaw,integral_const_mul]

abbrev ProductIncrement := Sum (ℝ × E) (ℝ × F)

def productMass : ProductIncrement (E:=E) (F:=F) → ℝ
  | .inl p => p.1
  | .inr p => p.1/2

def productVector : ProductIncrement (E:=E) (F:=F) → E × F
  | .inl p => (p.2,0)
  | .inr p => (0,p.2)

def productLeft (l : List (ProductIncrement (E:=E) (F:=F))) : List (ℝ × E) :=
  l.filterMap (fun p => match p with | .inl q => some q | .inr _ => none)

def productRight (l : List (ProductIncrement (E:=E) (F:=F))) : List (ℝ × F) :=
  l.filterMap (fun p => match p with | .inl _ => none | .inr q => some q)

def productBranchChain (l : List (ProductIncrement (E:=E) (F:=F))) : (E × F → ℝ) → E × F → ℝ :=
  vectorIncrementChain (l.map (fun p => (productMass p,productVector p)))

def productBranchAverage (l : List (ProductIncrement (E:=E) (F:=F))) :
    (E × F → ℝ) → (E × F → ℝ) → E × F → ℝ :=
  vectorIncrementAverage (l.map (fun p => (productMass p,productVector p)))

theorem vectorStep_half_double (m : ℝ) (v : E) (f : E → ℝ) :
    vectorStep (m/2) v (fun x => 2*f x)=fun x => 2*vectorStep m v f x :=
  gaussianStep_half_double m _

theorem vectorStepAverage_half_double (m : ℝ) (v : E) (f g : E → ℝ) :
    vectorStepAverage (m/2) v (fun x => 2*f x) g=vectorStepAverage m v f g :=
  gaussianAverage_half_double m _ _

theorem productBranchChain_factor (l : List (ProductIncrement (E:=E) (F:=F)))
    {f : E → ℝ} {g : F → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) :
    productBranchChain l (fun p => f p.1+2*g p.2)=
      fun p => vectorIncrementChain (productLeft l) f p.1+
        2*vectorIncrementChain (productRight l) g p.2 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change vectorStep (productMass p) (productVector p) (productBranchChain l _) = _
    rw [ih]
    cases p with
    | inl p =>
      simpa only [productMass,productVector,productLeft,productRight,List.filterMap_cons,vectorIncrementChain] using
        vectorStep_prod_left (vectorIncrementChain_regular (productLeft l) hf)
          (fun z => 2*vectorIncrementChain (productRight l) g z) p.1 p.2
    | inr p =>
      change vectorStep (p.1/2) (0,p.2)
        (fun z => vectorIncrementChain (productLeft l) f z.1+2*vectorIncrementChain (productRight l) g z.2)=_
      rw [vectorStep_prod_right _ ((vectorIncrementChain_regular _ hg).const_mul 2),vectorStep_half_double]
      rfl

theorem productBranchAverage_factor (l : List (ProductIncrement (E:=E) (F:=F)))
    {f : E → ℝ} {g : F → ℝ} (hf : BoundedDerivs f) (hg : BoundedDerivs g) (a : E → ℝ) (b : F → ℝ) :
    productBranchAverage l (fun p => f p.1+2*g p.2) (fun p => a p.1*b p.2)=
      fun p => vectorIncrementAverage (productLeft l) f a p.1*
        vectorIncrementAverage (productRight l) g b p.2 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change vectorStepAverage (productMass p) (productVector p) (productBranchChain l _)
      (productBranchAverage l _ _) = _
    rw [productBranchChain_factor l hf hg,ih]
    cases p with
    | inl p =>
      simpa only [productMass,productVector,productLeft,productRight,List.filterMap_cons,vectorIncrementAverage] using
        vectorStepAverage_prod_left (vectorIncrementChain (productLeft l) f)
          (vectorIncrementAverage (productLeft l) f a) (fun z => 2*vectorIncrementChain (productRight l) g z)
          (vectorIncrementAverage (productRight l) g b) p.1 p.2
    | inr p =>
      change vectorStepAverage (p.1/2) (0,p.2)
        (fun z => vectorIncrementChain (productLeft l) f z.1+2*vectorIncrementChain (productRight l) g z.2)
        (fun z => vectorIncrementAverage (productLeft l) f a z.1*vectorIncrementAverage (productRight l) g b z.2)=_
      rw [vectorStepAverage_prod_right (vectorIncrementChain (productLeft l) f)
        (vectorIncrementAverage (productLeft l) f a) (fun z => 2*vectorIncrementChain (productRight l) g z)
        (vectorIncrementAverage (productRight l) g b),vectorStepAverage_half_double]
      rfl
end Vector

end SK.Analytic

end
end

end OAI

import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyPenalty
import OAI.Probability.SKBarriers.Hierarchy.CascadeRecursion

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology NNReal
namespace SK.Analytic
attribute [-instance] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def hierarchyLevel : (n : ℕ) → (Fin n → ℝ) → (ParameterSpace n → ℝ) →
    Fin (n+1) → ParameterSpace n → ℝ
  | 0,_,f,_ => f
  | n+1,m,f,j => Fin.lastCases f (fun i z =>
      hierarchyLevel n (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) i z.1) j

def hierarchyAtom : (n : ℕ) → (Fin n → ℝ) → ℝ → Fin (n+1) → ℝ
  | 0,_,u,_ => u
  | n+1,m,u,j => Fin.lastCases (u-m (Fin.last n))
      (hierarchyAtom n (fun i => m i.castSucc) (m (Fin.last n))) j

theorem hierarchyLevel_boundedDerivs (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1)) :
    BoundedDerivs (hierarchyLevel n m f j) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [hierarchyLevel,Fin.lastCases_last] using hf
    · simp only [hierarchyLevel,Fin.lastCases_castSucc]
      let P : ParameterSpace (n+1) →L[ℝ] ParameterSpace n :=
        ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
      exact (ih (fun i => m i.castSucc) _ (hf.gaussianStep (m (Fin.last n))) i).compCLM P

theorem hierarchyPenalty_sum (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (z : ParameterSpace n) :
    hierarchyPenalty n m u f z = ∑ j, hierarchyAtom n m u j*hierarchyLevel n m f j z := by
  induction n generalizing u with
  | zero => simp [hierarchyPenalty,hierarchyLevel,hierarchyAtom]
  | succ n ih =>
    rw [hierarchyPenalty,ih (fun i => m i.castSucc) (m (Fin.last n))]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    simp only [hierarchyAtom,hierarchyLevel,Fin.lastCases_last,Fin.lastCases_castSucc]
    ring

theorem fderiv_hierarchyPenalty_apply (n : ℕ) (m : Fin n → ℝ) (u : ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (z v : ParameterSpace n) :
    fderiv ℝ (hierarchyPenalty n m u f) z v =
      ∑ j, hierarchyAtom n m u j*fderiv ℝ (hierarchyLevel n m f j) z v := by
  have he : hierarchyPenalty n m u f = fun z =>
      ∑ j, hierarchyAtom n m u j*hierarchyLevel n m f j z := funext (hierarchyPenalty_sum n m u f)
  rw [he]
  have hd := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((hierarchyLevel_boundedDerivs n m f hf j).1.differentiable (by norm_num) z).hasFDerivAt.const_mul
      (hierarchyAtom n m u j))
  rw [hd.fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul]

section Translation
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def TranslationInvariant (f : E → ℝ) (u : E) : Prop := ∀ (z : E) (t : ℝ), f (z+t • u) = f z

theorem TranslationInvariant.fderiv_zero {f : E → ℝ} {u : E}
    (hi : TranslationInvariant f u) (hf : Differentiable ℝ f) (z : E) : fderiv ℝ f z u = 0 := by
  have hd₀ : HasDerivAt (fun t : ℝ => z+t • u) u 0 := by
    convert (hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id (0 : ℝ)).smul_const u) using 1
    · rfl
    · simp
  have hd := (hf (z+(0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt 0 hd₀
  have he : (fun t : ℝ => f (z+t • u)) = fun _ => f z := funext (hi z)
  simp only [zero_smul,add_zero] at hd
  change HasDerivAt (fun t : ℝ => f (z+t • u)) (fderiv ℝ f z u) 0 at hd
  rw [he] at hd
  exact hd.unique (hasDerivAt_const 0 (f z))

theorem TranslationInvariant.gaussianStep {f : E × ℝ → ℝ} {u : E}
    (hi : TranslationInvariant f (u,0)) (m : ℝ) : TranslationInvariant (gaussianStep m f) u := by
  intro z t
  have he (y : ℝ) : f (z+t • u,y) = f (z,y) := by
    simpa only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero] using hi (z,y) t
  unfold SK.Analytic.gaussianStep positiveGaussianLogStep
  simp only [he]

theorem affineLogPartition_translation {S : Type} [Fintype S]
    (c : S → ℝ) (L : S → E →L[ℝ] ℝ) (u : E) (hu : ∀ s, L s u = 0) :
    TranslationInvariant (affineLogPartition c L) u := by
  intro z t
  simp only [affineLogPartition,map_add,map_smul,hu,smul_eq_mul,mul_zero,add_zero]

end Translation

def TailZero : (n : ℕ) → Fin (n+1) → ParameterSpace n → Prop
  | 0,_,_ => True
  | n+1,j,z => Fin.lastCases True (fun i => z.2 = 0 ∧ TailZero n i z.1) j

def PrefixZero : (n : ℕ) → Fin (n+1) → ParameterSpace n → Prop
  | 0,_,z => z = 0
  | n+1,j,z => Fin.lastCases (z = 0) (fun i => PrefixZero n i z.1) j

theorem hierarchyLevel_invariant_of_tail (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (u : ParameterSpace n) (hi : TranslationInvariant f u)
    (j : Fin (n+1)) (hz : TailZero n j u) : TranslationInvariant (hierarchyLevel n m f j) u := by
  induction n with
  | zero => exact hi
  | succ n ih =>
    revert hz
    refine Fin.lastCases (fun _ => ?_) (fun j hz => ?_) j
    · simpa only [hierarchyLevel,Fin.lastCases_last] using hi
    simp only [TailZero,Fin.lastCases_castSucc] at hz
    have hz' : u.2 = 0 ∧ TailZero n j u.1 := hz
    have hui : u = (u.1,0) := Prod.ext rfl hz'.1
    have hi' : TranslationInvariant f (u.1,0) := hui ▸ hi
    have H := ih (fun i => m i.castSucc) _ u.1 (hi'.gaussianStep (m (Fin.last n))) j hz'.2
    intro z t
    simpa only [hierarchyLevel,Fin.lastCases_castSucc,Prod.fst_add,Prod.smul_fst] using H z.1 t

theorem hierarchyLevel_invariant_of_prefix (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (u : ParameterSpace n) (j : Fin (n+1))
    (hz : PrefixZero n j u) : TranslationInvariant (hierarchyLevel n m f j) u := by
  induction n with
  | zero => simp only [PrefixZero] at hz; subst u; intro z t; simp
  | succ n ih =>
    revert hz
    refine Fin.lastCases (fun hz => ?_) (fun j hz => ?_) j
    · simp only [PrefixZero,Fin.lastCases_last] at hz
      subst u
      intro z t
      simp
    · simp only [PrefixZero,Fin.lastCases_castSucc] at hz
      have H := ih (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f) u.1 j hz
      intro z t
      simpa only [hierarchyLevel,Fin.lastCases_castSucc,Prod.fst_add,Prod.smul_fst] using H z.1 t

end SK.Analytic

end
end
end
end
end
end
end

end OAI

import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianResponse
import OAI.Probability.SKBarriers.Hierarchy.HierarchyPathLaw
import OAI.Probability.SKBarriers.Hierarchy.HierarchyLevels

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
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section TranslationMoments
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem TranslationInvariant.directionalGradient {f : E → ℝ} {u : E}
    (hi : TranslationInvariant f u) (v : E) : TranslationInvariant (directionalGradient f v) u := by
  intro z t
  unfold SK.Analytic.directionalGradient
  rw [← fderiv_comp_add_right (t • u)]
  have he : (fun z => f (z+t • u)) = f := funext (fun z => hi z t)
  rw [he]

theorem gaussianAverage_const_prefix {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (m : ℝ) (g : E → ℝ) : gaussianAverage m f (fun z => g z.1) = g := by
  funext z
  let := gaussianStepLaw_probability hf m z
  simp [gaussianAverage]

theorem TranslationInvariant.gaussianAverage {f g : E × ℝ → ℝ} {u : E}
    (hi : TranslationInvariant f (u,0)) (hig : TranslationInvariant g (u,0)) (m : ℝ) :
    TranslationInvariant (gaussianAverage m f g) u := by
  intro z t
  have he (y : ℝ) : f (z+t • u,y) = f (z,y) := by
    simpa only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero] using hi (z,y) t
  have heg (y : ℝ) : g (z+t • u,y) = g (z,y) := by
    simpa only [Prod.smul_mk,smul_zero,Prod.mk_add_mk,add_zero] using hig (z,y) t
  unfold SK.Analytic.gaussianAverage gaussianStepLaw
  simp only [he,heg]
end TranslationMoments

def hierarchyMomentLevel : (n : ℕ) → (Fin n → ℝ) → (ParameterSpace n → ℝ) →
    (ParameterSpace n → ℝ) → Fin (n+1) → ParameterSpace n → ℝ
  | 0,_,_,g,_ => g
  | n+1,m,f,g,j => Fin.lastCases g (fun i z => hierarchyMomentLevel n
      (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
      (gaussianAverage (m (Fin.last n)) f g) i z.1) j

theorem hierarchyMomentLevel_bounded_continuous (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (hg : Continuous g)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ z, ‖g z‖ ≤ C) (j : Fin (n+1)) :
    Continuous (hierarchyMomentLevel n m f g j) ∧
      ∀ z, ‖hierarchyMomentLevel n m f g j z‖ ≤ C := by
  induction n with
  | zero => exact ⟨hg,hb⟩
  | succ n ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using And.intro hg hb
    · have H := ih (fun i => m i.castSucc) (gaussianStep (m (Fin.last n)) f)
        (gaussianAverage (m (Fin.last n)) f g) (hf.gaussianStep (m (Fin.last n)))
        (gaussianAverage_continuous hf (m (Fin.last n)) hg hC hb)
        (fun z => gaussianAverage_norm_le hf (m (Fin.last n)) hb z) i
      simp only [hierarchyMomentLevel,Fin.lastCases_castSucc]
      exact ⟨H.1.comp continuous_fst,fun z => H.2 z.1⟩

theorem hierarchyMomentLevel_invariant_of_tail (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (u : ParameterSpace n)
    (hi : TranslationInvariant f u) (hig : TranslationInvariant g u)
    (j : Fin (n+1)) (hz : TailZero n j u) : TranslationInvariant (hierarchyMomentLevel n m f g j) u := by
  induction n with
  | zero => exact hig
  | succ n ih =>
    revert hz
    refine Fin.lastCases (fun _ => ?_) (fun j hz => ?_) j
    · simpa only [hierarchyMomentLevel,Fin.lastCases_last] using hig
    simp only [TailZero,Fin.lastCases_castSucc] at hz
    have hui : u = (u.1,0) := Prod.ext rfl hz.1
    have hi' : TranslationInvariant f (u.1,0) := hui ▸ hi
    have hig' : TranslationInvariant g (u.1,0) := hui ▸ hig
    have H := ih (fun i => m i.castSucc) _ _ u.1 (hi'.gaussianStep (m (Fin.last n)))
      (hi'.gaussianAverage hig' (m (Fin.last n))) j hz.2
    intro z t
    simpa only [hierarchyMomentLevel,Fin.lastCases_castSucc,Prod.fst_add,Prod.smul_fst] using H z.1 t

theorem hierarchyAverage_momentLevel (n : ℕ) (m : Fin n → ℝ)
    (f g : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1)) (x : ℝ) :
    hierarchyAverage n m f (hierarchyMomentLevel n m f g j) x = hierarchyAverage n m f g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [hierarchyMomentLevel,Fin.lastCases_last]
    · simp only [hierarchyMomentLevel,Fin.lastCases_castSucc,hierarchyAverage]
      rw [gaussianAverage_const_prefix hf]
      exact ih (fun i => m i.castSucc) _ _ (hf.gaussianStep _) j

theorem hierarchyLevel_gradient (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (j : Fin (n+1))
    (u z : ParameterSpace n) (hz : TailZero n j u) :
    fderiv ℝ (hierarchyLevel n m f j) z u =
      hierarchyMomentLevel n m f (directionalGradient f u) j z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    revert hz
    refine Fin.lastCases (fun _ => ?_) (fun j hz => ?_) j
    · simp only [hierarchyLevel,hierarchyMomentLevel,Fin.lastCases_last,directionalGradient]
    · simp only [TailZero,Fin.lastCases_castSucc] at hz
      simp only [hierarchyLevel,hierarchyMomentLevel,Fin.lastCases_castSucc]
      let f' := gaussianStep (m (Fin.last n)) f
      let P : ParameterSpace (n+1) →L[ℝ] ParameterSpace n :=
        ContinuousLinearMap.fst ℝ (ParameterSpace n) ℝ
      have hD := ((hierarchyLevel_boundedDerivs n (fun i => m i.castSucc) f'
        (hf.gaussianStep _) j).1.differentiable (by norm_num) z.1).hasFDerivAt.comp z
        P.hasFDerivAt
      change fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j ∘ P) z u = _
      have hDeq : fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j ∘ P) z =
          (fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j) z.1).comp P := hD.fderiv
      rw [hDeq]
      change fderiv ℝ (hierarchyLevel n (fun i => m i.castSucc) f' j) z.1 u.1 = _
      rw [ih (fun i => m i.castSucc) f' (hf.gaussianStep _) j u.1 z.1 hz.2]
      have he : directionalGradient f' u.1 = gaussianAverage (m (Fin.last n)) f (directionalGradient f u) := by
        funext y
        rw [directionalGradient,fderiv_gaussianStep_apply hf]
        have hui : u = (u.1,0) := Prod.ext rfl hz.1
        rw [hui]
        rfl
      rw [he]

end SK.Analytic

end
end
end
end
end
end
end

end OAI

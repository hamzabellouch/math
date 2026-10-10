import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.CascadeBlockLaw

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
section Generic
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BoundedDerivs.hasExpGrowth {f : E → ℝ} (hf : BoundedDerivs f) : HasExpGrowth f := by
  obtain ⟨hd,C,D,hC,_hD,h₁,_h₂⟩ := hf
  exact growth_of_fderiv_bound f (hd.differentiable (by norm_num)) hC h₁

theorem gaussianStep_add_prefix {f : E × ℝ → ℝ} (hf : BoundedDerivs f)
    (c : E → ℝ) (m : ℝ) :
    gaussianStep m (fun z => f z+c z.1) = fun x => gaussianStep m f x+c x := by
  funext x
  by_cases hm : m=0
  · subst m
    simp only [gaussianStep,ite_true]
    rw [integral_add (hf.hasExpGrowth.integrable_gaussian_section hf.1.continuous x)
      (integrable_const _)]
    simp
  · simp only [gaussianStep,ite_eq_right hm,positiveGaussianLogStep,mul_add,Real.exp_add]
    rw [integral_mul_const,Real.log_mul (integral_exp_pos (hf.exp_integrable m x)).ne'
      (Real.exp_ne_zero _),Real.log_exp,add_div,mul_div_cancel_left₀ _ hm]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in

theorem gaussianStep_prefix (c : E → ℝ) (m : ℝ) :
    gaussianStep m (fun z : E × ℝ => c z.1) = c := by
  funext x
  by_cases hm : m=0
  · simp [gaussianStep,hm]
  · simp [gaussianStep,hm,positiveGaussianLogStep]

theorem gaussianStep_sum_independent {I : Type} [Fintype I] [DecidableEq I]
    (f : I → E × ℝ → ℝ) (hf : ∀ i, BoundedDerivs (f i)) (j : I)
    (hi : ∀ i, i ≠ j → TranslationInvariant (f i) (0,1)) (m : ℝ) :
    gaussianStep m (fun z => ∑ i, f i z) = fun x => ∑ i, gaussianStep m (f i) x := by
  have he (i : I) (h : i ≠ j) (x : E) (y : ℝ) : f i (x,y) = f i (x,0) := by
    simpa using hi i h (x,0) y
  have hex : (fun z => ∑ i, f i z) = fun z => f j z+∑ i ∈ Finset.univ.erase j, f i (z.1,0) := by
    funext z
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    apply Finset.sum_congr rfl
    intro i h
    exact he i (Finset.mem_erase.mp h).1 z.1 z.2
  rw [hex,gaussianStep_add_prefix (hf j) (fun x => ∑ i ∈ Finset.univ.erase j, f i (x,0)) m]
  funext x
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  congr 1
  apply Finset.sum_congr rfl
  intro i h
  have H : f i = fun z => f i (z.1,0) := funext (fun z => he i (Finset.mem_erase.mp h).1 z.1 z.2)
  rw [H,gaussianStep_prefix (fun y => f i (y,0)) m]
end Generic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPressure_zero (n : ℕ) (f : ParameterSpace n → ℝ)
    (hf : BoundedDerivs f) (x : ℝ) :
    hierarchyPressure n (fun _ => 0) f x = ∫ z, f z ∂fiberGaussian n x := by
  induction n with
  | zero => simp [hierarchyPressure,fiberGaussian]
  | succ n ih =>
    rw [hierarchyPressure,ih _ (hf.gaussianStep 0),fiberGaussian,
      integral_prod _ (hf.hasExpGrowth.integrable_fiberGaussian (n+1) hf.1.continuous x)]
    simp only [gaussianStep,ite_true]

theorem hierarchyPressure_sum_independent {I : Type} [Fintype I] [DecidableEq I]
    (n : ℕ) (m : Fin n → ℝ) (owner : Fin n → I)
    (f : I → ParameterSpace n → ℝ) (hf : ∀ i, BoundedDerivs (f i))
    (hi : ∀ t i, i ≠ owner t → TranslationInvariant (f i) (coordinateAxis n t)) :
    hierarchyPressure n m (fun z => ∑ i, f i z) = fun x => ∑ i, hierarchyPressure n m (f i) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hierarchyPressure,gaussianStep_sum_independent f hf (owner (Fin.last n))
      (by simpa only [coordinateAxis_last] using hi (Fin.last n))]
    rw [ih (fun t => m t.castSucc) (fun t => owner t.castSucc)
      (fun i => gaussianStep (m (Fin.last n)) (f i))
      (fun i => (hf i).gaussianStep _) (fun t i h => ?_)]
    · rfl
    · apply TranslationInvariant.gaussianStep
      simpa only [coordinateAxis_castSucc] using hi t.castSucc i h
end SK.Analytic

end
end

end

end OAI

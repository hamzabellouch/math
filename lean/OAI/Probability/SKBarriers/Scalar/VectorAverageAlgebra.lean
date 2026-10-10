import Mathlib
import OAI.Probability.SKBarriers.Gaussian.GaussianStepSandwich
import OAI.Probability.SKBarriers.Hierarchy.IncrementListAnalytic

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Vector
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vectorStepAverage_add {f g h : E → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hgE : HasExpGrowth g) (hhE : HasExpGrowth h)
    (m : ℝ) (v : E) :
    vectorStepAverage m v f (fun x => g x+h x)=
      fun x => vectorStepAverage m v f g x+vectorStepAverage m v f h x := by
  funext x
  exact integral_add ((hgE.compCLM (vectorTranslation v)).integrable_gaussianStepLaw
    (hf.compCLM (vectorTranslation v)) (hg.comp (vectorTranslation v).continuous) m x)
    ((hhE.compCLM (vectorTranslation v)).integrable_gaussianStepLaw
    (hf.compCLM (vectorTranslation v)) (hh.comp (vectorTranslation v).continuous) m x)

theorem vectorStepAverage_const_mul (f g : E → ℝ) (m : ℝ) (v : E) (c : ℝ) :
    vectorStepAverage m v f (fun x => c*g x)=fun x => c*vectorStepAverage m v f g x := by
  funext x
  exact integral_const_mul c _

theorem vectorStepAverage_const {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) (v : E) (c : ℝ) :
    vectorStepAverage m v f (fun _ => c)=fun _ => c := by
  funext x
  let : IsProbabilityMeasure (gaussianStepLaw m (f ∘ vectorTranslation v) x) :=
    gaussianStepLaw_probability (hf.compCLM (vectorTranslation v)) m x
  change (∫ _y, c ∂gaussianStepLaw m (f ∘ vectorTranslation v) x)=c
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem vectorStepAverage_mono {f g h : E → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hgE : HasExpGrowth g) (hhE : HasExpGrowth h)
    (hle : ∀ x,g x≤h x) (m : ℝ) (v x : E) :
    vectorStepAverage m v f g x≤vectorStepAverage m v f h x := by
  exact integral_mono ((hgE.compCLM (vectorTranslation v)).integrable_gaussianStepLaw
    (hf.compCLM (vectorTranslation v)) (hg.comp (vectorTranslation v).continuous) m x)
    ((hhE.compCLM (vectorTranslation v)).integrable_gaussianStepLaw
    (hf.compCLM (vectorTranslation v)) (hh.comp (vectorTranslation v).continuous) m x)
    (fun _ => hle _)

theorem vectorIncrementAverage_add (l : List (ℝ × E)) {f g h : E → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hgE : HasExpGrowth g) (hhE : HasExpGrowth h) :
    vectorIncrementAverage l f (fun x => g x+h x)=
      fun x => vectorIncrementAverage l f g x+vectorIncrementAverage l f h x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change vectorStepAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f _) = _
    rw [ih]
    have G := vectorIncrementAverage_regular l hf hg hgE
    have H := vectorIncrementAverage_regular l hf hh hhE
    exact vectorStepAverage_add (vectorIncrementChain_regular l hf) G.1 H.1 G.2 H.2 p.1 p.2

theorem vectorIncrementAverage_const_mul (l : List (ℝ × E)) (f g : E → ℝ) (c : ℝ) :
    vectorIncrementAverage l f (fun x => c*g x)=fun x => c*vectorIncrementAverage l f g x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change vectorStepAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f _) = _
    rw [ih,vectorStepAverage_const_mul]
    rfl

theorem vectorIncrementAverage_const (l : List (ℝ × E)) {f : E → ℝ} (hf : BoundedDerivs f) (c : ℝ) :
    vectorIncrementAverage l f (fun _ => c)=fun _ => c := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    change vectorStepAverage p.1 p.2 (vectorIncrementChain l f) (vectorIncrementAverage l f _) = _
    rw [ih]
    exact vectorStepAverage_const (vectorIncrementChain_regular l hf) p.1 p.2 c

theorem vectorIncrementAverage_mono (l : List (ℝ × E)) {f g h : E → ℝ} (hf : BoundedDerivs f)
    (hg : Continuous g) (hh : Continuous h) (hgE : HasExpGrowth g) (hhE : HasExpGrowth h)
    (hle : ∀ x,g x≤h x) (x : E) :
    vectorIncrementAverage l f g x≤vectorIncrementAverage l f h x := by
  induction l generalizing x with
  | nil => exact hle x
  | cons p l ih =>
    have G := vectorIncrementAverage_regular l hf hg hgE
    have H := vectorIncrementAverage_regular l hf hh hhE
    exact vectorStepAverage_mono (vectorIncrementChain_regular l hf) G.1 H.1 G.2 H.2
      (fun y => by exact ih y) p.1 p.2 x

end Vector

end SK.Analytic

end
end

end OAI

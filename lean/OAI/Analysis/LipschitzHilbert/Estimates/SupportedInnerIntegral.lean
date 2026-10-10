import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-! Bounded tests supported on a measurable set turn local norm bounds
into literal global pairings. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem supported_inner_integral_le {X κ : Type*} [MeasurableSpace X] [Fintype κ]
    (mu : Measure X) (E : Set X) (hE : MeasurableSet E)
    (F g : X → EuclideanSpace ℂ κ) (hF : IntegrableOn F E mu)
    (hg : Measurable g) (hg1 : ∀ x, ‖g x‖≤1) (hgs : ∀ x, x∉E → g x=0) :
    Integrable (fun x => inner ℂ (F x) (g x)) mu ∧
      ‖∫ x, inner ℂ (F x) (g x) ∂mu‖≤∫ x in E, ‖F x‖ ∂mu := by
  have hp (x : X) : ‖inner ℂ (F x) (g x)‖≤‖F x‖ :=
    (norm_inner_le_norm (𝕜:=ℂ) _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hg1 x))
  have hlocal : IntegrableOn (fun x => inner ℂ (F x) (g x)) E mu :=
    hF.norm.mono' (hF.aestronglyMeasurable.inner hg.aestronglyMeasurable)
      (Filter.Eventually.of_forall hp)
  have he (x : X) : E.indicator (fun x => inner ℂ (F x) (g x)) x=inner ℂ (F x) (g x) := by
    by_cases hx : x∈E
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx,hgs x hx,inner_zero_right]
  have hglobal := ((integrable_indicator_iff hE).2 hlocal).congr (Filter.Eventually.of_forall he)
  refine ⟨hglobal,?_⟩
  have hI : (∫ x, inner ℂ (F x) (g x) ∂mu)=∫ x in E, inner ℂ (F x) (g x) ∂mu := by
    rw [←integral_indicator hE,funext he]
  rw [hI]
  exact (norm_integral_le_integral_norm _).trans (integral_mono hlocal.norm hF.norm hp)

end LipschitzHilbert

end

end OAI

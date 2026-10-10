import OAI.Probability.IsingPerceptron.RetainedDisplacement
import Mathlib.Probability.Kernel.Representation

namespace OAI

/-! A conditional product-law bridge for ancestor-dependent cascade marks. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace InvariantIsing

/-- Replacing a mark by a seed realization and replacing each descendant law
by the same conditional law preserves the full marked subtree distribution. -/
lemma ancestor_fiber_map_product {S A B C D : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (P : Measure S) (μ : Measure A) (Q : Measure B) (R : Measure C)
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    {f : S → A} (hf : Measurable f) (hlaw : P.map f = μ)
    {g : A × B → D} {h : A × C → D} (hg : Measurable g) (hh : Measurable h)
    (hsub : ∀ a, Q.map (fun b => g (a,b)) = R.map (fun c => h (a,c))) :
    (P.prod Q).map (fun p => (f p.1,g (f p.1,p.2))) =
      (μ.prod R).map (fun p => (p.1,h p)) := by
  have hleft : Measurable (fun p : S × B => (f p.1,g (f p.1,p.2))) :=
    (hf.comp measurable_fst).prodMk (hg.comp ((hf.comp measurable_fst).prodMk measurable_snd))
  have hright : Measurable (fun p : A × C => (p.1,h p)) := measurable_fst.prodMk hh
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF hleft, lintegral_map hF hright]
  rw [lintegral_prod (fun p : S × B => F (f p.1,g (f p.1,p.2))) (hF.comp hleft).aemeasurable,
    lintegral_prod (fun p : A × C => F (p.1,h p)) (hF.comp hright).aemeasurable]
  have hi a : MeasureTheory.lintegral Q (fun b => F (a,g (a,b))) =
      MeasureTheory.lintegral R (fun c => F (a,h (a,c))) := by
    have hFa : Measurable (fun d : D => F (a,d)) := hF.comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_map (g := fun b : B => g (a,b)) hFa
      (hg.comp (measurable_const.prodMk measurable_id)), hsub a,
      lintegral_map (g := fun c : C => h (a,c)) hFa
        (hh.comp (measurable_const.prodMk measurable_id))]
  simp_rw [hi]
  have hJ : Measurable (fun a => MeasureTheory.lintegral R (fun c => F (a,h (a,c)))) :=
    (hF.comp hright).lintegral_prod_right'
  rw [← lintegral_map hJ hf, hlaw]

end InvariantIsing

end

end OAI

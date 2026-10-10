import Mathlib
import OAI.Probability.Ballisticity.Estimates.ClassSelection

namespace OAI

section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def selectedClassProduct {d : ℕ} (e : Direction d) (n : ℕ) (r lam : ℝ)
    (w : CurrentWindow e) : ℝ≥0∞ :=
  if ∃ a, CurrentClassSelection e n r w.1 a then
    ∏ j : Fin n, upperNoDrop e (fun p => w.2 (currentSelect e n r w.1 j,p)) ^ (-lam)
  else 0

lemma selectedClassProduct_measurable {d : ℕ} (e : Direction d) (n : ℕ) (r lam : ℝ) :
    Measurable (selectedClassProduct e n r lam) := by
  unfold selectedClassProduct
  apply Measurable.ite ((current_selection_event_measurable e n r).preimage measurable_fst) _ measurable_const
  apply Finset.measurable_prod
  intro j _
  apply Measurable.pow_const
  apply (upperNoDrop_measurable e).comp
  apply Measurable.of_eval
  intro p
  have hm : Measurable (fun z : ReferenceClasses.AllFields (HorizontalSpace e) (Row d) × ℕ => z.1 (z.2,p)) :=
    measurable_from_prod_countable_left fun a => measurable_pi_apply (a,p)
  exact hm.comp (measurable_snd.prodMk (((currentSelect_measurable e n r).comp measurable_fst).eval))

lemma selectedClassProduct_lintegral {d : ℕ} (e : Direction d) (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (δ : Measure (CurrentData e)) [IsProbabilityMeasure δ]
    (n : ℕ) (r lam : ℝ) :
    (∫⁻ w, selectedClassProduct e n r lam w ∂δ.compProd (currentWindowReference e ν))≤
      (∫⁻ ξ, upperNoDrop e ξ ^ (-lam) ∂Measure.infinitePi (fun _ : ℕ×HorizontalSpace e => ν))^n := by
  rw [Measure.lintegral_compProd (selectedClassProduct_measurable e n r lam)]
  calc
    _ ≤ ∫⁻ _ : CurrentData e, (∫⁻ ξ, upperNoDrop e ξ ^ (-lam) ∂Measure.infinitePi
        (fun _ : ℕ×HorizontalSpace e => ν))^n ∂δ := by
      apply lintegral_mono
      intro A
      by_cases h : ∃ a, CurrentClassSelection e n r A a
      · simp only [selectedClassProduct,ite_eq_left h,currentWindowReference,Kernel.comap_apply]
        exact le_of_eq (ReferenceClasses.reference_distinct_product ν A.1 (currentSelect e n r A)
          (currentSelect_spec e n r A h).2 _ ((upperNoDrop_measurable e).pow_const (-lam)))
      · simp [selectedClassProduct,h]
    _ = _ := by simp

end DirectionalTransience

end

end OAI

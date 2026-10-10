import Mathlib
import OAI.Computability.VertexCover.Analysis.VarianceProduct

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Product
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsProbabilityMeasure μ]

theorem cons_measurePreserving (n : ℕ) :
    MeasurePreserving (fun p : X × (Fin n → X) => Fin.cons p.1 p.2)
      (μ.prod (Measure.pi (fun _ : Fin n => μ))) (Measure.pi (fun _ : Fin (n+1) => μ)) := by
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero', Fin.zero_succAbove] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) 0).symm

theorem integral_cons (n : ℕ) (f : (Fin (n+1) → X) → ℝ)
    (hi : Integrable f (Measure.pi (fun _ => μ))) :
    ∫ v, f v ∂Measure.pi (fun _ : Fin (n+1) => μ) =
      ∫ x, ∫ s, f (Fin.cons x s) ∂Measure.pi (fun _ : Fin n => μ) ∂μ := by
  have hp := cons_measurePreserving μ n
  calc
    _ = ∫ p : X × (Fin n → X), f (Fin.cons p.1 p.2) ∂μ.prod (Measure.pi (fun _ => μ)) := by
      rw [← hp.map_eq]
      exact integral_map hp.aemeasurable (by rw [hp.map_eq]; exact hi.aestronglyMeasurable)
    _ = _ := integral_prod _ (hp.integrable_comp_of_integrable hi)

noncomputable def coordinateVariance {n : ℕ} (f : (Fin n → X) → ℝ)
    (j : Fin n) (s : Fin n → X) : ℝ :=
  variance (fun x => f (Function.update s j x)) μ

theorem update_joint_measurable {n : ℕ} (j : Fin n) :
    Measurable (fun p : (Fin n → X) × X => Function.update p.1 j p.2) := by
  apply Measurable.of_eval
  intro k
  by_cases hk : k = j
  · subst k; simpa using measurable_snd
  · simpa only [Function.update_of_ne hk, Function.comp_def] using (measurable_pi_apply k).comp measurable_fst

theorem coordinateVariance_integrable {n : ℕ} (f : (Fin n → X) → ℝ)
    (hf : Measurable f) {C : ℝ} (hb : ∀ s, ‖f s‖ ≤ C) (j : Fin n) :
    Integrable (coordinateVariance μ f j) (Measure.pi (fun _ : Fin n => μ)) :=
  section_variance_integrable _ μ _ (hf.comp (update_joint_measurable j)) (fun _s _x => hb _)

theorem variance_pi_le (n : ℕ) (f : (Fin n → X) → ℝ) (hf : Measurable f)
    {C : ℝ} (hb : ∀ s, ‖f s‖ ≤ C) :
    variance f (Measure.pi (fun _ : Fin n => μ)) ≤
      ∑ j, ∫ s, coordinateVariance μ f j s ∂Measure.pi (fun _ : Fin n => μ) := by
  induction n with
  | zero =>
      have he : f = fun _ => f (fun i => Fin.elim0 i) := by
        funext s
        exact congrArg f (Subsingleton.elim _ _)
      rw [he, variance_eq_integral measurable_const.aemeasurable]
      simp
  | succ n ih =>
      let P := Measure.pi (fun _ : Fin n => μ)
      let F : X → (Fin n → X) → ℝ := fun x s => f (Fin.cons x s)
      have hF : Measurable (Function.uncurry F) := hf.comp (cons_measurePreserving μ n).measurable
      have hFb : ∀ x s, ‖F x s‖ ≤ C := fun x s => hb _
      have hsec : ∀ x, Measurable (F x) := fun x => hF.comp (measurable_const.prodMk measurable_id)
      have hpre : variance f (Measure.pi (fun _ : Fin (n+1) => μ)) ≤
          (∫ x, variance (F x) P ∂μ) + ∫ s, variance (fun x => F x s) μ ∂P := by
        rw [← (cons_measurePreserving μ n).variance_fun_comp hf.aemeasurable]
        exact variance_product_le μ P F hF hFb
      have hci := fun j : Fin (n+1) => coordinateVariance_integrable μ f hf hb j
      have hstep : ∀ x s (j : Fin n),
          coordinateVariance μ (F x) j s = coordinateVariance μ f j.succ (Fin.cons x s) := by
        intro x s j
        unfold coordinateVariance F
        simp only [Fin.cons_update]
      have hIi : ∀ j : Fin n, Integrable
          (fun x => ∫ s, coordinateVariance μ (F x) j s ∂P) μ := by
        intro j
        simp_rw [hstep]
        exact ((cons_measurePreserving μ n).integrable_comp_of_integrable (hci j.succ)).integral_prod_left
      have ht : (∫ x, variance (F x) P ∂μ) ≤
          ∑ j : Fin n, ∫ s, coordinateVariance μ f j.succ s ∂Measure.pi (fun _ => μ) := by
        calc
          _ ≤ ∫ x, ∑ j : Fin n, ∫ s, coordinateVariance μ (F x) j s ∂P ∂μ := by
            apply integral_mono (section_variance_integrable μ P F hF hFb)
              (integrable_finsetSum _ (fun j _ => hIi j))
            intro x
            exact ih (F x) (hsec x) (hFb x)
          _ = _ := by
            rw [integral_finsetSum _ (fun j _ => hIi j)]
            apply Finset.sum_congr rfl
            intro j hj
            simp_rw [hstep]
            exact (integral_cons μ n _ (hci j.succ)).symm
      have hz : (∫ s, variance (fun x => F x s) μ ∂P) =
          ∫ s, coordinateVariance μ f 0 s ∂Measure.pi (fun _ : Fin (n+1) => μ) := by
        rw [integral_cons μ n _ (hci 0)]
        simp only [coordinateVariance, Fin.update_cons_zero]
        simp only [F, integral_const, probReal_univ, one_smul]
        rfl
      calc
        _ ≤ (∫ x, variance (F x) P ∂μ) + ∫ s, variance (fun x => F x s) μ ∂P := hpre
        _ ≤ (∑ j : Fin n, ∫ s, coordinateVariance μ f j.succ s ∂Measure.pi (fun _ => μ)) +
            ∫ s, coordinateVariance μ f 0 s ∂Measure.pi (fun _ => μ) := by
          rw [← hz]
          exact add_le_add ht le_rfl
        _ = _ := by rw [Fin.sum_univ_succ]; exact add_comm _ _

end VertexCover.Product


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI

import OAI.Analysis.AncientFlat.Evolution.MeasurableTime

namespace OAI
noncomputable section
namespace MeasurableSchauder
open VariableSchauder
open scoped ContDiff BoundedContinuousFunction SchwartzMap
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
theorem integratedJet_fourth_holder (K : SchwartzMap V ℂ)
    (α β γ L : ℝ) (hα : 0<α) (hγ : 0<γ) (hγ1 : γ<1) (hL : 0≤L) :
    ∃ C : ℝ, 0≤C ∧ ∀ (A : ℝ → V → ℝ), Continuous (Function.uncurry A) →
      (∀ t y, A t y ∈ Set.Icc α β) →
      (∀ t x y, ‖A t x-A t y‖≤L*‖x-y‖) →
      ∀ (f : ℝ → (V →ᵇ ℂ)) (M H T : ℝ), 0≤M → 0≤H → 0≤T → T≤1 → MeasureTheory.StronglyMeasurable f →
      (∀ t∈Set.Icc 0 T, ‖f t‖≤M) →
      (∀ t∈Set.Icc 0 T, ∀ x y, ‖f t x-f t y‖≤H*‖x-y‖^γ) →
      (∀ t∈Set.Icc 0 T, ∀ x, ‖integratedJet K A f t 4 x‖≤C*(H+M)) ∧
      (∀ t∈Set.Icc 0 T, ∀ s∈Set.Icc 0 T, ∀ x y,
        ‖integratedJet K A f t 4 x-integratedJet K A f s 4 y‖≤
          C*(H+M)*(‖x-y‖^γ+|t-s|^(γ/4))) := by
  by_cases hab : α≤β
  · obtain ⟨B,hB,hb⟩ := VariableSchauder.exists_fourth_bound α β L hα hL K γ hγ hγ1.le
    obtain ⟨D,hD,hd⟩ := MeasurableSchauder.exists_fourth_spatial_holder α β L hα hL K γ hγ hγ1
    obtain ⟨E,hE,he⟩ := MeasurableSchauder.exists_fourth_time_holder α β L hα hab hL K γ hγ hγ1
    refine ⟨B+D+E,by positivity,?_⟩
    intro A hA hAr hAL f M H T hM hH hT hT1 hf hm hh
    have hhs (t : ℝ) (ht : t∈Set.Icc 0 T) : ∀ r∈Set.Ioo 0 t, ∀ x y,
        ‖f r x-f r y‖≤H*‖x-y‖^γ := fun r hr => hh r ⟨hr.1.le,hr.2.le.trans ht.2⟩
    have hms (t : ℝ) (ht : t∈Set.Icc 0 T) : ∀ r∈Set.Ioo 0 t, ‖f r‖≤M :=
      fun r hr => hm r ⟨hr.1.le,hr.2.le.trans ht.2⟩
    constructor
    · intro t ht x
      have h := hb A hA hAr hAL f H M t hH hM ht.1 (ht.2.trans hT1) (hms t ht) (hhs t ht) x
      refine h.trans ?_
      calc
        _ ≤ B*(H+M)*1 := mul_le_mul_of_nonneg_left
          (Real.rpow_le_one ht.1 (ht.2.trans hT1) (by positivity)) (by positivity)
        _ ≤ _ := by nlinarith [mul_nonneg hD (add_nonneg hH hM),mul_nonneg hE (add_nonneg hH hM)]
    · intro t ht s hs x y
      have hspace := hd A hA hAr hAL f hf H M t hH hM ht.1 (ht.2.trans hT1)
        (hms t ht) (hhs t ht) x y
      have htime := he A hA hAr hAL f hf H M T hH hM hT1 hm hh s hs t ht y
      calc
        _ ≤ ‖VariableSchauder.integratedJet K A f t 4 x-VariableSchauder.integratedJet K A f t 4 y‖+
            ‖VariableSchauder.integratedJet K A f t 4 y-VariableSchauder.integratedJet K A f s 4 y‖ := norm_sub_le_norm_sub_add_norm_sub ..
        _ ≤ D*(H+M)*‖x-y‖^γ+E*(H+M)*|t-s|^(γ/4) := add_le_add hspace htime
        _ ≤ _ := by
          have h1 : D≤B+D+E := by linarith
          have h2 : E≤B+D+E := by linarith
          calc
            _ ≤ (B+D+E)*(H+M)*‖x-y‖^γ+(B+D+E)*(H+M)*|t-s|^(γ/4) := by gcongr
            _ = _ := by ring
  · refine ⟨0,le_rfl,fun A _ hAr => ?_⟩
    exact (hab ((hAr 0 0).1.trans (hAr 0 0).2)).elim
end MeasurableSchauder

end

end OAI

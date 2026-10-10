import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.PairDistanceContinuous

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
namespace CurrentFalconer.AssemblyLimit
open MeasureTheory Set Filter
open scoped ENNReal Topology

theorem original_distance_monotone_limit
    (d : ℕ) (hd : 2 ≤ d) (E E₁ E₂ : Set (Ambient d))
    (hE : IsCompact E) (_hE₁ : IsCompact E₁) (_hE₂ : IsCompact E₂)
    (h₁E : E₁ ⊆ E) (h₂E : E₂ ⊆ E)
    (μ ν : Measure (Ambient d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ E₁ᶜ=0) (hν : ν E₂ᶜ=0)
    (δ D : ℝ) (hδ : 0 < δ) (_hD : 0 < D)
    (hsep : ∀ x ∈ E₁, ∀ y ∈ E₂, δ ≤ dist x y ∧ dist x y ≤ D)
    (Γ : ℕ → Set (Ambient d × Ambient d))
    (hm : ∀ N, MeasurableSet (Γ N)) (hs : ∀ N, Γ N ⊆ E₁ ×ˢ E₂)
    (hmono : Antitone Γ) (hpos : 0 < (μ.prod ν) (⋂ N, Γ N)) :
    (∀ N, IsFiniteMeasure (filteredDistanceMeasure μ ν (Γ N))) ∧
    Antitone (fun N => filteredDistanceMeasure μ ν (Γ N)) ∧
    (∀ s, MeasurableSet s → Tendsto (fun N => filteredDistanceMeasure μ ν (Γ N) s)
      atTop (𝓝 (filteredDistanceMeasure μ ν (⋂ N, Γ N) s))) ∧
    IsFiniteMeasure (filteredDistanceMeasure μ ν (⋂ N, Γ N)) ∧
    0 < filteredDistanceMeasure μ ν (⋂ N, Γ N) univ ∧
    (∀ N, filteredDistanceMeasure μ ν (Γ N) (distanceSet E)ᶜ=0) ∧
    filteredDistanceMeasure μ ν (⋂ N, Γ N) (distanceSet E)ᶜ=0 ∧
    IsCompact (distanceSet E)
 := by
  have hsep' : ∀ x∈E₁, ∀ y∈E₂, δ≤dist x y := fun x hx y hy => (hsep x hx y hy).1
  have : IsFiniteMeasure (weightedOriginalPair μ ν) :=
    weightedOriginalPair_finite hd μ ν E₁ E₂ hμ hν δ hδ hsep'
  have hinf : MeasurableSet (⋂ N, Γ N) := MeasurableSet.iInter hm
  have hfin {A : Set (Ambient d × Ambient d)} (hA : MeasurableSet A) :
      IsFiniteMeasure (filteredDistanceMeasure μ ν A) := by
    rw [filteredDistanceMeasure_eq μ ν hA]
    infer_instance
  refine ⟨fun N => hfin (hm N),?_,?_,hfin hinf,?_,?_,?_,distanceSet_compact hE⟩
  · intro N M hNM
    dsimp only
    rw [filteredDistanceMeasure_eq μ ν (hm N),filteredDistanceMeasure_eq μ ν (hm M)]
    exact Measure.map_mono (Measure.restrict_mono_set _ (hmono hNM)) pairDistance_continuous.measurable
  · intro s hs'
    simp_rw [filteredDistanceMeasure_eq μ ν (hm _),filteredDistanceMeasure_eq μ ν hinf,
      Measure.map_apply pairDistance_continuous.measurable hs',
      Measure.restrict_apply (pairDistance_continuous.measurable hs')]
    have ht := tendsto_measure_iInter_atTop (μ:=weightedOriginalPair μ ν)
      (fun N => ((pairDistance_continuous.measurable hs').inter (hm N)).nullMeasurableSet)
      (fun N M hNM => inter_subset_inter_right _ (hmono hNM)) ⟨0,measure_ne_top _ _⟩
    simpa only [Function.comp_def,←inter_iInter] using ht
  · rw [filteredDistanceMeasure_eq μ ν hinf,Measure.map_apply pairDistance_continuous.measurable
      MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ]
    apply pos_iff_ne_zero.mpr
    intro hz
    exact hpos.ne' (originalPair_ac_weighted μ ν E₁ E₂ hμ hν δ hδ hsep' hz)
  · intro N
    exact filteredDistanceMeasure_carried μ ν hE h₁E h₂E (hm N) (hs N)
  · exact filteredDistanceMeasure_carried μ ν hE h₁E h₂E hinf
      ((iInter_subset Γ 0).trans (hs 0))

end CurrentFalconer.AssemblyLimit
end
end

end OAI

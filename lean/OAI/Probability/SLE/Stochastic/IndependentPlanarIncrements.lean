import OAI.Probability.SLE.BrownianGenerators
import OAI.Probability.SLE.Geometry.PublishedWienerSupport

namespace OAI

/-! Independence of the two-coordinate Wiener increment from its full
original past. Product coordinates retain both original pasts. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

private lemma measurePreserving_shuffle
    {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (τ : Measure D)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure τ] :
    MeasurePreserving (fun p : (A×B)×(C×D) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μ.prod ν).prod (ρ.prod τ)) ((μ.prod ρ).prod (ν.prod τ)) := by
  have h1 := measurePreserving_prodAssoc μ ν (ρ.prod τ)
  have h2 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ν ρ τ).symm
  have h3 := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := ρ)).prod (MeasurePreserving.id τ))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ρ ν τ)
  have h5 := (measurePreserving_prodAssoc μ ρ (ν.prod τ)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

lemma independent_product_pairs
    {Ω Ω' A B C D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Ω → A} {Y : Ω → B} {X' : Ω' → C} {Y' : Ω' → D}
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (hXY : IndepFun X Y μ) (hXY' : IndepFun X' Y' ν) :
    IndepFun (fun p : Ω×Ω' => (X p.1,X' p.2))
      (fun p : Ω×Ω' => (Y p.1,Y' p.2)) (μ.prod ν) := by
  have hx : HasLaw X (μ.map X) μ := ⟨hX.aemeasurable,rfl⟩
  have hy : HasLaw Y (μ.map Y) μ := ⟨hY.aemeasurable,rfl⟩
  have hx' : HasLaw X' (ν.map X') ν := ⟨hX'.aemeasurable,rfl⟩
  have hy' : HasLaw Y' (ν.map Y') ν := ⟨hY'.aemeasurable,rfl⟩
  have h1 : MeasurePreserving (fun ω => (X ω,Y ω)) μ ((μ.map X).prod (μ.map Y)) :=
    ⟨hX.prodMk hY,(hXY.hasLaw_prod hx hy).map_eq⟩
  have h2 : MeasurePreserving (fun ω => (X' ω,Y' ω)) ν ((ν.map X').prod (ν.map Y')) :=
    ⟨hX'.prodMk hY',(hXY'.hasLaw_prod hx' hy').map_eq⟩
  have h3 := (measurePreserving_shuffle (μ.map X) (μ.map Y) (ν.map X') (ν.map Y')).comp
    (h1.prod h2)
  have hpair : HasLaw (fun p : Ω×Ω' => ((X p.1,X' p.2),(Y p.1,Y' p.2)))
      (((μ.map X).prod (ν.map X')).prod ((μ.map Y).prod (ν.map Y'))) (μ.prod ν) :=
    ⟨h3.measurable.aemeasurable,h3.map_eq⟩
  have ha : HasLaw (fun p : Ω×Ω' => (X p.1,X' p.2))
      ((μ.map X).prod (ν.map X')) (μ.prod ν) := by
    exact (measurePreserving_fst (μ := (μ.map X).prod (ν.map X'))
      (ν := (μ.map Y).prod (ν.map Y'))).hasLaw.comp hpair
  have hb : HasLaw (fun p : Ω×Ω' => (Y p.1,Y' p.2))
      ((μ.map Y).prod (ν.map Y')) (μ.prod ν) := by
    exact (measurePreserving_snd (μ := (μ.map X).prod (ν.map X'))
      (ν := (μ.map Y).prod (ν.map Y'))).hasLaw.comp hpair
  exact (indepFun_iff_hasLaw_prodMk_prod ha hb).mpr hpair

end SLEExactGauge

end

end OAI

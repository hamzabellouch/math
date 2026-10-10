import OAI.Probability.FreeIsing.Conditioning.Pullback
import OAI.Probability.FreeIsing.Estimates.LatentProductIndependence

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace Problem367

theorem condIndepFun_of_product_jointLaw
    {Ω S A B C D : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace S]
    [StandardBorelSpace A] [StandardBorelSpace B]
    (P : Measure Ω) [IsFiniteMeasure P]
    (ρ : Measure S) (μ : Measure A) (ν : Measure B)
    [IsFiniteMeasure ρ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {Z : Ω → S} {X : Ω → A} {Y : Ω → B}
    (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (hjoint : Measure.map (fun ω => (Z ω, X ω, Y ω)) P = ρ.prod (μ.prod ν))
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap Z) hZ.comap_le
      (fun ω => F (Z ω, X ω)) (fun ω => G (Z ω, Y ω)) P := by
  have he : MeasurePreserving (fun ω => (Z ω, X ω, Y ω)) P (ρ.prod (μ.prod ν)) :=
    ⟨hZ.prodMk (hX.prodMk hY), hjoint⟩
  have hbase := condIndepFun_latent_product ρ μ ν F G hF hG
  have hpull := condIndepFun_comp_measurePreserving P (ρ.prod (μ.prod ν))
    (fun ω => (Z ω, X ω, Y ω)) he (mS.comap Prod.fst) measurable_fst.comap_le
    (show Measurable (fun z : S × (A × B) => F (z.1, z.2.1)) by fun_prop)
    (show Measurable (fun z : S × (A × B) => G (z.1, z.2.2)) by fun_prop) hbase
  simpa only [MeasurableSpace.comap_comp, Function.comp_def] using hpull

theorem condIndepFun_of_independent_latent_noises
    {Ω S A B C D : Type*} [MeasurableSpace Ω] [mS : MeasurableSpace S]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    [StandardBorelSpace Ω] [StandardBorelSpace S]
    [StandardBorelSpace A] [StandardBorelSpace B]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → S} {X : Ω → A} {Y : Ω → B}
    (hZ : Measurable Z) (hX : Measurable X) (hY : Measurable Y)
    (hZXY : IndepFun Z (fun ω => (X ω, Y ω)) P) (hXY : IndepFun X Y P)
    (F : S × A → C) (G : S × B → D) (hF : Measurable F) (hG : Measurable G) :
    CondIndepFun (mS.comap Z) hZ.comap_le
      (fun ω => F (Z ω, X ω)) (fun ω => G (Z ω, Y ω)) P := by
  apply condIndepFun_of_product_jointLaw P (Measure.map Z P)
    (Measure.map X P) (Measure.map Y P) hZ hX hY _ F G hF hG
  rw [hZXY.map_prod_eq_prod_map_map hZ.aemeasurable (hX.prodMk hY).aemeasurable,
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]

end Problem367

end

end OAI

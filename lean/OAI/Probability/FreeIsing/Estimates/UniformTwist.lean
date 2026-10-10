import Mathlib

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory

namespace Problem367

theorem measurePreserving_fiberTwist
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (twist : B → A → A)
    (hmeas : Measurable (fun p : A × B => twist p.2 p.1))
    (hpres : ∀ b, MeasurePreserving (twist b) μ μ) :
    MeasurePreserving (fun p : A × B => (twist p.2 p.1, p.2))
      (μ.prod ν) (μ.prod ν) := by
  have hm : Measurable (fun p : A × B => (twist p.2 p.1, p.2)) :=
    hmeas.prodMk measurable_snd
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, Measure.prod_apply_symm (hs.preimage hm),
    Measure.prod_apply_symm hs]
  apply lintegral_congr
  intro b
  change μ ((twist b) ⁻¹' ((fun a => (a, b)) ⁻¹' s)) =
    μ ((fun a => (a, b)) ⁻¹' s)
  exact (hpres b).measure_preimage ((hs.preimage measurable_prodMk_right).nullMeasurableSet)

theorem map_pair_fiberTwist_of_indepFun
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure Ω) [IsFiniteMeasure P]
    {X : Ω → A} {Y : Ω → B}
    (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P)
    (twist : B → A → A)
    (hmeas : Measurable (fun p : A × B => twist p.2 p.1))
    (hpres : ∀ b, MeasurePreserving (twist b) (P.map X) (P.map X)) :
    P.map (fun ω => (twist (Y ω) (X ω), Y ω)) =
      (P.map X).prod (P.map Y) := by
  have hm : Measurable (fun p : A × B => (twist p.2 p.1, p.2)) :=
    hmeas.prodMk measurable_snd
  rw [← Function.comp_def (f := fun p : A × B => (twist p.2 p.1, p.2))
    (g := fun ω => (X ω, Y ω))]
  rw [← Measure.map_map hm (hX.prodMk hY),
    hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
  exact (measurePreserving_fiberTwist (P.map X) (P.map Y) twist hmeas hpres).map_eq

end Problem367

end

end OAI

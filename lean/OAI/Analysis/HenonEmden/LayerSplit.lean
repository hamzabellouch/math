import OAI.Analysis.HenonEmden.MeasureShuffle

namespace OAI

universe uZ uA uB uC uA2 uB2 uC2 uA3 uB3 uC3

section LayerSplit

open MeasureTheory Set
open scoped ENNReal
namespace HenonLaneEmden.LayerTonelli

variable {Z : Type uZ} [MeasurableSpace Z]

def tripleSwap {A : Type uA} {B : Type uB} {C : Type uC} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] :
    (A × B) × C ≃ᵐ (A × C) × B :=
  MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl A) MeasurableEquiv.prodComm).trans
      MeasurableEquiv.prodAssoc.symm)

@[simp] lemma tripleSwap_apply {A : Type uA2} {B : Type uB2} {C : Type uC2} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (x : (A × B) × C) :
    tripleSwap x = ((x.1.1,x.2),x.1.2) := rfl

lemma measurePreserving_tripleSwap {A : Type uA3} {B : Type uB3} {C : Type uC3} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [SFinite ν] [SFinite ρ] [SFinite μ] :
    MeasurePreserving (tripleSwap : (A × B) × C ≃ᵐ (A × C) × B)
      ((μ.prod ν).prod ρ) ((μ.prod ρ).prod ν) := by
  exact ((MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ρ ν)).comp
    ((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := ρ)))).comp
    (measurePreserving_prodAssoc μ ν ρ)

def parameterLayer (f : Z × ℝ → ℝ) : Set ((Z × ℝ) × ℝ) :=
  {z | 0 < z.1.2 ∧ z.1.2 < f (z.1.1,z.2)}

lemma measurableSet_parameterLayer {f : Z × ℝ → ℝ} (hf : Measurable f) :
    MeasurableSet (parameterLayer f) :=
  (measurableSet_lt measurable_const measurable_fst.snd).inter
    (measurableSet_lt measurable_fst.snd (hf.comp (measurable_fst.fst.prodMk measurable_snd)))

noncomputable def parameterLayerMeasure (μ : Measure Z) (f : Z × ℝ → ℝ) :
    Measure ((Z × ℝ) × ℝ) :=
  ((μ.prod volume).prod volume).restrict (parameterLayer f)

instance parameterLayerMeasure_sfinite (μ : Measure Z) [SFinite μ] (f : Z × ℝ → ℝ) :
    SFinite (parameterLayerMeasure μ f) := inferInstanceAs (SFinite (Measure.restrict _ _))

lemma measurePreserving_layer_tripleSwap (μ : Measure Z) [SFinite μ]
    {f : Z × ℝ → ℝ} (hf : Measurable f) :
    MeasurePreserving (tripleSwap : (Z × ℝ) × ℝ ≃ᵐ (Z × ℝ) × ℝ)
      (layerMeasure (μ.prod volume) f) (parameterLayerMeasure μ f) := by
  exact (measurePreserving_tripleSwap μ volume volume).restrict_preimage
    (measurableSet_parameterLayer hf)

/-- After permuting the real position and level coordinates, every pair layer
integral is the iterated nonnegative integral over two transverse/level parameters
and then the two real line layers. This is valid before proving finiteness. -/
lemma lintegral_pair_layer_split (μ : Measure Z) [SFinite μ]
    {f g : Z × ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    {F : ((Z × ℝ) × ℝ) × ((Z × ℝ) × ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂(layerMeasure (μ.prod volume) f).prod (layerMeasure (μ.prod volume) g)) =
      ∫⁻ p : (Z × ℝ) × (Z × ℝ),
        ∫⁻ s : ℝ × ℝ in {s | (p.1,s) ∈ parameterLayer f} ×ˢ {s | (p.2,s) ∈ parameterLayer g},
          F (((p.1.1,s.1),p.1.2),((p.2.1,s.2),p.2.2))
        ∂volume.prod volume ∂(μ.prod volume).prod (μ.prod volume) := by
  let V := parameterLayer f ×ˢ parameterLayer g
  let G : ((Z × ℝ) × ℝ) × ((Z × ℝ) × ℝ) → ℝ≥0∞ :=
    fun z => F (((z.1.1.1,z.1.2),z.1.1.2),((z.2.1.1,z.2.2),z.2.1.2))
  have hG : Measurable G := by fun_prop
  have hV : MeasurableSet V := (measurableSet_parameterLayer hf).prod (measurableSet_parameterLayer hg)
  calc
    _ = ∫⁻ z, G z ∂(parameterLayerMeasure μ f).prod (parameterLayerMeasure μ g) := by
      exact ((measurePreserving_layer_tripleSwap μ hf).prod
        (measurePreserving_layer_tripleSwap μ hg)).lintegral_comp hG
    _ = ∫⁻ z, V.indicator G z ∂((μ.prod volume).prod volume).prod ((μ.prod volume).prod volume) := by
      rw [parameterLayerMeasure,parameterLayerMeasure,Measure.prod_restrict]
      exact (lintegral_indicator hV G).symm
    _ = ∫⁻ z : ((Z × ℝ) × (Z × ℝ)) × (ℝ × ℝ),
        V.indicator G ((z.1.1,z.2.1),(z.1.2,z.2.2))
        ∂((μ.prod volume).prod (μ.prod volume)).prod (volume.prod volume) :=
      lintegral_prod_prod_shuffle _ _ _ _ (hG.indicator hV)
    _ = _ := by
      rw [lintegral_prod _ (by fun_prop)]
      apply lintegral_congr
      intro p
      have hset : MeasurableSet ({s | (p.1,s) ∈ parameterLayer f} ×ˢ {s | (p.2,s) ∈ parameterLayer g}) :=
        ((measurableSet_parameterLayer hf).preimage measurable_prodMk_left).prod
          ((measurableSet_parameterLayer hg).preimage measurable_prodMk_left)
      rw [← lintegral_indicator hset]
      apply lintegral_congr; intro s
      rfl

end HenonLaneEmden.LayerTonelli
end LayerSplit

end OAI

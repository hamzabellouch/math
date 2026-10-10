import Mathlib
import OAI.Probability.LatticeSurface.Convexity.HeatBathGeometry
import OAI.Probability.LatticeSurface.Convexity.TransportResampling
import OAI.Probability.LatticeSurface.Convexity.SupportUnit

namespace OAI

namespace BoundedData

open Set MeasureTheory ExtremalEdges

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

lemma update_preserves_volume (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (x : Free pins) :
    Measure.map (fun z : (Free pins → ℝ)×ℝ => update G pins hn b x z.1 z.2)
      ((volume.restrict (conditionalBody G pins b)).prod (volume.restrict (Icc (0:ℝ) 1)))=
    volume.restrict (conditionalBody G pins b) := by
  obtain ⟨R,l,u,hR,hl,hu,hbody,hends⟩ := split_body_region G pins hn b x
  let e := splitCoordinate pins x x.property
  apply IntervalResampling.transport volume volume e (preserving_splitCoordinate pins x x.property)
    (conditionalBody G pins b) hR hl hu hbody _ (continuous_update G pins hn b x).measurable
  intro z
  have hz : e.symm ((e z.1).1,(e z.1).2)=z.1 := e.symm_apply_apply z.1
  have he := hends (e z.1).1 (e z.1).2
  change lower G pins hn b (e.symm ((e z.1).1,(e z.1).2)) x=l (e z.1).1 ∧
    upper G pins hn b (e.symm ((e z.1).1,(e z.1).2)) x=u (e z.1).1 at he
  rw [hz] at he
  apply e.symm.injective
  rw [e.symm_apply_apply,split_inv_update pins x (e z.1).1 (e z.1).2 _,hz]
  unfold update
  rw [he.1,he.2]
  congr 1
  ring

noncomputable def law (G : SimpleGraph V) (pins : Set V) (b : V → ℝ) : Measure (Free pins → ℝ) :=
  (volume (conditionalBody G pins b))⁻¹ • volume.restrict (conditionalBody G pins b)

lemma law_probability (G : SimpleGraph V) (hc : G.Connected) (pins : Set V) (hp : pins.Nonempty)
    (b : V → ℝ) (hpos : 0<volume (conditionalBody G pins b)) : IsProbabilityMeasure (law G pins b) := by
  constructor
  simp only [law,Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ,univ_inter,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' (compact_body G hc pins hp b).measure_ne_top

lemma update_preserves_law (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (x : Free pins) :
    Measure.map (fun z : (Free pins → ℝ)×ℝ => update G pins hn b x z.1 z.2)
      ((law G pins b).prod (volume.restrict (Icc (0:ℝ) 1)))=law G pins b := by
  rw [law,Measure.prod_smul_left,
    Measure.map_smul _ (continuous_update G pins hn b x).measurable.aemeasurable,update_preserves_volume]

noncomputable def bodyMeasure (G : SimpleGraph V) (hc : G.Connected) (pins : Set V) (hp : pins.Nonempty)
    (b : V → ℝ) (hpos : 0<volume (conditionalBody G pins b)) : ProbabilityMeasure (conditionalBody G pins b) :=
  ⟨(volume (conditionalBody G pins b))⁻¹ • Measure.comap Subtype.val volume,by
    constructor
    rw [Measure.smul_apply,(MeasurableEmbedding.subtype_coe (closed_conditionalBody G pins b).measurableSet).comap_apply,
      image_univ,Subtype.range_coe]
    exact ENNReal.inv_mul_cancel hpos.ne' (compact_body G hc pins hp b).measure_ne_top⟩

lemma bodyMeasure_map (G : SimpleGraph V) (hc : G.Connected) (pins : Set V) (hp : pins.Nonempty)
    (b : V → ℝ) (hpos : 0<volume (conditionalBody G pins b)) :
    Measure.map Subtype.val (bodyMeasure G hc pins hp b hpos : Measure (conditionalBody G pins b))=law G pins b := by
  change Measure.map Subtype.val (_ • Measure.comap Subtype.val volume)=_
  rw [Measure.map_smul _ measurable_subtype_coe.aemeasurable,
    map_comap_subtype_coe (closed_conditionalBody G pins b).measurableSet]
  rfl

noncomputable def bodyUpdate (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (x : Free pins) (z : (conditionalBody G pins b)×Icc (0:ℝ) 1) : conditionalBody G pins b :=
  ⟨update G pins hn b x z.1.val z.2.val,update_mem G pins hn b x z.1.val z.1.property z.2.property⟩

lemma continuous_bodyUpdate (G : SimpleGraph V) (pins : Set V) (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (x : Free pins) : Continuous (bodyUpdate G pins hn b x) := by
  exact ((continuous_update G pins hn b x).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

lemma bodyUpdate_preserves (G : SimpleGraph V) (hc : G.Connected) (pins : Set V) (hp : pins.Nonempty)
    (hn : ∀ x : Free pins,(G.neighborFinset x).Nonempty)
    (b : V → ℝ) (hpos : 0<volume (conditionalBody G pins b)) (x : Free pins) :
    Measure.map (bodyUpdate G pins hn b x)
      ((bodyMeasure G hc pins hp b hpos : Measure (conditionalBody G pins b)).prod UnitControl.law)=
    (bodyMeasure G hc pins hp b hpos : Measure (conditionalBody G pins b)) := by
  apply (MeasurableEmbedding.subtype_coe (closed_conditionalBody G pins b).measurableSet).map_injective
  rw [Measure.map_map measurable_subtype_coe (continuous_bodyUpdate G pins hn b x).measurable,bodyMeasure_map]
  change Measure.map ((fun z : (Free pins → ℝ)×ℝ => update G pins hn b x z.1 z.2) ∘ Prod.map Subtype.val Subtype.val) _=_
  rw [← Measure.map_map (continuous_update G pins hn b x).measurable (measurable_subtype_coe.prodMap measurable_subtype_coe),
    ← Measure.map_prod_map _ _ measurable_subtype_coe measurable_subtype_coe,bodyMeasure_map,UnitControl.map_val]
  exact update_preserves_law G pins hn b x

end BoundedData

end OAI

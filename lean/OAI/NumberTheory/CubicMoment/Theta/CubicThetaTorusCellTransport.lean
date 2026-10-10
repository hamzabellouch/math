import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHorizontalCoefficient

namespace OAI

/-! Exact measurable transport between the arithmetic period cell and
the torus. This also applies to measurable L2 representatives. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
local instance cubicThetaTorusCellTransportMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

def cubicThetaTorusCellPoint (u : UnitAddTorus (Fin 2)) : ℂ :=
  cubicThetaPeriodCell ((UnitAddTorus.measurableEquivPiIoc (0 : Fin 2 → ℝ)) u).val

lemma cubicThetaTorusCellPoint_embedding : MeasurableEmbedding cubicThetaTorusCellPoint := by
  have hS : MeasurableSet {x : Fin 2 → ℝ | ∀ i,
      x i∈Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i+1)} :=
    MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  exact cubicThetaPeriodEquiv.toHomeomorph.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe hS).comp
      (UnitAddTorus.measurableEquivPiIoc (0 : Fin 2 → ℝ)).measurableEmbedding)

theorem cubicThetaTorusCellPoint_map :
    Measure.map cubicThetaTorusCellPoint volume=
      ENNReal.ofReal (2/(9*Real.sqrt 3)) •
        (volume : Measure ℂ).restrict cubicThetaHorizontalCell := by
  let e := UnitAddTorus.measurableEquivPiIoc (0 : Fin 2 → ℝ)
  let r := fun u : UnitAddTorus (Fin 2) => (e u).val
  have hr : Measurable r := measurable_subtype_coe.comp e.measurable
  have hS : MeasurableSet {x : Fin 2 → ℝ | ∀ i,
      x i∈Ioc ((0 : Fin 2 → ℝ) i) ((0 : Fin 2 → ℝ) i+1)} :=
    MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  have hm : Measure.map r volume=
      (volume : Measure (Fin 2 → ℝ)).restrict {x | ∀ i,x i∈Ioc (0:ℝ) 1} := by
    change Measure.map (Subtype.val ∘ e) volume=_
    rw [←Measure.map_map measurable_subtype_coe e.measurable,
      (UnitAddTorus.measurePreserving_equivPiIoc (0 : Fin 2 → ℝ)).map_eq]
    convert! map_comap_subtype_coe hS (volume : Measure (Fin 2 → ℝ)) using 1
    congr 1
    ext x
    simp
  change Measure.map (cubicThetaPeriodEquiv ∘ r) volume=_
  rw [←Measure.map_map cubicThetaPeriodEquiv.continuous.measurable hr,hm,
    ←cubicThetaCube_halfOpen_measure,←cubicThetaPeriodEquiv_preimage_cell,
    ←Measure.restrict_map cubicThetaPeriodEquiv.continuous.measurable
      cubicThetaHorizontalCell_measurable,cubicThetaPeriodEquiv_map_volume,
    Measure.restrict_smul]

lemma cubicThetaTorusCellPoint_character (h : Eisenstein) (u : UnitAddTorus (Fin 2)) :
    cubicThetaTorusFourier h u=
      (Real.fourierChar (tracePair (cubicThetaTorusCellPoint u) (cubicThetaRowFrequency h)):ℂ) := by
  let e := UnitAddTorus.measurableEquivPiIoc (0 : Fin 2 → ℝ)
  have hu : (fun i => ((e u).val i:UnitAddCircle))=u := e.symm_apply_apply u
  calc
    _ = cubicThetaTorusFourier h (fun i => ((e u).val i:UnitAddCircle)) :=
      congrArg (cubicThetaTorusFourier h) hu.symm
    _ = _ := cubicThetaTorusFourier_actual h (e u).val

lemma cubicThetaTorusCellPoint_memLp {f : ℂ → ℂ}
    (hf : MemLp f 2 ((volume : Measure ℂ).restrict cubicThetaHorizontalCell)) :
    MemLp (f ∘ cubicThetaTorusCellPoint) 2 volume := by
  have hs := hf.smul_measure (c:=ENNReal.ofReal (2/(9*Real.sqrt 3))) ENNReal.ofReal_ne_top
  rw [←cubicThetaTorusCellPoint_map] at hs
  exact hs.comp_of_map cubicThetaTorusCellPoint_embedding.measurable.aemeasurable

lemma cubicThetaTorusCellPoint_integral (f : ℂ → ℂ) :
    (∫ u : UnitAddTorus (Fin 2),f (cubicThetaTorusCellPoint u))=
      (2/(9*Real.sqrt 3):ℝ) • ∫ z in cubicThetaHorizontalCell,f z := by
  rw [←cubicThetaTorusCellPoint_embedding.integral_map,cubicThetaTorusCellPoint_map,
    integral_smul_measure,ENNReal.toReal_ofReal (by positivity : (0:ℝ)≤2/(9*Real.sqrt 3))]

end CubicFirstMoment

end

end OAI

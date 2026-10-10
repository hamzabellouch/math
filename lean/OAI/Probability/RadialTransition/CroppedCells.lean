import OAI.Probability.RadialTransition.MultisetEnergy

namespace OAI

noncomputable section


open MeasureTheory Set Filter Function

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma measurable_cellOf : Measurable cellOf := by
  apply Measurable.of_eval
  intro k
  exact Int.measurable_floor.comp (measurable_const.mul (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).measurable)

def gridRegion (k : Cell) : Set Position := {x | cellOf x = k}

lemma measurableSet_gridRegion (k : Cell) : MeasurableSet (gridRegion k) :=
  measurable_cellOf (measurableSet_singleton k)

abbrev CroppedCell (A : Set Position) (k : Cell) := {x : Position // x ∈ A ∩ gridRegion k}

def croppedCellMeasure (A : Set Position) (k : Cell) : Measure (CroppedCell A k) :=
  volume.comap Subtype.val

def gridOrigin (k : Cell) : Position := WithLp.toLp 2 (fun i => (k i : ℝ)/4)

lemma gridRegion_subset_box (k : Cell) : gridRegion k ⊆ translateSet (gridOrigin k) (cube (1/4)) := by
  intro x hx i
  have hh : ⌊4*x i⌋ = k i := congrFun hx i
  have hl := Int.floor_le (4*x i)
  have hu := Int.lt_floor_add_one (4*x i)
  rw [hh] at hl hu
  change 0 ≤ x i - (k i : ℝ)/4 ∧ x i - (k i : ℝ)/4 ≤ 1/4
  constructor <;> linarith

lemma volume_gridRegion_le (k : Cell) : volume (gridRegion k) ≤ ENNReal.ofReal (1/64:ℝ) := by
  have hh := measure_mono (gridRegion_subset_box k) (μ := volume)
  rw [volume_translateSet _ _ (measurableSet_cube _), volume_cube] at hh
  rw [← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/4)] at hh
  norm_num at hh ⊢
  exact hh

lemma croppedCellMeasure_univ {A : Set Position} (hA : MeasurableSet A) (k : Cell) :
    croppedCellMeasure A k univ = volume (A ∩ gridRegion k) := by
  rw [croppedCellMeasure, comap_subtype_coe_apply (hA.inter (measurableSet_gridRegion k))]
  simp only [Set.image_univ, Subtype.range_coe]

lemma croppedCellMeasure_finite {A : Set Position} (hA : MeasurableSet A) (k : Cell) :
    IsFiniteMeasure (croppedCellMeasure A k) := by
  constructor
  rw [croppedCellMeasure_univ hA k]
  exact ((measure_mono inter_subset_right).trans (volume_gridRegion_le k)).trans_lt ENNReal.ofReal_lt_top

lemma croppedCellMeasure_volume {A : Set Position} (hA : MeasurableSet A) (k : Cell) :
    ((croppedCellMeasure A k) univ).toReal ≤ 1/64 := by
  rw [croppedCellMeasure_univ hA k]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    ((measure_mono (inter_subset_right (s := A))).trans (volume_gridRegion_le k))
  simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/64)] using hh

lemma croppedCellMeasure_map {A : Set Position} (hA : MeasurableSet A) (k : Cell) :
    Measure.map Subtype.val (croppedCellMeasure A k) = volume.restrict (A ∩ gridRegion k) :=
  map_comap_subtype_coe (hA.inter (measurableSet_gridRegion k)) volume

lemma croppedCell_diameter {A : Set Position} {k : Cell} (x y : CroppedCell A k) :
    dist (x : Position) y ≤ 1 :=
  same_cell_diameter (x.property.2.trans y.property.2.symm)

lemma croppedCell_partition {I : Type} [Fintype I] (e : I → Cell) (he : Function.Injective e)
    {A : Set Position} (hA : MeasurableSet A) (hcover : ∀ x ∈ A, ∃ i, cellOf x = e i) :
    volume.restrict A = ∑ i, Measure.map Subtype.val (croppedCellMeasure A (e i)) := by
  have hd : Pairwise (Disjoint on (fun i => A ∩ gridRegion (e i))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hij (he (hx.2.symm.trans hy.2))
  have hu : (⋃ i, A ∩ gridRegion (e i)) = A := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, gridRegion, mem_ofPred_eq]
    exact ⟨fun ⟨_,hx,_⟩ => hx, fun hx => by obtain ⟨i,hi⟩ := hcover x hx; exact ⟨i,hx,hi⟩⟩
  rw [← hu, Measure.restrict_iUnion hd (fun i => hA.inter (measurableSet_gridRegion (e i))), Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [hu, croppedCellMeasure_map hA]

end RadialTransition

end

end OAI

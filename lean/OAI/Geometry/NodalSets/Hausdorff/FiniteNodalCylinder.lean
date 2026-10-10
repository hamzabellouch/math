import OAI.Geometry.NodalSets.Hausdorff.PhysicalNodalCylinder

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

lemma finite_nodal_cylinder_measure {ι : Type*} (t : Finset ι)
    (f : Coord → ℝ) (hf : Continuous f) (x : ι → Coord) (R : ι → ℝ) (j : ι → Fin 4)
    {U : Set Coord} {tau r : ℝ} (ht : 0 ≤ tau) (hr : 0 ≤ r) (htr : tau+r ≤ 1)
    (hR : ∀ i ∈ t, 0 < R i)
    (hdis : (↑t : Set ι).PairwiseDisjoint (fun i ↦ sourceClosedBall (x i) (R i)))
    (hU : ∀ i ∈ t, sourceClosedBall (x i) (R i) ⊆ U)
    (hsign : ∀ i ∈ t,
      (∀ y ∈ sourceClosedBall (x i) (r*R i), 0 < f y) ∧
      (∀ y ∈ sourceClosedBall (x i+R i • (tau • Pi.single (j i) 1)) (r*R i), f y < 0)) :
    ENNReal.ofReal (2*r^3*∑ i ∈ t, (R i)^3) ≤
      Measure.hausdorffMeasure (4:ℝ) ((U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | f y.1 = 0}) := by
  classical
  let Z := fun i ↦ (sourceClosedBall (x i) (R i) ×ˢ Icc (-1:ℝ) 1) ∩
    {y : Coord × ℝ | f y.1 = 0}
  have hm (i : ι) : MeasurableSet (Z i) :=
    (((sourceClosedBall_isCompact (x i) (R i)).measurableSet.prod measurableSet_Icc).inter
      (isClosed_eq (hf.comp continuous_fst) continuous_const).measurableSet)
  have hd : (↑t : Set ι).PairwiseDisjoint Z := by
    intro i hi k hk hik
    apply disjoint_left.mpr
    intro y hyi hyk
    exact disjoint_left.mp (hdis hi hk hik) hyi.1.1 hyk.1.1
  have hsub : (⋃ i ∈ t, Z i) ⊆ (U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Coord × ℝ | f y.1 = 0} := by
    intro y hy
    obtain ⟨i,hi,hyi⟩ := mem_iUnion₂.mp hy
    exact ⟨⟨hU i hi hyi.1.1,hyi.1.2⟩,hyi.2⟩
  calc
    _ = ∑ i ∈ t, ENNReal.ofReal (2*r^3*(R i)^3) := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
      intro i hi
      exact mul_nonneg (by positivity) (pow_pos (hR i hi) 3).le
    _ ≤ ∑ i ∈ t, Measure.hausdorffMeasure (4:ℝ) (Z i) :=
      Finset.sum_le_sum (fun i hi ↦ physical_nodal_cylinder_measure f hf (x i) (j i)
        (hR i hi) ht hr htr (hsign i hi).1 (hsign i hi).2)
    _ = Measure.hausdorffMeasure (4:ℝ) (⋃ i ∈ t, Z i) :=
      (measure_biUnion_finset hd (fun i _ ↦ hm i)).symm
    _ ≤ _ := measure_mono hsub

end
end Yau.Geometry

end OAI

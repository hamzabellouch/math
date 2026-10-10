import OAI.Analysis.LipschitzHilbert.Geometry.RectangleProjection

namespace OAI

/-! The actual projected-popularity packing estimate for the far-angle
rectangle groups, in the finite form needed by the application. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace LipschitzHilbert
variable {ι : Type*}

theorem projected_popularity_packing (R : ι → Rectangle) (s : Finset ι) (S : Rectangle)
    {v : Plane → Plane} {K δ : ℝ≥0} (hv : Continuous v)
    (hR : ∀ i ∈ s, (R i).Admissible v K δ)
    (hL : ∀ i ∈ s, (R i).long ≤ S.long)
    (hinter : ∀ i ∈ s, ((R i).carrier ∩ S.carrier).Nonempty)
    (hangle : ∀ i ∈ s, dist ((R i).axes 0) (S.axes 0) ≤ 1/4)
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i => S.coordinateProjection ((R i).popularSet v))) :
    (δ : ℝ≥0∞) * (∑ i ∈ s, ENNReal.ofReal (R i).long) ≤ 12*ENNReal.ofReal S.long := by
  let P := fun i => S.coordinateProjection ((R i).popularSet v)
  have hPm (i : ι) : MeasurableSet (P i) :=
    (S.isCompact_coordinateProjection ((R i).isCompact_popularSet hv)).measurableSet
  have hsub : (⋃ i ∈ s, P i) ⊆ Icc (-3*S.long) (3*S.long) := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp hx
    exact (Rectangle.projection_in_long_interval (R i) S (hL i hi) (hinter i hi)
      (fun _ hx => hx.1)) hxi
  calc
    _ = ∑ i ∈ s, (δ : ℝ≥0∞)*ENNReal.ofReal (R i).long := Finset.mul_sum _ _ _
    _ ≤ ∑ i ∈ s, 2*volume (P i) :=
      Finset.sum_le_sum (fun i hi => Rectangle.popular_projection_density (R i) S hv (hR i hi) (hangle i hi))
    _ = 2*volume (⋃ i ∈ s, P i) := by
      rw [measure_biUnion_finset hdisj (fun i _ => hPm i),Finset.mul_sum]
    _ ≤ 2*volume (Icc (-3*S.long) (3*S.long)) := mul_le_mul' le_rfl (measure_mono hsub)
    _ = _ := by
      rw [Real.volume_Icc,show 3*S.long- -3*S.long = 6*S.long by ring,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
      ring

end LipschitzHilbert

end

end OAI

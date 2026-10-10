import OAI.Geometry.IsometricImmersion.Caps.BoundedClassReflection
import OAI.Geometry.IsometricImmersion.Caps.CapInductionData

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow

theorem bounded_class_actual_cap_data
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (eta : metricPatchSet g0 kappa) {z : Coord → ℝ} {M : ℕ}
    (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z) :
    ∃ U : Set Coord, IsOpen U ∧ modelSquare ⊆ U ∧ U ⊆ V ∧
      SmoothPositiveOn g0 U ∧ SmoothPositiveOn (perturbedMetric g0 eta.val) U ∧
      CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z := by
  obtain ⟨_,hadm,hjets,hyy,hE⟩ := hclass
  obtain ⟨W,hW,hSW,hg,hz,hD,_,_,hq⟩ := hadm
  let U := W ∩ V
  have hU : IsOpen U := hW.inter hV
  have hSU : modelSquare ⊆ U := fun p hp => ⟨hSW hp,hSV hp⟩
  have hg0U : SmoothPositiveOn g0 U :=
    ⟨fun i j => (hg0.1 i j).mono inter_subset_right,
      fun p hp => hg0.2 p hp.2⟩
  have hgU : SmoothPositiveOn (perturbedMetric g0 eta.val) U :=
    ⟨fun i j => (hg.1 i j).mono inter_subset_left,
      fun p hp => hg.2 p hp.1⟩
  refine ⟨U,hU,hSU,inter_subset_right,hg0U,hgU,?_⟩
  exact ⟨hz.mono inter_subset_left,hjets,(fun p hp => (hyy p hp).1),hE,hq,hD⟩

end SmoothLocal.Perturbation

end

end OAI

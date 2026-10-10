import OAI.Geometry.CylinderCovering.Convexity.RegularCounterexamples
import OAI.Geometry.CylinderCovering.Convexity.CylinderBridge
import OAI.Geometry.CylinderCovering.Convexity.CompactParallelogramApproximation

namespace OAI

noncomputable section
open Set MeasureTheory
namespace CylinderCovering

theorem parallelogramCounterexample_of_compact {S : Set Space} {n : ℕ}
    (C : Fin n → RuledApproximation.Cylinder)
    (hcompact : ∀ i, IsCompact (C i).base)
    (hcov : S ⊆ RuledApproximation.familySet C)
    (harea : RuledApproximation.familyArea C < minimumShadowArea S / 2) :
    ∃ m : ℕ, ∃ D : Fin m → RuledApproximation.Cylinder,
      (∀ i, (D i).parallelogram) ∧ S ⊆ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea D < minimumShadowArea S / 2 ∧
      relativeCost S D < 1 / 2 := by
  have hnonneg : 0 ≤ RuledApproximation.familyArea C :=
    Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have hmin : 0 < minimumShadowArea S := by linarith
  let ε := (minimumShadowArea S / 2 - RuledApproximation.familyArea C) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨m, D, hD, hCD, hcost⟩ :=
    RuledApproximation.compact_family_parallelogram_cover C hcompact hε
  have hstrict : RuledApproximation.familyArea D < minimumShadowArea S / 2 := by
    dsimp [ε] at hcost
    linarith
  refine ⟨m, D, hD, hcov.trans hCD, hstrict, ?_⟩
  exact RuledApproximation.relativeCost_lt_half_of_familyArea_lt S hmin D hstrict

theorem parallelogramCounterexample_of_triangular {S : Set Space} {n : ℕ}
    (C : Fin n → TriangularCovering.TriCylinder)
    (hcov : triangularCovers S C)
    (harea : TriangularCovering.totalArea C < minimumShadowArea S / 2) :
    ∃ m : ℕ, ∃ D : Fin m → RuledApproximation.Cylinder,
      (∀ i, (D i).parallelogram) ∧ S ⊆ RuledApproximation.familySet D ∧
      RuledApproximation.familyArea D < minimumShadowArea S / 2 ∧
      relativeCost S D < 1 / 2 := by
  let C' : Fin n → RuledApproximation.Cylinder := fun i => (C i).toCylinder
  have harea' : RuledApproximation.familyArea C' < minimumShadowArea S / 2 := by
    simpa only [RuledApproximation.familyArea, C',
      TriangularCovering.TriCylinder.toCylinder_area, TriangularCovering.totalArea] using harea
  apply parallelogramCounterexample_of_compact C'
    (fun i => (C i).toCylinder_compact) ?_ harea'
  intro x hx
  obtain ⟨i, hi⟩ := hcov x hx
  exact mem_iUnion.mpr ⟨i, by
    simpa only [C', TriangularCovering.TriCylinder.toCylinder_carrier] using hi⟩

theorem regularParallelogramCounterexample_result :
    RegularParallelogramCounterexampleStatement := by
  intro S hS
  obtain ⟨n, C, hcov, harea, _⟩ := regularTriangularCounterexample_result S hS
  exact parallelogramCounterexample_of_triangular C hcov harea

theorem regularOpenCounterexample_result : RegularOpenCounterexampleStatement :=
  regularOpen_of_regularTriangular regularTriangularCounterexample_result

end CylinderCovering

end

end OAI

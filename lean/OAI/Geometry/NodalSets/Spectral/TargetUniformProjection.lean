import OAI.Geometry.NodalSets.Charts.TargetMetricEnergy
import OAI.Geometry.NodalSets.Charts.TargetProductChart

namespace OAI

namespace Yau.Target
open Bundle Manifold Set MeasureTheory Yau.Jets
open scoped ENNReal NNReal ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F]

 theorem uniform_smooth_projection_nodal_measure (g0 : SmoothMetric) (L : ℝ≥0) (hL : 0 < L)
    (P : Manifold5 → F) (hP : ContMDiff modelWithCorners 𝓘(ℝ,F) ∞ P) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ g : SmoothMetric,
      (∀ (x : Manifold5) (v : TangentSpace modelWithCorners x),
        g0.inner x v v ≤ (L:ℝ)^2*g.inner x v v) →
      ∀ (u : Manifold5 → ℝ) (Z : Set F), Z ⊆ P '' {x | u x = 0} →
        Measure.hausdorffMeasure (4:ℝ) Z ≤ (C : ℝ≥0∞)^4 * nodalMeasure g u := by
  obtain ⟨B,hB,hE⟩ := smooth_projection_energy_bound g0 P hP
  refine ⟨B*L,mul_pos hB hL,?_⟩
  intro g hcomp
  apply energy_projection_nodal_measure g P hP (B*L) (mul_pos hB hL)
  intro x v
  calc
    ‖mfderiv modelWithCorners 𝓘(ℝ,F) P x v‖^2 ≤ (B:ℝ)^2*g0.inner x v v := hE x v
    _ ≤ (B:ℝ)^2*((L:ℝ)^2*g.inner x v v) := by gcongr; exact hcomp x v
    _ = ((B*L:ℝ≥0):ℝ)^2*g.inner x v v := by simp only [NNReal.coe_mul]; ring

 theorem uniform_compact_coordinate_nodal_transfer (g0 : SmoothMetric) (L : ℝ≥0) (hL : 0 < L)
    (p : Manifold5) (a : ℝ) {b : ℝ} (hb : b ≠ 0) {K : Set (Coord × ℝ)} (hK : IsCompact K)
    (hKD : K ⊆ productChartDomain p a b) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ g : SmoothMetric,
      (∀ (x : Manifold5) (v : TangentSpace modelWithCorners x),
        g0.inner x v v ≤ (L:ℝ)^2*g.inner x v v) →
      ∀ (u : Manifold5 → ℝ) (Z : Set (Coord × ℝ)), Z ⊆ K →
        (∀ z ∈ Z, u (productChartInverse p a b z) = 0) →
        Measure.hausdorffMeasure (4:ℝ) Z ≤ (C : ℝ≥0∞)^4 * nodalMeasure g u := by
  obtain ⟨P,hP,hPK⟩ := compact_productChart_extension p a hb hK hKD
  obtain ⟨C,hC,hproj⟩ := uniform_smooth_projection_nodal_measure g0 L hL P hP
  refine ⟨C,hC,?_⟩
  intro g hcomp u Z hZ hzero
  apply hproj g hcomp
  intro z hz
  exact ⟨productChartInverse p a b z,hzero z hz,hPK z (hZ hz)⟩

end
end Yau.Target

end OAI

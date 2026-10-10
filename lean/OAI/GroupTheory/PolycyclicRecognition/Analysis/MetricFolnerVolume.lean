import OAI.GroupTheory.PolycyclicRecognition.Analysis.RightFolnerExpansion
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LowerPacking
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseMultiplicity
import Mathlib.Topology.MetricSpace.Thickening

namespace OAI

/-! # The volume estimates in metric Følner transfer

A finite union of fixed-radius target balls has mass bounded below by its
source cardinality, using a separated net and bounded coarse multiplicity.
Its metric boundary is covered by balls indexed by the source boundary.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set MeasureTheory
open scoped ENNReal

def metricFolnerSet {X Y : Type*} [PseudoMetricSpace Y]
    (u : X → Y) (E : Finset X) (a : ℝ) : Set Y :=
  ⋃ p ∈ E, ball (u p) a

theorem metricFolnerSet_measurable {X Y : Type*} [PseudoMetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] (u : X → Y) (E : Finset X) (a : ℝ) :
    MeasurableSet (metricFolnerSet u E a) :=
  E.finite_toSet.measurableSet_biUnion (fun _ _ => measurableSet_ball)

theorem metricFolnerSet_volume_lower
    {X Y : Type*} [Group Y] [MetricSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [MeasurableMul Y] [IsIsometricSMul Y Y]
    (μ : Measure Y) [μ.IsMulLeftInvariant] (u : X → Y) (E : Finset X)
    {a : ℝ} (ha : 0 < a) (M : ℕ)
    (hmult : ∀ (y : Y) (A : Finset X),
      (∀ x ∈ A, dist (u x) y ≤ a + a) → A.card ≤ M) :
    (E.card : ℝ≥0∞) * μ (ball (1 : Y) a) ≤
      (M : ℝ≥0∞) * μ (metricFolnerSet u E a) := by
  classical
  obtain ⟨t, ht, hsep, hcover⟩ := exists_separated_net_of_totallyBounded
    (E.image u).finite_toSet.isCompact.totallyBounded (add_pos ha ha)
  have hc : E.card ≤ t.card * M :=
    card_le_cover_mul_of_bounded_multiplicity E u t (a + a) M
      (fun x hx => hcover (u x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)) hmult
  have hv : (t.card : ℝ≥0∞) * μ (ball (1 : Y) a) ≤ μ (metricFolnerSet u E a) := by
    apply separated_card_mul_ball_le μ t a _
      (fun x hx y hy hxy => (hsep x hx y hy hxy).le)
    intro y hy z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (ht hy)
    exact Set.mem_iUnion₂.mpr ⟨x, hx, hz⟩
  have hc' : (E.card : ℝ≥0∞) ≤ (t.card : ℝ≥0∞) * M := by exact_mod_cast hc
  calc
    (E.card : ℝ≥0∞) * μ (ball (1 : Y) a) ≤
        ((t.card : ℝ≥0∞) * M) * μ (ball (1 : Y) a) := by gcongr
    _ = (M : ℝ≥0∞) * ((t.card : ℝ≥0∞) * μ (ball (1 : Y) a)) := by ac_rfl
    _ ≤ _ := by gcongr

theorem metricFolnerSet_boundary_subset
    {X Y : Type*} [Group X] [MetricSpace X] [IsIsometricSMul X X]
    [PseudoMetricSpace Y] [DecidableEq X]
    (hfinite : ∀ R : ℝ, (closedBall (1 : X) R).Finite)
    (u : X → Y) (E : Finset X) {a c K C R : ℝ}
    (hca : c < a) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hsurj : ∀ y, ∃ q, dist y (u q) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    cthickening R (metricFolnerSet u E a) \ metricFolnerSet u E a ⊆
      ⋃ q ∈ finiteMetricNeighborhood hfinite E (K * (c + (R + 1) + a) + C) \ E,
        closedBall (u q) c := by
  rintro y ⟨hy, hyout⟩
  have hy' : y ∈ thickening (R + 1) (metricFolnerSet u E a) :=
    cthickening_subset_thickening' (by linarith) (by linarith) _ hy
  obtain ⟨z, hz, hyz⟩ := mem_thickening_iff.mp hy'
  obtain ⟨p, hp, hzp⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨q, hyq⟩ := hsurj y
  have hqnot : q ∉ E := by
    intro hq
    apply hyout
    exact Set.mem_iUnion₂.mpr ⟨q, hq, lt_of_le_of_lt hyq hca⟩
  have hqp : dist q p ≤ K * (c + (R + 1) + a) + C := by
    apply (hlower q p).trans
    apply add_le_add (mul_le_mul_of_nonneg_left _ hK) le_rfl
    calc
      dist (u q) (u p) ≤ dist (u q) y + dist y (u p) := dist_triangle _ _ _
      _ ≤ dist (u q) y + (dist y z + dist z (u p)) := by
        gcongr
        exact dist_triangle _ _ _
      _ ≤ c + (R + 1) + a := by
        rw [dist_comm (u q) y]
        have hzp' : dist z (u p) < a := hzp
        linarith
  exact Set.mem_iUnion₂.mpr ⟨q,
    Finset.mem_sdiff.mpr ⟨(mem_finiteMetricNeighborhood hfinite E _ q).mpr ⟨p, hp, hqp⟩,
      hqnot⟩, hyq⟩

theorem metricFolnerSet_boundary_volume
    {X Y : Type*} [Group X] [MetricSpace X] [IsIsometricSMul X X]
    [Group Y] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableMul Y] [IsIsometricSMul Y Y] [DecidableEq X]
    (μ : Measure Y) [μ.IsMulLeftInvariant]
    (hfinite : ∀ R : ℝ, (closedBall (1 : X) R).Finite)
    (u : X → Y) (E : Finset X) {a c K C R : ℝ}
    (hca : c < a) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hsurj : ∀ y, ∃ q, dist y (u q) ≤ c)
    (hlower : ∀ x y, dist x y ≤ K * dist (u x) (u y) + C) :
    μ (cthickening R (metricFolnerSet u E a) \ metricFolnerSet u E a) ≤
      ((finiteMetricNeighborhood hfinite E (K * (c + (R + 1) + a) + C) \ E).card : ℝ≥0∞) *
        μ (closedBall (1 : Y) c) := by
  apply (measure_mono (metricFolnerSet_boundary_subset hfinite u E hca hK hR hsurj hlower)).trans
  apply (measure_biUnion_finset_le _ _).trans
  simp only [measure_closedBall_eq_identity, Finset.sum_const, nsmul_eq_mul, le_refl]

end PolycyclicRecognition

end

end OAI

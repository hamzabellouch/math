import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarseEquivalence
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.Bounded

namespace OAI

/-!
# Metric quasi-isometries and the discrete group coarse structure

The finiteness and duality endgame uses finite sets of group differences.
Here an actual metric quasi-isometry supplies that data. The metrics are
left invariant and their bounded identity balls are finite, as for word
metrics on finitely generated groups. No recognition theorem is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric

variable {G H : Type*} [Group G] [Group H]
  [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul G G] [IsIsometricSMul H H]

/-- Left invariance measures a group difference by the distance between its
two endpoints. -/
theorem dist_one_groupDifference (x y : G) : dist 1 (x⁻¹ * y) = dist x y := by
  simpa using (dist_mul_left x⁻¹ x y)

/-- An upper coarse Lipschitz inequality sends each finite set of group
differences into a finite identity ball. -/
theorem groupBornologous_of_metric_bound (f : G → H)
    (hfinite : ∀ R : ℝ, (closedBall (1 : H) R).Finite)
    {K C : ℝ} (hK : 0 ≤ K)
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C) :
    GroupBornologous f := by
  intro S hS
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall (1 : G)).mp hS.isBounded
  refine ⟨closedBall (1 : H) (K * R + C), hfinite _, ?_⟩
  intro x y hxy
  have hdist : dist x y ≤ R := by
    have h := hR hxy
    simpa only [mem_closedBall, dist_comm (x⁻¹ * y), dist_one_groupDifference] using h
  change dist ((f x)⁻¹ * f y) 1 ≤ _
  rw [dist_comm, dist_one_groupDifference]
  exact (hupper x y).trans (add_le_add (mul_le_mul_of_nonneg_left hdist hK) le_rfl)

/-- Uniformly bounded metric displacement is a finite set of group errors. -/
theorem finite_groupDifference_range_of_metric_bound (r : G → G)
    (hfinite : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    {E : ℝ} (herror : ∀ x, dist x (r x) ≤ E) :
    (Set.range fun x => x⁻¹ * r x).Finite := by
  apply (hfinite E).subset
  rintro _ ⟨x, rfl⟩
  simpa only [mem_closedBall, dist_comm (x⁻¹ * r x), dist_one_groupDifference]
    using herror x

/-- Coarse inverse metric maps produce the concrete equivalence used by
Li's group-cohomological invariance theorems. -/
def groupCoarseEquivalenceOfMetricInverse (f : G → H) (r : H → G)
    (hfiniteG : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (hfiniteH : ∀ R : ℝ, (closedBall (1 : H) R).Finite)
    {K C K' C' E E' : ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hf : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hr : ∀ x y, dist (r x) (r y) ≤ K' * dist x y + C')
    (hleft : ∀ x, dist x (r (f x)) ≤ E)
    (hright : ∀ y, dist y (f (r y)) ≤ E') :
    GroupCoarseEquivalence G H where
  toFun := f
  invFun := r
  bornologous_toFun := groupBornologous_of_metric_bound f hfiniteH hK hf
  bornologous_invFun := groupBornologous_of_metric_bound r hfiniteG hK' hr
  left_error := finite_groupDifference_range_of_metric_bound (r ∘ f) hfiniteG hleft
  right_error := finite_groupDifference_range_of_metric_bound (f ∘ r) hfiniteH hright

/-- A metric quasi-isometry yields an actual discrete-group coarse
equivalence. The inverse is chosen from coarse surjectivity, and all its
control estimates are derived from the lower inequality. -/
def groupCoarseEquivalenceOfQuasiIsometry (f : G → H)
    (hfiniteG : ∀ R : ℝ, (closedBall (1 : G) R).Finite)
    (hfiniteH : ∀ R : ℝ, (closedBall (1 : H) R).Finite)
    {K C K' C' E : ℝ} (hK : 0 ≤ K) (hK' : 0 ≤ K')
    (hupper : ∀ x y, dist (f x) (f y) ≤ K * dist x y + C)
    (hlower : ∀ x y, dist x y ≤ K' * dist (f x) (f y) + C')
    (hsurj : ∀ y, ∃ x, dist y (f x) ≤ E) : GroupCoarseEquivalence G H := by
  choose r hr using hsurj
  refine groupCoarseEquivalenceOfMetricInverse f r hfiniteG hfiniteH hK hK'
    hupper (C' := K' * (E + E) + C') (E := K' * E + C') (E' := E) ?_ ?_ hr
  · intro x y
    have hdist : dist (f (r x)) (f (r y)) ≤ dist x y + (E + E) := by
      calc
        dist (f (r x)) (f (r y)) ≤
            dist (f (r x)) x + dist x y + dist y (f (r y)) :=
          dist_triangle4 _ _ _ _
        _ ≤ E + dist x y + E := by
          gcongr
          exact (dist_comm (f (r x)) x).trans_le (hr x)
          exact hr y
        _ = dist x y + (E + E) := by ring
    calc
      dist (r x) (r y) ≤ K' * dist (f (r x)) (f (r y)) + C' := hlower _ _
      _ ≤ K' * (dist x y + (E + E)) + C' := by gcongr
      _ = K' * dist x y + (K' * (E + E) + C') := by ring
  · intro x
    exact (hlower x (r (f x))).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hr (f x)) hK') le_rfl)

end PolycyclicRecognition

end

end OAI

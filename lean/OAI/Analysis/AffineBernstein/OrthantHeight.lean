import Mathlib
import OAI.Analysis.AffineBernstein.ConvexGradientBound
import OAI.Analysis.AffineBernstein.OrthantGeometry

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open Filter
open scoped Topology

open Filter Metric
open scoped Topology

def orthantHeight (n : ℕ) : (Space n × ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n ⊕ Unit, (ContinuousLinearMap.proj i).comp
    (ambientCoordinates n).toContinuousLinearEquiv.toContinuousLinearMap

lemma orthantHeight_apply {n : ℕ} (z : Space n × ℝ) :
    orthantHeight n z = ∑ i, ambientCoordinates n z i := by
  simp [orthantHeight]

def orthantCenter (n : ℕ) : Space n × ℝ :=
  (ambientCoordinates n).symm (fun _ => 1)

lemma orthantCenter_coordinates {n : ℕ} (i : Fin n ⊕ Unit) :
    ambientCoordinates n (orthantCenter n) i = 1 := by simp [orthantCenter]

lemma orthantCenter_height (n : ℕ) : orthantHeight n (orthantCenter n) = (n:ℝ)+1 := by
  rw [orthantHeight_apply]
  simp [orthantCenter_coordinates]

lemma orthantCenter_interior (n : ℕ) : orthantCenter n ∈ interior (ambientOrthant n) :=
  pos_mem_interior_ambientOrthant (fun i => by rw [orthantCenter_coordinates]; norm_num)

lemma orthantHeight_ne_zero (n : ℕ) : orthantHeight n ≠ 0 := by
  intro hh
  have h := orthantCenter_height n
  rw [hh, zero_apply] at h
  have hn := Nat.cast_nonneg (α := ℝ) n
  linarith

lemma orthant_cap_bounded (n : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    Bornology.IsBounded (ambientOrthant n ∩ {z | orthantHeight n z ≤ b}) := by
  apply (isCompact_closedBall (0 : Space n × ℝ) (max (n*b) b)).isBounded.subset
  intro z hz
  have hcoord (i : Fin n ⊕ Unit) : |ambientCoordinates n z i| ≤ b := by
    rw [abs_of_nonneg (hz.1 i)]
    calc
      _ ≤ ∑ i, ambientCoordinates n z i :=
        Finset.single_le_sum (fun i _ => hz.1 i) (Finset.mem_univ i)
      _ ≤ b := by rw [← orthantHeight_apply]; exact hz.2
  have hbase : ‖z.1‖ ≤ n*b := norm_le_card_of_coord_bound hb
    (fun i => by simpa only [ambientCoordinates_inl] using hcoord (Sum.inl i))
  have hlast : ‖z.2‖ ≤ b := by
    simpa only [ambientCoordinates_inr,Real.norm_eq_abs] using hcoord (Sum.inr ())
  simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] using max_le_max hbase hlast

end AffineBernstein

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Analysis.PairMeanControl
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace OAI

/-! # Continuous uniformly bounded label-distance observables -/

noncomputable section

namespace PolycyclicRecognition

open Metric
open scoped NNReal ENNReal

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {Λ K : ℝ≥0}

omit [IsTopologicalGroup G] [IsIsometricSMul G G] in
/-- For each fixed scale the observable is continuous on the compact pair section. -/
theorem continuous_pair_label_distance
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    (g : G) (r : ℝ) (S : Set W) :
    Continuous (fun p : NormalizedPair G Λ => infDist (r⁻¹ • pairHeight π g p) S) :=
  (continuous_infDist_pt S).comp ((pairHeightProfile π hπ g).continuous.const_smul _)

omit [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G] in
/-- Linear growth of the sampled group element gives a common bound at all
scales at least one, using any fixed member of the comparison set. -/
theorem pair_label_distance_le
    (π : G →* Multiplicative W)
    (hπ : LipschitzWith K (fun g => (π g).toAdd))
    {g : G} {r R : ℝ} (hr : 1 ≤ r) (_hR : 0 ≤ R) (hg : dist 1 g ≤ R * r)
    {S : Set W} {w : W} (hw : w ∈ S) (p : NormalizedPair G Λ) :
    infDist (r⁻¹ • pairHeight π g p) S ≤ (K : ℝ) * Λ * R + ‖w‖ := by
  have hr0 : 0 < r := by linarith
  have hn : ‖r⁻¹ • pairHeight π g p‖ ≤ (K : ℝ) * Λ * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr0)]
    calc
      _ ≤ r⁻¹ * ((K : ℝ) * Λ * dist 1 g) :=
        mul_le_mul_of_nonneg_left (norm_pairHeight_le π hπ g p) (inv_nonneg.mpr hr0.le)
      _ ≤ r⁻¹ * ((K : ℝ) * Λ * (R * r)) := by gcongr
      _ = _ := by field_simp
  exact (infDist_le_dist_of_mem hw).trans (by
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (add_le_add hn le_rfl))

end PolycyclicRecognition

end

end OAI

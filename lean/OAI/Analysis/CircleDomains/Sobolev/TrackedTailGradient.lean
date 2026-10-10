import OAI.Analysis.CircleDomains.Selection.TrackedTailSequence

namespace OAI

/-! Convert the tracked gradient's L2 metric estimate to its actual
weak-gradient difference, including restriction to a working disk. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => tailWitness hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem tail_gradient_norm_error (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) (L : ℝ) :
    (eLpNorm (fun x => (W k i n).weakGrad x-(W k i 0).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤
      ∑ j ∈ Finset.range n, recursiveTestBudget ε (k+j) (states (k+j)).tolerances := by
  have h := tail_gradient_error hsupply hsard hsch hG hinf hTD ha hBa hε T k i n
  rw [Lp.dist_edist,Lp.edist_toLp_toLp] at h
  change (eLpNorm (fun x => (W k i n).weakGrad x-(W k i 0).weakGrad x) 2
    (volume.restrict (physicalPlaneDomain G))).toReal ≤ _ at h
  have hm : MemLp (fun x => (W k i n).weakGrad x-(W k i 0).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G)) :=
    (W k i n).weakGrad_memLp.sub (W k i 0).weakGrad_memLp
  exact (ENNReal.toReal_mono hm.eLpNorm_ne_top (eLpNorm_mono_measure _
    (Measure.restrict_mono (inter_subset_left : physicalPlaneDomain G ∩ ball 0 L ⊆ physicalPlaneDomain G) le_rfl))).trans h

end AppendingSequence
end CircleDomainRigidity

end

end OAI

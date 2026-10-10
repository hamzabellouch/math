import OAI.Combinatorics.ContingencyTables.Rooted.RootedOracleDensity
import OAI.Combinatorics.ContingencyTables.Counting.CompanionOracleCut

namespace OAI

/-! # The selected-root density satisfies the actual weighted grid cut bound -/

namespace ContingencyTables.RootedOracleDensity

open scoped BigOperators Classical
open CompanionFactorialApplication GridBoundary
open CompanionOracleDensity (dimension height closedBin_distances tube_distances interpolation_bounds)

variable {I J : Type*} [Fintype I] [Fintype J]

lemma tube_comparison (A : Instance I J) (S : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    {K : ℕ} {Q : (Fin (dimension A) → ℤ) → Prop} (edge : CutEdge K Q)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (x : Fin (dimension A) → ℝ)
    (hx : x ∈ edgeTube edge r) :
    rho A S C a z x ≤ 4*min (V A S C a z (realCorner edge.val.1))
      (V A S C a z (realCorner edge.val.2.1)) := by
  obtain ⟨hlo,hhi⟩ := tube_distances A edge r x hx
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
  apply le_min
  · apply DenseWeights.tube_density_comparison
    exact (exponent_change A S C a hC ha haH z x _ (1+r) (by positivity) hlo).trans (by linarith)
  · apply DenseWeights.tube_density_comparison
    exact (exponent_change A S C a hC ha haH z x _ (1+r) (by positivity) hhi).trans (by linarith)

/-- The companion bin weights satisfy the source cut bound directly
from their actual forest density and the precise published PL input. -/
theorem weighted_min_cut (A : Instance I J) (S : RootedCompletion.Selection A.T) (C a : ℝ) (hC : 0 < C)
    (ha : 0 ≤ a) (haH : a ≤ height A C) (z : View A → ℕ)
    (K : ℕ) (hK : 1 ≤ K)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (Q : (Fin (dimension A) → ℤ) → Prop)
    (hne : Nonempty (Selected K Q)) (hne' : Nonempty (Selected K (fun x => ¬Q x))) :
    (1/(128*(A.d:ℝ)*K))*min
        (∑ v : Selected K Q,V A S C a z (realCorner v.val))
        (∑ v : Selected K (fun x => ¬Q x),V A S C a z (realCorner v.val)) ≤
      ∑ e : CutEdge K Q,min (V A S C a z (realCorner e.val.1))
        (V A S C a z (realCorner e.val.2.1)) := by
  obtain ⟨ht,ht1,hr,hsize⟩ := interpolation_bounds A.d K (dimension A) A.hd hK
    (ForestScaledPenalty.free_card_le A)
  have hh := GridBoundary.weighted_min_cut hPL Q (denseInterpolation A.d K) ht ht1 hr hsize
    (rho A S C a z) (fun v => V A S C a z (realCorner v))
    (fun v => DenseWeights.binWeight_pos _ _ _) (rho_continuous A S C a z).continuousOn
    (fun x _ => rho_positive A S C a z x)
    (fun x _ y _ t ht ht1 => rho_logConcave A S C a hC ha z x (Set.mem_univ _) y (Set.mem_univ _) t ht ht1)
    (fun v x hx => by
      have hclosed : ClosedBin (corner v) x := fun i => ⟨(hx i).1.le,(hx i).2.le⟩
      exact (bin_comparison A S C a hC ha haH z (realCorner v) x
        (fun i => by simpa only [abs_sub_comm] using closedBin_distances A v x hclosed i)).1)
    (fun e x hx => tube_comparison A S C a hC ha haH z e (denseInterpolation A.d K*K)
      (by positivity) (by linarith) x hx.1) hne hne'
  have hg := two_rpow_gain (denseInterpolation A.d K) ht.le
  have hm : 0 ≤ min (∑ v : Selected K Q,V A S C a z (realCorner v.val))
      (∑ v : Selected K (fun x => ¬Q x),V A S C a z (realCorner v.val)) := by
    apply le_min <;> exact Finset.sum_nonneg (fun _ _ => (DenseWeights.binWeight_pos _ _ _).le)
  have he : 1/(128*(A.d:ℝ)*K)=denseInterpolation A.d K/32 := by
    unfold denseInterpolation
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_right (by linarith : denseInterpolation A.d K/32 ≤
    ((2:ℝ)^denseInterpolation A.d K-1)/16) hm).trans hh

end ContingencyTables.RootedOracleDensity

end OAI

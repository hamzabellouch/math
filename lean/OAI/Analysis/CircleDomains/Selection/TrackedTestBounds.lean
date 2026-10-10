import OAI.Analysis.CircleDomains.Uniformization.TrackedTestLimits
import OAI.Analysis.CircleDomains.Sobolev.SphericalGradientEnergyNorm

namespace OAI

/-! Uniform scalar and Dirichlet bounds for the actual tracked old tests.
The bounds depend only on the original test and the total recursive budget. -/
open Set Function Filter MeasureTheory
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
local notation "f" => scalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => witness hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "d" => (fun n : ℕ => recursiveTestBudget ε n (AppendingConstructionState.tolerances (states n)))

 theorem finite_budget_le (n : ℕ) : ∑ j ∈ Finset.range n, d j ≤ ε/4 := by
  have hd := summable_recursive_test_budget hε (fun n => (states n).tolerances)
    (fun n => (states n).positive)
  exact (hd.sum_le_tsum (Finset.range n) (fun j _ =>
    (recursiveTestBudget_pos hε j (states j).positive).le)).trans
    (tsum_recursive_test_budget_le hε (fun n => (states n).tolerances)
      (fun n => (states n).positive))

 theorem scalar_initial_error (i : Fin T.count) (n : ℕ) (x : EuclideanPlane) :
    |f i n x-T.test i x| ≤ ε/4 := by
  have hstep (j : ℕ) : dist (f i j x) (f i (j+1) x) ≤ d j := by
    simpa only [Real.dist_eq,abs_sub_comm] using
      (step_uniform hsupply hsard hsch hG hinf hTD ha hBa hε T i j x).le
  have hh := dist_le_range_sum_of_dist_le n (fun {j} _ => hstep j)
  have hh' := hh.trans (finite_budget_le hsupply hsard hsch hG hinf hTD ha hBa hε T n)
  change |T.test i x-f i n x| ≤ ε/4 at hh'
  simpa only [abs_sub_comm] using hh'

 theorem gradient_norm_bound (i : Fin T.count) (n : ℕ) :
    ‖(W i n).weakGrad_memLp.toLp ((W i n).weakGrad)‖ ≤
      ‖(T.witness i).weakGrad_memLp.toLp ((T.witness i).weakGrad)‖+ε/4 := by
  let V := fun n => (W i n).weakGrad_memLp.toLp ((W i n).weakGrad)
  have hstep (j : ℕ) : dist (V j) (V (j+1)) ≤ d j := by
    rw [dist_comm,Lp.dist_edist,Lp.edist_toLp_toLp]
    exact (step_gradient hsupply hsard hsch hG hinf hTD ha hBa hε T i j).le
  have hh := (dist_le_range_sum_of_dist_le n (fun {j} _ => hstep j)).trans
    (finite_budget_le hsupply hsard hsch hG hinf hTD ha hBa hε T n)
  have hn := norm_le_norm_sub_add (V n) (V 0)
  rw [← dist_eq_norm,dist_comm] at hn
  change ‖V n‖ ≤ ‖V 0‖+ε/4
  linarith

end AppendingSequence
end CircleDomainRigidity

end

end OAI

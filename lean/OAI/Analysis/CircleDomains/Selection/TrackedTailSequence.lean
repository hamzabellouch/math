import OAI.Analysis.CircleDomains.Selection.RecursiveTestHistory

namespace OAI

/-! Track a scalar from any saved stage, with cumulative uniform and
Sobolev-gradient errors controlled by the actual later budgets. -/
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

 def tailIndex (k : ℕ) (i : Fin (states k).family.count) :
    (n : ℕ) → Fin (states (k+n)).family.count
  | 0 => i
  | n+1 => (tailIndex k i n).succ.succ

local notation "idx" => tailIndex hsupply hsard hsch hG hinf hTD ha hBa hε T

 def tailScalar (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) : EuclideanPlane → ℝ :=
  (states (k+n)).family.test (idx k i n)

 def tailWitness (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) :
    DeGiorgi.MemW1pWitness 2 (tailScalar hsupply hsard hsch hG hinf hTD ha hBa hε T k i n)
      (physicalPlaneDomain G) := (states (k+n)).family.witness (idx k i n)

local notation "f" => tailScalar hsupply hsard hsch hG hinf hTD ha hBa hε T
local notation "W" => tailWitness hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem tail_step_uniform (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) (x : EuclideanPlane) :
    |f k i (n+1) x-f k i n x| < recursiveTestBudget ε (k+n) (states (k+n)).tolerances := by
  exact ((states (k+n)).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε (k+n)).data.old_close (idx k i n) x

 theorem tail_step_gradient (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) :
    (eLpNorm (fun x => (W k i (n+1)).weakGrad x-(W k i n).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G))).toReal <
      recursiveTestBudget ε (k+n) (states (k+n)).tolerances := by
  exact ((states (k+n)).chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε (k+n)).data.old_error (idx k i n)

 theorem tail_uniform_error (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) (x : EuclideanPlane) :
    |f k i n x-f k i 0 x| ≤ ∑ j ∈ Finset.range n,
      recursiveTestBudget ε (k+j) (states (k+j)).tolerances := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := abs_sub_le (f k i (n+1) x) (f k i n x) (f k i 0 x)
    have hs := (tail_step_uniform hsupply hsard hsch hG hinf hTD ha hBa hε T k i n x).le
    rw [Finset.sum_range_succ]
    linarith

 theorem tail_gradient_error (k : ℕ) (i : Fin (states k).family.count) (n : ℕ) :
    dist ((W k i n).weakGrad_memLp.toLp ((W k i n).weakGrad))
      ((W k i 0).weakGrad_memLp.toLp ((W k i 0).weakGrad)) ≤
      ∑ j ∈ Finset.range n, recursiveTestBudget ε (k+j) (states (k+j)).tolerances := by
  let F := fun n => (W k i n).weakGrad_memLp.toLp ((W k i n).weakGrad)
  have hs (j : ℕ) : dist (F j) (F (j+1)) ≤
      recursiveTestBudget ε (k+j) (states (k+j)).tolerances := by
    rw [dist_comm,Lp.dist_edist,Lp.edist_toLp_toLp]
    change (eLpNorm (fun x => (W k i (j+1)).weakGrad x-(W k i j).weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G))).toReal ≤ _
    exact (tail_step_gradient hsupply hsard hsch hG hinf hTD ha hBa hε T k i j).le
  rw [dist_comm]
  exact dist_le_range_sum_of_dist_le n (fun {j} _ => hs j)

end AppendingSequence
end CircleDomainRigidity

end

end OAI

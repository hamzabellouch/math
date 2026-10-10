import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeConservation
import OAI.Analysis.LipschitzHilbert.Estimates.StoppedScalarExpansion
import OAI.Analysis.LipschitzHilbert.Trees.SourceMassStopping

namespace OAI

/-! The finite angular-tree conservation law is exactly the stopped
product used in the analytic path estimate. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} {κ : Type} [Fintype κ]

section Path
variable (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
  (cutoff : ℝ) (weight : τ → X → ℝ) (level : ℕ → ℕ)
  (A : ℕ → ℤ → EuclideanSpace ℂ κ) (α p : ℝ) (x : X)

def sourceTreePathMass (top : τ) (j : ℕ) : ℝ :=
  if g.eligible cutoff (precision top) (level j) then
    g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x
  else 0

def sourceTreePathRatio (top : τ) (j : ℕ) : ℝ :=
  g.sourceTreeAmount tops slope precision cutoff weight level A α p x j
      (g.index (level j) (slope top))/
    g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j
      (g.index (level j) (slope top))

variable {g tops slope precision cutoff weight level A α p x}

theorem sourceTreeTail_eq_scalar (M : ℝ) (n j : ℕ) (top : τ) :
    g.sourceTreeTail tops slope precision cutoff weight level A α p x M n j top =
    stoppedScalarExpansion
      (fun k => g.eligible cutoff (precision top) (level k) ∧
        M < g.mass tops slope precision cutoff weight (level k) (g.index (level k) (slope top)) x)
      (g.sourceTreePathRatio tops slope precision cutoff weight level A α p x top)
      (fun k => g.sourceTreeExit tops slope precision cutoff weight level A α p x k top) n j := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    simp only [sourceTreeTail,stoppedScalarExpansion,ih]
    rfl

theorem sourceTreeTail_eq_stopped (M : ℝ) (hM : 0 ≤ M) (count : ℕ) (top : τ)
    (hterminal : ¬g.eligible cutoff (precision top) (level count)) :
    let stop := firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x top) count M
    g.sourceTreeTail tops slope precision cutoff weight level A α p x M count 0 top =
      g.sourceTreeExit tops slope precision cutoff weight level A α p x stop top*
        ∏ j ∈ Finset.range stop,
          g.sourceTreePathRatio tops slope precision cutoff weight level A α p x top j := by
  dsimp only
  let n := g.sourceTreePathMass tops slope precision cutoff weight level x top
  have hlast : n count ≤ M := by
    simpa only [n,sourceTreePathMass,ite_eq_right hterminal] using hM
  have hs := firstMassStop_spec n count M hlast
  have hactive (j : ℕ) :
      (g.eligible cutoff (precision top) (level j) ∧
        M < g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x)
        ↔ M < n j := by
    by_cases he : g.eligible cutoff (precision top) (level j)
    · simp only [n,sourceTreePathMass,he,ite_true,true_and]
    · simp only [n,sourceTreePathMass,he,ite_false,false_and,not_lt_of_ge hM]
  rw [sourceTreeTail_eq_scalar]
  simpa only [Nat.zero_add] using stoppedScalarExpansion_eq
    (fun k => g.eligible cutoff (precision top) (level k) ∧
      M < g.mass tops slope precision cutoff weight (level k) (g.index (level k) (slope top)) x)
    (g.sourceTreePathRatio tops slope precision cutoff weight level A α p x top)
    (fun k => g.sourceTreeExit tops slope precision cutoff weight level A α p x k top)
    count (firstMassStop n count M) 0 hs.1
    (fun j hj => (hactive (0+j)).mpr (by simpa using hs.2.2 j hj))
    (fun h => (not_lt_of_ge hs.2.1) (by
      simpa only [Nat.zero_add] using (hactive _).mp h))

/-- Exact terminal product expansion of the original node amount. -/
theorem sourceTree_terminal_expansion (hp : ∀ t ∈ tops, 0 ≤ precision t)
    (hw : ∀ t x, 0 < weight t x) (hlevel : Monotone level)
    (M : ℝ) (hM : 0 ≤ M) (count : ℕ) (cell : ℤ)
    (hne : (g.cellTops tops slope precision cutoff (level 0) cell).Nonempty)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (level 0) cell,
      ¬g.eligible cutoff (precision t) (level count)) :
    (∑ t ∈ g.cellTops tops slope precision cutoff (level 0) cell,
      let stop := firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x t) count M
      weight t x*g.sourceTreeExit tops slope precision cutoff weight level A α p x stop t*
        ∏ j ∈ Finset.range stop,
          g.sourceTreePathRatio tops slope precision cutoff weight level A α p x t j) =
      g.sourceTreeAmount tops slope precision cutoff weight level A α p x 0 cell := by
  have h := sourceTreeTail_sum (A := A) (α := α) (p := p) (x := x)
    hp hw hlevel M count 0 cell hne
  rw [← h]
  apply Finset.sum_congr rfl
  intro t ht
  rw [sourceTreeTail_eq_stopped M hM count t (hterminal t ht)]
  exact mul_assoc _ _ _

end Path
end LipschitzHilbert.AngularGrid

end

end OAI

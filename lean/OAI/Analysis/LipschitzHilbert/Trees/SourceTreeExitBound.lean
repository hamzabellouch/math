import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeGoodPaths
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathProduct

namespace OAI

/-! The ordinary amplitude envelope gives the actual mass-stop cost.
No positive lower bound on a stopped top weight is needed. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} {κ : Type} [Fintype κ]

 theorem sourceTree_stop_exit_bound
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hw : ∀ t x, 0 < weight t x)
    (level : ℕ → ℕ) (A : ℕ → ℤ → EuclideanSpace ℂ κ)
    (α p M C : ℝ) (hα : 1 ≤ α) (hp : 0 ≤ p) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (x : X) (count : ℕ) (top : τ) (htop : top ∈ tops)
    (hterminal : ¬g.eligible cutoff (precision top) (level count))
    (hamp : ∀ j ≤ count, g.eligible cutoff (precision top) (level j) →
      ‖A j (g.index (level j) (slope top))‖ ≤
        C*g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x) :
    g.sourceTreeExit tops slope precision cutoff weight level A α p x
      (firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x top) count M) top ≤
      1+C^p*(M+1)^(α-1) := by
  let n := g.sourceTreePathMass tops slope precision cutoff weight level x top
  let stop := firstMassStop n count M
  have hlast : n count ≤ M := by
    simpa only [n,sourceTreePathMass,ite_eq_right hterminal] using hM
  have hs := firstMassStop_spec n count M hlast
  change g.sourceTreeExit tops slope precision cutoff weight level A α p x stop top ≤ _
  unfold sourceTreeExit
  split_ifs with he
  · have hn := g.path_mass_pos tops slope precision cutoff weight hw (level stop) top htop he x
    have hsmall : g.mass tops slope precision cutoff weight (level stop)
        (g.index (level stop) (slope top)) x ≤ M+1 := by
      have hm := hs.2.1
      change n stop ≤ M at hm
      rw [show n stop = g.mass tops slope precision cutoff weight (level stop)
        (g.index (level stop) (slope top)) x by
          simp only [n,sourceTreePathMass,ite_eq_left he]] at hm
      linarith
    exact source_exceptional_factor_le _ hn le_rfl hsmall hC hα hp (hamp stop hs.1 he)
  · exact le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hC _)
      (Real.rpow_nonneg (by linarith) _))

end LipschitzHilbert.AngularGrid

end

end OAI

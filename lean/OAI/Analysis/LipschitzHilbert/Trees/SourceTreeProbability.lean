import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeExpansion
import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedAmplitude

namespace OAI

/-! Every child transition in the actual angular tree has mass at most
one. The terminal path weights therefore have the required uniform cap. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable
variable {τ X : Type*} {κ : Type} [Fintype κ]

section Path
variable {g : AngularGrid} {tops : Finset τ} {slope precision : τ → ℝ}
  {cutoff : ℝ} {weight : τ → X → ℝ} {level : ℕ → ℕ}
  {A : ℕ → ℤ → EuclideanSpace ℂ κ} {α p : ℝ} {x : X}

theorem sourceTreePathRatio_nonneg (hw : ∀ t x, 0 ≤ weight t x) (top : τ) (j : ℕ) :
    0 ≤ g.sourceTreePathRatio tops slope precision cutoff weight level A α p x top j := by
  unfold sourceTreePathRatio sourceTreeAmount sourceTreeDenominator
  apply div_nonneg
  · exact (g.mass_nonnegative tops slope precision cutoff weight hw _ _ x).trans
      (mass_le_vertexAmount (g.mass_nonnegative tops slope precision cutoff weight hw _ _ x) _)
  · exact (g.mass_nonnegative tops slope precision cutoff weight hw _ _ x).trans
      (sourceNodeDenominator_ge_mass _ _ _ α p
        (fun c => g.mass_nonnegative tops slope precision cutoff weight hw _ c.val x))

theorem sourceTreeExit_nonneg (hw : ∀ t x, 0 ≤ weight t x) (top : τ) (j : ℕ) :
    0 ≤ g.sourceTreeExit tops slope precision cutoff weight level A α p x j top := by
  unfold sourceTreeExit
  split_ifs
  · apply div_nonneg
    · exact (g.mass_nonnegative tops slope precision cutoff weight hw _ _ x).trans
        (mass_le_vertexAmount (g.mass_nonnegative tops slope precision cutoff weight hw _ _ x) _)
    · exact g.mass_nonnegative tops slope precision cutoff weight hw _ _ x
  · exact zero_le_one

theorem sourceTreeDenominator_ge_child_amount
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (hlevel : Monotone level) (top : τ) (htop : top ∈ tops) (j : ℕ)
    (he : g.eligible cutoff (precision top) (level (j+1))) :
    g.sourceTreeAmount tops slope precision cutoff weight level A α p x (j+1)
      (g.index (level (j+1)) (slope top)) ≤
    g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j
      (g.index (level j) (slope top)) := by
  let cells := g.sourceBlockCells tops slope precision cutoff (level j) (level (j+1))
    (g.index (level j) (slope top))
  have hc : g.index (level (j+1)) (slope top) ∈ cells :=
    g.mem_sourceBlockCells_of_top tops slope precision cutoff (level j) (level (j+1))
      (g.index (level j) (slope top)) hp (hlevel (Nat.le_succ j)) top htop rfl he
  have hm := g.path_mass_antitone tops slope precision cutoff weight hp hw top x
    (hlevel (Nat.le_succ j))
  have hd := sourceNodeDenominator_ge_child
    (g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x)
    (fun c : cells => g.mass tops slope precision cutoff weight (level (j+1)) c.val x)
    (fun c : cells => A (j+1) c.val) α p
    (fun c => g.mass_nonnegative tops slope precision cutoff weight hw _ c.val x)
    ⟨g.index (level (j+1)) (slope top),hc⟩
  change _ ≤ sourceNodeDenominator _ _ _ _ _
  unfold sourceTreeAmount
  linarith

/-- The product-to-root quotient has a uniform cap for every individual
terminal top; all preceding transitions use the actual child denominator. -/
theorem sourceTree_terminal_probability_le
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hlevel : Monotone level) (M : ℝ) (hM : 1 ≤ M)
    (count : ℕ) (top : τ) (htop : top ∈ tops)
    (hterminal : ¬g.eligible cutoff (precision top) (level count))
    (hroot : M < g.sourceTreePathMass tops slope precision cutoff weight level x top 0)
    (C : ℝ)
    (hexit : g.sourceTreeExit tops slope precision cutoff weight level A α p x
      (firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x top) count M)
      top ≤ C) :
    weight top x*g.sourceTreeTail tops slope precision cutoff weight level A α p x M count 0 top/
      g.sourceTreeAmount tops slope precision cutoff weight level A α p x 0
        (g.index (level 0) (slope top)) ≤ C*weight top x := by
  let n := g.sourceTreePathMass tops slope precision cutoff weight level x top
  let stop := firstMassStop n count M
  let V := fun j => g.sourceTreeAmount tops slope precision cutoff weight level A α p x j
    (g.index (level j) (slope top))
  let D := fun j => g.sourceTreeDenominator tops slope precision cutoff weight level A α p x j
    (g.index (level j) (slope top))
  have hlast : n count ≤ M := by
    simp only [n,sourceTreePathMass,ite_eq_right hterminal]
    linarith
  have hs := firstMassStop_spec n count M hlast
  have hspos : 0 < stop := by
    by_contra hn
    have hz : stop = 0 := by omega
    have h := hs.2.1
    change n stop ≤ M at h
    rw [hz] at h
    exact (not_le_of_gt hroot) h
  have he (j : ℕ) (hj : j < stop) : g.eligible cutoff (precision top) (level j) := by
    have hn := hs.2.2 j hj
    by_contra h
    simp only [n,sourceTreePathMass,ite_eq_right h] at hn
    linarith
  have hnpos (j : ℕ) (hj : j < stop) :
      0 < g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x :=
    g.path_mass_pos tops slope precision cutoff weight hw _ top htop (he j hj) x
  have hV (j : ℕ) (hj : j ≤ stop-1) : 0 < V j :=
    vertexAmount_pos (hnpos j (by omega)) _
  have hDmass (j : ℕ) :
      g.mass tops slope precision cutoff weight (level j) (g.index (level j) (slope top)) x ≤ D j := by
    dsimp only [D,sourceTreeDenominator]
    apply sourceNodeDenominator_ge_mass
    intro c
    exact g.mass_nonnegative tops slope precision cutoff weight (fun t x => (hw t x).le)
      (level (j+1)) c.val x
  have hD (j : ℕ) (hj : j ≤ stop-1) : 0 < D j := (hnpos j (by omega)).trans_le (hDmass j)
  have hchild (j : ℕ) (hj : j < stop-1) : V (j+1) ≤ D j :=
    sourceTreeDenominator_ge_child_amount hp (fun t x => (hw t x).le) hlevel top htop j
      (he (j+1) (by omega))
  have hexit0 : 0 ≤ g.sourceTreeExit tops slope precision cutoff weight level A α p x stop top :=
    sourceTreeExit_nonneg (fun t x => (hw t x).le) top stop
  have hfinal : 1 ≤ D (stop-1) := by
    have hn := hs.2.2 (stop-1) (by omega)
    rw [show n (stop-1) = g.mass tops slope precision cutoff weight (level (stop-1))
      (g.index (level (stop-1)) (slope top)) x by
        simp only [n,sourceTreePathMass,ite_eq_left (he (stop-1) (by omega))]] at hn
    exact hM.trans (hn.le.trans (hDmass (stop-1)))
  rw [sourceTreeTail_eq_stopped M (by linarith) count top hterminal]
  have hstop : stop-1+1 = stop := by omega
  have hbound := normalized_terminal_weight_bound V D (stop-1)
    (weight top x*g.sourceTreeExit tops slope precision cutoff weight level A α p x stop top)
    C (weight top x) hV hD hchild (mul_nonneg (hw top x).le hexit0)
    ((mul_le_mul_of_nonneg_left hexit (hw top x).le).trans_eq (mul_comm _ _)) hfinal
  rw [hstop] at hbound
  simpa only [V,D,sourceTreePathRatio,mul_assoc] using hbound

end Path
end LipschitzHilbert.AngularGrid

end

end OAI

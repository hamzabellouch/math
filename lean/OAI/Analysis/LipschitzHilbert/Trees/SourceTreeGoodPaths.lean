import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeProbability
import OAI.Analysis.LipschitzHilbert.Trees.FiniteGoodPath

namespace OAI

/-! The good-path domination inequality for the original finite angular
tree, derived from its exact expansion and actual child transitions. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable Classical.decEq
variable {τ X : Type*} {κ : Type} [Fintype κ]

theorem sourceTree_good_path_domination
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (level : ℕ → ℕ) (hlevel : Monotone level)
    (A : ℕ → ℤ → EuclideanSpace ℂ κ) (α p M C : ℝ) (hM : 1 ≤ M)
    (x : X) (count : ℕ) (cell : ℤ)
    (hne : (g.cellTops tops slope precision cutoff (level 0) cell).Nonempty)
    (hroot : M < g.mass tops slope precision cutoff weight (level 0) cell x)
    (hterminal : ∀ t ∈ g.cellTops tops slope precision cutoff (level 0) cell,
      ¬g.eligible cutoff (precision t) (level count))
    (hexit : ∀ t ∈ g.cellTops tops slope precision cutoff (level 0) cell,
      g.sourceTreeExit tops slope precision cutoff weight level A α p x
        (firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x t) count M) t ≤ C)
    (bad : Finset τ) (hbadS : bad ⊆ g.cellTops tops slope precision cutoff (level 0) cell)
    (hbad : C*(∑ t ∈ bad, weight t x) ≤ 1/2) :
    g.sourceTreeAmount tops slope precision cutoff weight level A α p x 0 cell ≤
      2*C*∑ t ∈ g.cellTops tops slope precision cutoff (level 0) cell\bad,
        weight t x*∏ j ∈ Finset.range
          (firstMassStop (g.sourceTreePathMass tops slope precision cutoff weight level x t) count M),
          g.sourceTreePathRatio tops slope precision cutoff weight level A α p x t j := by
  let S := g.cellTops tops slope precision cutoff (level 0) cell
  let finish := fun t => firstMassStop
    (g.sourceTreePathMass tops slope precision cutoff weight level x t) count M
  let Q := fun t => ∏ j ∈ Finset.range (finish t),
    g.sourceTreePathRatio tops slope precision cutoff weight level A α p x t j
  let e := fun t => weight t x*
    g.sourceTreeExit tops slope precision cutoff weight level A α p x (finish t) t
  let V := g.sourceTreeAmount tops slope precision cutoff weight level A α p x 0 cell
  have hV : 0 < V := vertexAmount_pos (lt_trans (by linarith : 0 < M) hroot) _
  have htotal : ∑ t ∈ S, e t*Q t = V :=
    g.sourceTree_terminal_expansion hp hw hlevel M (by linarith) count cell hne hterminal
  have hprob : ∀ t ∈ bad, e t*Q t/V ≤ C*weight t x := by
    intro t ht
    have ht' := (g.mem_cellTops _ _ _ _ _ _ _).mp (hbadS ht)
    have hr : M < g.sourceTreePathMass tops slope precision cutoff weight level x t 0 := by
      simpa only [sourceTreePathMass,ite_eq_left ht'.2.2,ht'.2.1] using hroot
    have hb := sourceTree_terminal_probability_le (A := A) (α := α) (p := p) hp hw hlevel
      M hM count t ht'.1 (hterminal t (hbadS ht)) hr C (hexit t (hbadS ht))
    rw [sourceTreeTail_eq_stopped M (by linarith) count t (hterminal t (hbadS ht))] at hb
    simpa only [ht'.2.1,e,Q,V,finish,mul_assoc] using hb
  have he : ∀ t ∈ S, e t ≤ C*weight t x := by
    intro t ht
    exact (mul_le_mul_of_nonneg_left (hexit t ht) (hw t x).le).trans_eq (mul_comm _ _)
  have hQ : ∀ t ∈ S, 0 ≤ Q t := by
    intro t _
    exact Finset.prod_nonneg fun j _ => sourceTreePathRatio_nonneg (fun t x => (hw t x).le) t j
  exact finite_good_path_domination S bad hbadS (fun t => weight t x) e Q V C
    hV htotal hprob he hQ hbad

end LipschitzHilbert.AngularGrid

end

end OAI

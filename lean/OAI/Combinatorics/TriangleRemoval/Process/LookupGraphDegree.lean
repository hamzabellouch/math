import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEpsilon
import OAI.Combinatorics.TriangleRemoval.Process.LookupGraph

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave

open Classical in

lemma lookupGraph_degree_le {n : ℕ} (G : Graph n) (x : Fin n) :
    (Finset.univ.filter (fun z => (lookupGraph G).Adj x z)).card ≤ currentDegree G x := by
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,(Finset.mem_filter.mp hz).2.2⟩

open Classical in

lemma lookupGraph_codegree_le {n : ℕ} (G : Graph n) (x y : Fin n) :
    (Finset.univ.filter (fun z => (lookupGraph G).Adj x z ∧ (lookupGraph G).Adj y z)).card ≤
      currentCodegree G x y := by
  apply Finset.card_le_card
  intro z hz
  have hh := (Finset.mem_filter.mp hz).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,hh.1.2,hh.2.2⟩

open Classical in

lemma goodPrefix_degree_bound {n : ℕ} {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (hc : (n : ℝ)^(-c) ≤ 1)
    (hp : 0 ≤ prefixDensity n) (x : Fin n) :
    ((Finset.univ.filter (fun z => (lookupGraph G).Adj x z)).card : ℝ) ≤
      2 * (n * prefixDensity n) := by
  have h := (abs_le.mp (hGood.2.2.1 x)).2
  have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg (Nat.cast_nonneg n) hp)
  have hl : ((Finset.univ.filter (fun z => (lookupGraph G).Adj x z)).card : ℝ) ≤
      currentDegree G x := by exact_mod_cast lookupGraph_degree_le G x
  linarith

open Classical in

lemma goodPrefix_codegree_bound {n : ℕ} {G : Graph n} {c C : ℝ}
    (hGood : GoodPrefixGraph n c C G) (hc : (n : ℝ)^(-c) ≤ 1)
    (x y : Fin n) (hxy : x ≠ y) :
    ((Finset.univ.filter (fun z => (lookupGraph G).Adj x z ∧ (lookupGraph G).Adj y z)).card : ℝ) ≤
      2 * prefixD n := by
  have h := (abs_le.mp (hGood.2.2.2.1 x y hxy)).2
  have hD : 0 ≤ prefixD n := mul_nonneg (Nat.cast_nonneg n) (sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hc hD
  have hl : ((Finset.univ.filter (fun z => (lookupGraph G).Adj x z ∧ (lookupGraph G).Adj y z)).card : ℝ) ≤
      currentCodegree G x y := by exact_mod_cast lookupGraph_codegree_le G x y
  linarith

end SharpTerminalLeave

end

end OAI

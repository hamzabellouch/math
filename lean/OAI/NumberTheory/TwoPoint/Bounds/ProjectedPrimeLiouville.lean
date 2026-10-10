import OAI.NumberTheory.TwoPoint.Bounds.PrimeLiouvilleQuadratic
import OAI.NumberTheory.TwoPoint.Bounds.ProjectedLiouvilleVector

namespace OAI

/-! The exact retained-edge identity for the projected vector used by
actual block testing, including both degree cutoffs. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem projected_prime_liouville_quadratic {J : ℕ} {V : Type*}
    [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible (actualPaddingVertex Qp) L K extra h gate
    let keep := fun n => (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J
    let proj := coordinateProjection (fun i => keep (site i))
    let v := paddingTestVector Qp L site integerLiouville
    inner ℂ v ((proj * (∑ d, B d) * proj) v) =
      (2 * (L : ℂ)) * ∑ d : (j : Fin J) → P j, ∑ i, ∑ j,
        if gate (∏ k, (d k).val) i j then ∑ q ∈ Q,
          retainedLiouvilleEdge Q u (eligible (∏ k, (d k).val)) (actualPaddingVertex Qp)
            (centeredTuple (∏ k, (d k).val).primeFactors) L K (extra (∏ k, (d k).val))
            (fun n => keep n ∧ actualPaddingDegreeCut Qp L n)
            h (∏ k, (d k).val) q (site i) (site j)
        else 0 := by
  dsimp only
  let keep := fun n => (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J
  let proj := coordinateProjection (fun i => keep (site i))
  let v := paddingTestVector Qp L site integerLiouville
  let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
    site Q u eligible (actualPaddingVertex Qp) L K extra h gate
  have hq := prime_graph_liouville_quadratic P hprime hdisjoint site Q u eligible
    (actualPaddingVertex Qp) L K extra (fun n => keep n ∧ actualPaddingDegreeCut Qp L n)
    h gate hgate (actualPaddingVertex_ne_zero Qp)
  dsimp only at hq
  rw [← projectedLiouvilleVector_eq Qp L site keep] at hq
  have he := (coordinateProjection_selfAdjoint (fun i => keep (site i))).isSymmetric
    v ((∑ d, B d) (proj v))
  exact he.symm.trans hq

end TwoPointCorrelations

end OAI

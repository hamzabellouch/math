import OAI.NumberTheory.TwoPoint.Bounds.GraphMatrixCompression
import OAI.NumberTheory.TwoPoint.Bounds.LiouvilleQuadraticIdentity

namespace OAI

/-! The full tuple graph tests to the literal sum of retained directed
Liouville edges, with the original numerical tuple and padding divisor. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem prime_graph_liouville_quadratic {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (keep : ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hg : ∀ z, g z ≠ 0) :
    let v := WithLp.toLp 2 (fun i => retainedLiouvilleScalar g keep (site i))
    inner ℂ v ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val)
      (fun _ _ => 0) site Q u eligible g L K extra h gate d) v) =
      (2 * (L : ℂ)) * ∑ d : (j : Fin J) → P j, ∑ i, ∑ j,
        if gate (∏ k, (d k).val) i j then ∑ q ∈ Q,
          retainedLiouvilleEdge Q u (eligible (∏ k, (d k).val)) g
            (centeredTuple (∏ k, (d k).val).primeFactors) L K
            (extra (∏ k, (d k).val)) keep h (∏ k, (d k).val) q (site i) (site j)
        else 0 := by
  dsimp only
  let v : EuclideanSpace ℂ V := WithLp.toLp 2 (fun i => retainedLiouvilleScalar g keep (site i))
  have hd (d : (j : Fin J) → P j) :
      inner ℂ v (primeFamilyGraphOperator (fun j (p : P j) => p.val)
        (fun _ _ => 0) site Q u eligible g L K extra h gate d v) =
        (2 * (L : ℂ)) * ∑ i, ∑ j,
          if gate (∏ k, (d k).val) i j then ∑ q ∈ Q,
            retainedLiouvilleEdge Q u (eligible (∏ k, (d k).val)) g
              (centeredTuple (∏ k, (d k).val).primeFactors) L K
              (extra (∏ k, (d k).val)) keep h (∏ k, (d k).val) q (site i) (site j)
          else 0 := by
    have hc : familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d =
        centeredTuple (∏ j, (d j).val).primeFactors := by
      funext n
      exact familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
        d (selectedPrimeValues_injective d hdisjoint) n
    unfold primeFamilyGraphOperator
    rw [hc]
    exact maskedLiouville_quadratic site Q u _ g _ L K _ keep h _ _ (hgate _) hg
  change inner ℂ v ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val)
    (fun _ _ => 0) site Q u eligible g L K extra h gate d) v) = _
  rw [_root_.sum_apply, inner_sum]
  simp_rw [hd]
  rw [mul_sum]

end TwoPointCorrelations

end OAI

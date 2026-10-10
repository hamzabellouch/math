import OAI.NumberTheory.TwoPoint.Bounds.GraphTesting
import OAI.NumberTheory.TwoPoint.Walks.BlockTesting

namespace OAI

/-! The deterministic bound for the manuscript's actual test vectors,
with both degree cutoffs and the square-root padding weight. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma paddingTestVector_apply_norm_le {V : Type*} (Q : Finset ℕ) (L : ℝ)
    (site : V → ℤ) (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (i : V) :
    ‖paddingTestVector Q L site f i‖ ≤ actualPaddingVertex Q (site i) := by
  by_cases hi : actualPaddingDegreeCut Q L (site i)
  · simp only [paddingTestVector, WithLp.ofLp_toLp, ite_eq_left hi, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (actualPaddingVertex_pos Q _)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf (site i))
      (actualPaddingVertex_pos Q _).le
  · simpa [paddingTestVector, hi] using (actualPaddingVertex_pos Q (site i)).le

lemma projected_paddingTestVector_support {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset ℕ) (L : ℝ) (site : V → ℤ) (f : ℤ → ℂ) (keep : V → Prop)
    (i : V) (hi : coordinateProjection keep (paddingTestVector Q L site f) i ≠ 0) :
    keep i ∧ actualPaddingDegreeCut Q L (site i) := by
  constructor
  · by_contra hk
    apply hi
    simp only [coordinateProjection_apply, ite_eq_right hk]
  · by_contra hq
    apply hi
    simp [coordinateProjection_apply, paddingTestVector, hq]

lemma paddingVertex_cut_bound (Q : Finset ℕ) (L : ℝ) (n : ℤ)
    (hn : actualPaddingDegreeCut Q L n) :
    actualPaddingVertex Q n ^ 2 ≤ (5 : ℝ) ^ (400 * Real.log L) := by
  rw [actualPaddingVertex_sq, actualPaddingWeight, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn

theorem projected_padding_graph_test {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ) (gate : ℕ → V → V → Prop)
    (hL : 0 < L) (hK : 0 ≤ K) (hW : 0 ≤ W) (hu : ∀ q ∈ Q, 0 ≤ u q)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (f : ℤ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible (actualPaddingVertex Qp) L K extra h gate
    let proj := coordinateProjection (fun i : V =>
      (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J)
    let v := paddingTestVector Qp L site f
    ‖inner ℂ v ((proj * (∑ d, B d) * proj) v)‖ ≤
      Fintype.card V * (2 * K * (8 * W) ^ J) * (5 : ℝ) ^ (400 * Real.log L) := by
  dsimp only
  let keep := fun i : V => (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J
  let proj := coordinateProjection keep
  let v := paddingTestVector Qp L site f
  have hcoord (i : V) : ‖proj v i‖ ≤ actualPaddingVertex Qp (site i) := by
    dsimp only [proj]
    rw [coordinateProjection_apply]
    split_ifs
    · exact paddingTestVector_apply_norm_le Qp L site f hf i
    · simpa only [norm_zero] using (actualPaddingVertex_pos Qp (site i)).le
  have hsupp (i : V) (hi : proj v i ≠ 0) :
      keep i ∧ actualPaddingDegreeCut Qp L (site i) :=
    projected_paddingTestVector_support Qp L site f keep i hi
  have hb := prime_graph_test_deterministic P hprime hdisjoint site hinj Q u eligible
    (actualPaddingVertex Qp) L K W extra h gate hL hK hW hu
    (actualPaddingVertex_pos Qp) hV (proj v) hcoord (fun i hi => (hsupp i hi).1)
    ((5 : ℝ) ^ (400 * Real.log L)) (Real.rpow_nonneg (by norm_num) _)
    (fun i hi => paddingVertex_cut_bound Qp L (site i) (hsupp i hi).2)
  have he := (coordinateProjection_selfAdjoint keep).isSymmetric v
    ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible (actualPaddingVertex Qp) L K extra h gate d) (proj v))
  change inner ℂ (proj v) _ = inner ℂ v (proj _) at he
  exact (le_of_eq (congrArg norm he.symm)).trans hb

end TwoPointCorrelations

end OAI

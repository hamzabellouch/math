import OAI.NumberTheory.TwoPoint.Walks.RetainedBlockIdentity
import OAI.NumberTheory.TwoPoint.Bounds.GraphTesting
import OAI.NumberTheory.TwoPoint.Bounds.ProjectedGraphTesting

namespace OAI

/-! The one-orientation row majorant for the actual retained correlation.
The retained cutoffs supply the degree bound and the truncated padding weight. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma retainedLiouvilleEdge_norm_le (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop)
    (h d q : ℕ) (n m : ℤ) (hL : 0 < L) (hu : 0 ≤ u q) (hg : g n ≠ 0) :
    ‖retainedLiouvilleEdge Q u eligible g center L K extra keep h d q n m‖ ≤
      |center n| * retainedPaddingAtom Q u eligible g L K extra n q * ((g n) ^ 2 / L) := by
  unfold retainedLiouvilleEdge
  split_ifs with he
  · have hk : eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n :=
      ⟨he.2.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2.1⟩
    rw [retainedPaddingAtom, ite_eq_left hk]
    calc
      _ = |u q * center n| * ‖integerLiouville n‖ * ‖integerLiouville m‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |u q * center n| * 1 * 1 := by
        gcongr <;> exact integerLiouville_norm_le_one _
      _ = _ := by
        rw [abs_mul, abs_of_nonneg hu]
        field_simp
  · simpa only [norm_zero] using mul_nonneg
      (mul_nonneg (abs_nonneg _) (retainedPaddingAtom_nonneg Q u eligible g L K extra n q hL.le hu))
      (div_nonneg (sq_nonneg _) hL.le)

theorem retainedPrimeEdge_row_bound {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop)
    (hL : 0 < L) (hK : 0 ≤ K) (hW : 0 ≤ W) (hu : ∀ q ∈ Q, 0 ≤ u q)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W) (n : ℤ) :
    (∑ e : ((j : Fin J) → P j) × Q,
      ‖retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
        (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ))‖) ≤
      K / L * (5 : ℝ) ^ (400 * Real.log L) * (8 * W) ^ J := by
  let good := (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J ∧
    actualPaddingDegreeCut Qp L n
  by_cases hn : good
  · have hq (d : (j : Fin J) → P j) (q : Q) :
        ‖retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep (d, q) n
          (n + (h * q.val * ∏ j, (d j).val : ℕ))‖ ≤
        |centeredTuple (∏ j, (d j).val).primeFactors n| *
          retainedPaddingAtom Q u (eligible (∏ j, (d j).val)) (actualPaddingVertex Qp)
            L K (extra (∏ j, (d j).val)) n q.val *
          ((actualPaddingVertex Qp n) ^ 2 / L) := by
      unfold retainedPrimeEdge
      split_ifs
      · exact retainedLiouvilleEdge_norm_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL
          (hu q.val q.property) (actualPaddingVertex_ne_zero Qp n)
      · simpa only [norm_zero] using mul_nonneg
          (mul_nonneg (abs_nonneg _) (retainedPaddingAtom_nonneg _ _ _ _ _ _ _ _ _ hL.le
            (hu q.val q.property))) (div_nonneg (sq_nonneg _) hL.le)
    have hc : (∑ d : (j : Fin J) → P j,
        |centeredTuple (∏ j, (d j).val).primeFactors n|) ≤ (8 * W) ^ J := by
      have hc := sum_familyCenter_abs_le P hprime hdisjoint n W hV hn.1
      simpa only [familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
        _ (selectedPrimeValues_injective _ hdisjoint), familyTuple] using hc
    rw [Fintype.sum_prod_type]
    calc
      _ ≤ ∑ d : (j : Fin J) → P j,
          |centeredTuple (∏ j, (d j).val).primeFactors n| * K *
            ((actualPaddingVertex Qp n) ^ 2 / L) := by
        apply sum_le_sum
        intro d _
        calc
          _ ≤ ∑ q : Q, |centeredTuple (∏ j, (d j).val).primeFactors n| *
              retainedPaddingAtom Q u (eligible (∏ j, (d j).val)) (actualPaddingVertex Qp)
                L K (extra (∏ j, (d j).val)) n q.val *
              ((actualPaddingVertex Qp n) ^ 2 / L) := sum_le_sum (fun q _ => hq d q)
          _ = |centeredTuple (∏ j, (d j).val).primeFactors n| *
              (∑ q ∈ Q, retainedPaddingAtom Q u (eligible (∏ j, (d j).val)) (actualPaddingVertex Qp)
                L K (extra (∏ j, (d j).val)) n q) * ((actualPaddingVertex Qp n) ^ 2 / L) := by
            rw [← sum_mul, ← mul_sum, sum_coe_sort]
          _ ≤ _ := by
            gcongr
            exact retainedPaddingAtom_sum_le _ _ _ _ _ _ _ _ hL hK
      _ = K / L * (actualPaddingVertex Qp n) ^ 2 *
          (∑ d : (j : Fin J) → P j, |centeredTuple (∏ j, (d j).val).primeFactors n|) := by
        simp only [← sum_mul]
        ring
      _ ≤ _ := by
        gcongr
        · exact paddingVertex_cut_bound Qp L n hn.2
  · have hz (e : ((j : Fin J) → P j) × Q) :
        retainedPrimeEdge P Q Qp u eligible L K W extra h gate keep e n
          (n + (h * e.2.val * ∏ j, (e.1 j).val : ℕ)) = 0 := by
      unfold retainedPrimeEdge retainedLiouvilleEdge
      split_ifs with he he'
      · exact (hn he'.1).elim
      · rfl
      · rfl
    simp only [hz, norm_zero, sum_const_zero]
    positivity

end TwoPointCorrelations

end OAI

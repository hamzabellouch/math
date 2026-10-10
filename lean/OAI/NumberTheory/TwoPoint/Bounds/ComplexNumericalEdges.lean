import OAI.NumberTheory.TwoPoint.Bounds.ComplexPrefixBound
import OAI.NumberTheory.TwoPoint.Walks.RetainedDeletionBridge

namespace OAI

/-! Transfer the existing positive deletion costs to arbitrary complex factors.
Liouville's unit values serve only as an exact algebraic change of test functions. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def liouvilleUntwist (F G : ℤ → ℂ) (n m : ℤ) : ℂ :=
  (F n * integerLiouville n) * (G m * integerLiouville m)

lemma liouvilleUntwist_norm_le (F G : ℤ → ℂ)
    (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1) (n m : ℤ) :
    ‖liouvilleUntwist F G n m‖ ≤ 1 := by
  unfold liouvilleUntwist
  simp only [norm_mul]
  have ha := mul_le_mul (hF n) (integerLiouville_norm_le_one n)
    (norm_nonneg (integerLiouville n)) (by norm_num : (0 : ℝ) ≤ 1)
  have hb := mul_le_mul (hG m) (integerLiouville_norm_le_one m)
    (norm_nonneg (integerLiouville m)) (by norm_num : (0 : ℝ) ≤ 1)
  have hab := mul_le_mul ha hb
    (mul_nonneg (norm_nonneg (G m)) (norm_nonneg (integerLiouville m)))
    (by norm_num : (0 : ℝ) ≤ 1 * 1)
  simpa only [one_mul] using hab

lemma liouvilleUntwist_cancel (F G : ℤ → ℂ) (n m : ℤ) (hn : 0 < n) (hm : 0 < m)
    (z : ℂ) : liouvilleUntwist F G n m * (z * integerLiouville n * integerLiouville m) =
      z * F n * G m := by
  have hn0 : n.toNat ≠ 0 := by omega
  have hm0 : m.toNat ≠ 0 := by omega
  have hn2 : integerLiouville n ^ 2 = 1 := liouville_sq hn0
  have hm2 : integerLiouville m ^ 2 = 1 := liouville_sq hm0
  calc
    _ = z * F n * G m * integerLiouville n ^ 2 * integerLiouville m ^ 2 := by
      unfold liouvilleUntwist
      ring
    _ = _ := by rw [hn2, hm2, mul_one, mul_one]

lemma retainedComplexPrimeEdge_eq_untwist {J : ℕ} (P : Fin J → Finset ℕ)
    (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (keep : ℤ → Prop) (F G : ℤ → ℂ)
    (e : ((j : Fin J) → P j) × Q) (n m : ℤ) (hn : 0 < n) (hm : 0 < m) (hL : L ≠ 0) :
    retainedComplexPrimeEdge P Q Qp u eligible L K W extra h gate keep F G e n m / (L : ℂ) =
      liouvilleUntwist F G n m * retainedNumericalEdge P Q Qp u eligible L K W extra h
        gate keep (∏ j, (e.1 j).val) e.2.val n m := by
  unfold retainedComplexPrimeEdge retainedNumericalEdge retainedLiouvilleEdge retainedRealEdge
  split_ifs
  · rw [liouvilleUntwist_cancel F G n m hn hm]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hL]
  all_goals simp

lemma uncutNumericalEdge_untwist (R : Finset ℕ) (eligible : ℕ → ℕ → Prop)
    (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop) (F G : ℤ → ℂ)
    (d q : ℕ) (n m : ℤ) (hn : 0 < n) (hm : 0 < m) :
    liouvilleUntwist F G n m * uncutNumericalEdge R eligible h gate d q n m =
      if gate d n m ∧ q ∈ R ∧ eligible d q ∧ (q : ℤ) ∣ n ∧
        m = n + (h * q * d : ℕ) then
        (actualPaddingCoefficient q * centeredTuple d.primeFactors n : ℝ) * F n * G m
      else 0 := by
  unfold uncutNumericalEdge
  split_ifs
  · exact liouvilleUntwist_cancel F G n m hn hm _
  · simp

lemma complex_uncut_sub_retained_edge_le {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (d q : ℕ) (n : ℤ)
    (hsub : ∀ r ∈ R, eligible j d r → actualPaddingBin η (c d) j r)
    (hd : d.primeFactors.card = J) (F G : ℤ → ℂ)
    (hF : ∀ n, ‖F n‖ ≤ 1) (hG : ∀ n, ‖G n‖ ≤ 1) :
    let m := n + (h * q * d : ℕ)
    ‖liouvilleUntwist F G n m * uncutNumericalEdge R (eligible j) h gate d q n m -
      liouvilleUntwist F G n m * retainedNumericalEdge P R Q actualPaddingCoefficient
        (eligible j) L K W (fun _ => actualPaddingDegreeCut Q L) h gate
        (fun z => ¬bad j z) d q n m‖ ≤
      positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n +
      positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q m := by
  dsimp only
  rw [← mul_sub, norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) (liouvilleUntwist_norm_le F G hF hG n _)).trans
  exact uncut_sub_retained_edge_le P R Q η c L K W eligible h gate bad j d q n hsub hd

end TwoPointCorrelations

end OAI

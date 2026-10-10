import OAI.NumberTheory.TwoPoint.Walks.RetainedNumericalPrefix
import OAI.NumberTheory.TwoPoint.Bounds.SourceDeletionTerms
import OAI.NumberTheory.TwoPoint.Bounds.DivisorEndpointSymmetry

namespace OAI

/-! The actual complex correlation lost at either endpoint is dominated
by the positive deletion costs already estimated on integer intervals. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma integerEdgeKeep_of_larger_eligibility (R : Finset ℕ) (u : ℕ → ℝ)
    (small large : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop)
    (hu : ∀ q ∈ R, 0 ≤ u q) (hsub : ∀ q ∈ R, small q → large q) (n : ℤ)
    (hk : integerEdgeKeep R u large g L K extra n) :
    integerEdgeKeep R u small g L K extra n := by
  refine ⟨?_, hk.2⟩
  apply le_trans _ hk.1
  unfold paddingDensity
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply sum_le_sum
  intro q hq
  by_cases hs : small q ∧ (q : ℤ) ∣ n
  · have hl : large q ∧ (q : ℤ) ∣ n := ⟨hsub q hq hs.1, hs.2⟩
    rw [ite_eq_left hs, ite_eq_left hl]
  · simp only [hs, ite_false]
    split_ifs <;> first | exact hu q hq | exact le_rfl

lemma liouville_edge_norm_le_positive (d q : ℕ) (n m : ℤ) :
    ‖(actualPaddingCoefficient q * centeredTuple d.primeFactors n : ℝ) *
      integerLiouville n * integerLiouville m‖ ≤
      actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n := by
  calc
    _ = |actualPaddingCoefficient q * centeredTuple d.primeFactors n| *
        ‖integerLiouville n‖ * ‖integerLiouville m‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |actualPaddingCoefficient q * centeredTuple d.primeFactors n| * 1 * 1 := by
      gcongr <;> exact integerLiouville_norm_le_one _
    _ ≤ _ := by
      rw [mul_one, mul_one, abs_mul, abs_of_nonneg (actualPaddingCoefficient_nonneg q)]
      exact mul_le_mul_of_nonneg_left (abs_centeredTuple_le_positivePrimeWeight _ _)
        (actualPaddingCoefficient_nonneg q)

noncomputable def uncutNumericalEdge (R : Finset ℕ) (eligible : ℕ → ℕ → Prop)
    (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop) (d q : ℕ) (n m : ℤ) : ℂ :=
  if gate d n m ∧ q ∈ R ∧ eligible d q ∧ (q : ℤ) ∣ n ∧
      m = n + (h * q * d : ℕ) then
    (actualPaddingCoefficient q * centeredTuple d.primeFactors n : ℝ) *
      integerLiouville n * integerLiouville m
  else 0

lemma norm_sub_optional_le_two_costs (z retained : ℂ) (B : ℝ) (gn gm : Prop)
    (hB : ‖z‖ ≤ B) (hret : retained = z ∨ retained = 0)
    (hgood : gn → gm → retained = z) :
    ‖z - retained‖ ≤ (if gn then 0 else B) + (if gm then 0 else B) := by
  have hB0 := (norm_nonneg z).trans hB
  by_cases hn : gn <;> by_cases hm : gm
  · simp only [hn, hm, ite_true, hgood hn hm, sub_self, norm_zero, add_zero, le_refl]
  all_goals
    rcases hret with rfl | rfl <;> simp only [hn, hm, ite_true, ite_false,
      sub_self, sub_zero, norm_zero, zero_add, add_zero] <;> linarith

lemma retainedNumericalEdge_optional {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (eligible : ℕ → ℕ → Prop) (L K W : ℝ) (h : ℕ)
    (gate : ℕ → ℤ → ℤ → Prop) (bad : ℤ → Prop) (d q : ℕ) (n m : ℤ) :
    retainedNumericalEdge P R Q actualPaddingCoefficient eligible L K W
      (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad z) d q n m =
        uncutNumericalEdge R eligible h gate d q n m ∨
    retainedNumericalEdge P R Q actualPaddingCoefficient eligible L K W
      (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad z) d q n m = 0 := by
  unfold retainedNumericalEdge retainedLiouvilleEdge uncutNumericalEdge
  split_ifs <;> simp_all

lemma retainedNumericalEdge_eq_uncut_of_good {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → Prop) (j : ℤ) (d q : ℕ) (n m : ℤ)
    (hsub : ∀ r ∈ R, eligible d r → actualPaddingBin η (c d) j r)
    (hn : integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∧
      (actualPaddingDegree (primeTuplePool P) n : ℝ) ≤ 6 * W * J ∧ ¬bad n)
    (hm : integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) m ∧
      (actualPaddingDegree (primeTuplePool P) m : ℝ) ≤ 6 * W * J ∧ ¬bad m) :
    retainedNumericalEdge P R Q actualPaddingCoefficient eligible L K W
      (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad z) d q n m =
        uncutNumericalEdge R eligible h gate d q n m := by
  have hkn := integerEdgeKeep_of_larger_eligibility R actualPaddingCoefficient
    (eligible d) (actualPaddingBin η (c d) j) (actualPaddingVertex Q) L K
    (actualPaddingDegreeCut Q L) (fun r _ => actualPaddingCoefficient_nonneg r) hsub n hn.1
  have hkm := integerEdgeKeep_of_larger_eligibility R actualPaddingCoefficient
    (eligible d) (actualPaddingBin η (c d) j) (actualPaddingVertex Q) L K
    (actualPaddingDegreeCut Q L) (fun r _ => actualPaddingCoefficient_nonneg r) hsub m hm.1
  have hdn : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J := hn.2.1
  have hdm : (actualPaddingDegree (univ.biUnion P) m : ℝ) ≤ 6 * W * J := hm.2.1
  by_cases hg : gate d n m
  · simp only [retainedNumericalEdge, retainedLiouvilleEdge, uncutNumericalEdge,
      hn.2.2, hm.2.2, hkn, hkm, hdn, hdm, hn.1.2, hm.1.2, hg,
      and_true, true_and, not_false_eq_true, ite_true]
    congr 1
    apply propext
    tauto
  · simp only [retainedNumericalEdge, uncutNumericalEdge, hg, false_and, ite_false]

lemma positiveDeletionAtom_eq_good_cost {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (j : ℤ) (d q : ℕ) (n : ℤ) (he : eligible j d q) (hq : (q : ℤ) ∣ n)
    (hd : d.primeFactors.card = J) :
    positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n =
      if integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
          (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∧
        (actualPaddingDegree (primeTuplePool P) n : ℝ) ≤ 6 * W * J ∧ ¬bad j n
      then 0 else actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n := by
  have hf : (¬integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
      (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∨
      6 * W * J < (actualPaddingDegree (primeTuplePool P) n : ℝ) ∨ bad j n) ↔
      ¬(integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) n ∧
        (actualPaddingDegree (primeTuplePool P) n : ℝ) ≤ 6 * W * J ∧ ¬bad j n) := by
    simp only [not_and_or, not_le, not_not]
  simp only [positiveDeletionAtom, he, hq, hd, ite_true, true_and, hf]
  split_ifs <;> simp_all

lemma positiveDeletionAtom_nonneg (P Q R : Finset ℕ) (η : ℝ) (c : ℕ → ℝ)
    (L K W : ℝ) (eligible : ℤ → ℕ → ℕ → Prop) (bad : ℤ → ℤ → Prop)
    (j : ℤ) (d q : ℕ) (n : ℤ) :
    0 ≤ positiveDeletionAtom P Q R η c L K W eligible bad j d q n := by
  unfold positiveDeletionAtom
  split_ifs <;> first
    | exact le_rfl
    | exact mul_nonneg (mul_nonneg (actualPaddingCoefficient_nonneg q)
        (positivePrimeWeight_nonneg _ _)) (by norm_num)

/-- On a numerical edge, each discarded correlation is paid by one of
its two actual endpoint costs. No averaging or periodicity premise is added. -/
theorem uncut_sub_retained_edge_le {J : ℕ} (P : Fin J → Finset ℕ)
    (R Q : Finset ℕ) (η : ℝ) (c : ℕ → ℝ) (L K W : ℝ)
    (eligible : ℤ → ℕ → ℕ → Prop) (h : ℕ) (gate : ℕ → ℤ → ℤ → Prop)
    (bad : ℤ → ℤ → Prop) (j : ℤ) (d q : ℕ) (n : ℤ)
    (hsub : ∀ r ∈ R, eligible j d r → actualPaddingBin η (c d) j r)
    (hd : d.primeFactors.card = J) :
    ‖uncutNumericalEdge R (eligible j) h gate d q n (n + (h * q * d : ℕ)) -
      retainedNumericalEdge P R Q actualPaddingCoefficient (eligible j) L K W
        (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z)
        d q n (n + (h * q * d : ℕ))‖ ≤
      positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q n +
      positiveDeletionAtom (primeTuplePool P) Q R η c L K W eligible bad j d q
        (n + (h * q * d : ℕ)) := by
  let m := n + (h * q * d : ℕ)
  let z := uncutNumericalEdge R (eligible j) h gate d q n m
  let r := retainedNumericalEdge P R Q actualPaddingCoefficient (eligible j) L K W
    (fun _ => actualPaddingDegreeCut Q L) h gate (fun z => ¬bad j z) d q n m
  have hop : r = z ∨ r = 0 := retainedNumericalEdge_optional P R Q (eligible j)
    L K W h gate (bad j) d q n m
  by_cases ha : gate d n m ∧ q ∈ R ∧ eligible j d q ∧ (q : ℤ) ∣ n
  · have hmdiv : (q : ℤ) ∣ m := by
      dsimp [m]
      apply dvd_add ha.2.2.2
      exact_mod_cast (show q ∣ h * q * d from dvd_mul_of_dvd_left (dvd_mul_left q h) d)
    have hw : positivePrimeWeight d.primeFactors m = positivePrimeWeight d.primeFactors n := by
      have he : (h * q * d : ℕ) = (d : ℤ) * ((h * q : ℕ) : ℤ) := by push_cast; ring
      change positivePrimeWeight d.primeFactors (n + (h * q * d : ℕ)) = _
      rw [he, positivePrimeWeight_add_multiple]
    let good := fun t : ℤ =>
      integerEdgeKeep R actualPaddingCoefficient (actualPaddingBin η (c d) j)
        (actualPaddingVertex Q) L K (actualPaddingDegreeCut Q L) t ∧
      (actualPaddingDegree (primeTuplePool P) t : ℝ) ≤ 6 * W * J ∧ ¬bad j t
    have hz : ‖z‖ ≤ actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n := by
      dsimp [z, uncutNumericalEdge]
      rw [ite_eq_left ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2, rfl⟩]
      exact liouville_edge_norm_le_positive d q n m
    have hg : good n → good m → r = z :=
      fun hn hm => retainedNumericalEdge_eq_uncut_of_good P R Q η c L K W
        (eligible j) h gate (bad j) j d q n m hsub hn hm
    have hb := norm_sub_optional_le_two_costs z r
      (actualPaddingCoefficient q * positivePrimeWeight d.primeFactors n)
      (good n) (good m) hz hop hg
    have hcn := positiveDeletionAtom_eq_good_cost P R Q η c L K W eligible bad j d q n
      ha.2.2.1 ha.2.2.2 hd
    have hcm := positiveDeletionAtom_eq_good_cost P R Q η c L K W eligible bad j d q m
      ha.2.2.1 hmdiv hd
    change ‖z - r‖ ≤ _
    rw [hcn, hcm, hw]
    by_cases hn : good n <;> by_cases hm : good m
    all_goals
      dsimp only [good] at hn hm hb
      simpa only [hn, hm, ite_true, ite_false] using hb
  · have hz : z = 0 := by
      dsimp [z, uncutNumericalEdge]
      exact ite_eq_right (fun hcond => ha ⟨hcond.1, hcond.2.1, hcond.2.2.1, hcond.2.2.2.1⟩)
    have hr : r = 0 := hop.elim (fun he => he.trans hz) id
    change ‖z - r‖ ≤ _
    rw [hz, hr, sub_self, norm_zero]
    exact add_nonneg
      (positiveDeletionAtom_nonneg (primeTuplePool P) Q R η c L K W eligible bad j d q n)
      (positiveDeletionAtom_nonneg (primeTuplePool P) Q R η c L K W eligible bad j d q m)

end TwoPointCorrelations

end OAI

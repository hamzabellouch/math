import OAI.NumberTheory.TotientAsymptotic.PPTFactorLabels
import OAI.NumberTheory.TotientAsymptotic.PPTPrefixEquation

namespace OAI

/-!
Actual residual data after choosing the terminal prefix and canceling
matching coordinates. This keeps the candidate integer, both finite
factor labels, and the exact shifted-product equation together.
-/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def pptTailIndices (k J : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i : Fin k => J ≤ i.val)

def pptTailList {k : ℕ} (p : Fin k → ℕ) (J : ℕ) :
    Fin (pptTailIndices k J).card → ℕ :=
  p ∘ (pptTailIndices k J).orderEmbOfFin rfl

lemma ppt_tail_list_product {k : ℕ} (p : Fin k → ℕ) (J : ℕ) :
    (∏ i, pptTailList p J i) = pptPrimeTailProduct p J := by
  classical
  let e := (pptTailIndices k J).orderEmbOfFin rfl
  have he : Finset.univ.image e = pptTailIndices k J :=
    (pptTailIndices k J).image_orderEmbOfFin_univ rfl
  calc
    _ = ∏ i ∈ Finset.univ.image e, p i := by
      rw [Finset.prod_image]
      · rfl
      · exact fun i _ j _ hij => e.injective hij
    _ = _ := by rw [he]; rfl

lemma ppt_tail_list_mem {k : ℕ} (p : Fin k → ℕ) (J : ℕ)
    (i : Fin (pptTailIndices k J).card) :
    ∃ j : Fin k, J ≤ j.val ∧ pptTailList p J i = p j := by
  let e := (pptTailIndices k J).orderEmbOfFin rfl
  exact ⟨e i, (Finset.mem_filter.mp
    ((pptTailIndices k J).orderEmbOfFin_mem rfl i)).2, rfl⟩

/-- The residual pair and both factor labels are built from the actual
lists. The first prime survives cancellation, and the target size is
divided by the totient of precisely the canceled product. -/
theorem ppt_actual_truncated_block {k l J d n E N : ℕ}
    (p : Fin k → ℕ) (q : Fin l → ℕ) (hJp : J ≤ k) (hJq : J ≤ l)
    (hJ : 0 < J) {W V z K : ℝ}
    (hp : ∀ i, IsNormalPrime W (p i)) (hq : ∀ i, IsNormalPrime W (q i))
    (hpa : StrictAnti p) (hqa : StrictAnti q)
    (hp3 : ∀ i, 3 ≤ p i) (hq3 : ∀ i, 3 ≤ q i)
    (hfirst : p ⟨0,hJ.trans_le hJp⟩ ≠ q ⟨0,hJ.trans_le hJq⟩)
    (hn : n = ∏ i, p i)
    (heq : d*shiftedProduct p = E*shiftedProduct q)
    (hE : 0 < E) (hV : 1 ≤ V) (hEV : (largestPrimeFactor E : ℝ) ≤ V)
    (hptail : ∀ i : Fin k, J ≤ i.val → (largestPrimeFactor (p i-1) : ℝ) ≤ V)
    (hqtail : ∀ i : Fin l, J ≤ i.val → (largestPrimeFactor (q i-1) : ℝ) ≤ V)
    (hsize : ((d*n.totient : ℕ) : ℝ) ≤ z)
    (hsq : SquarefreeAbove (d*n.totient) K)
    (hpN : ∀ i, p i ≤ N) :
    ∃ (b h s c a : ℕ) (t : ShiftedPair b) (tail : Fin h → ℕ),
      0 < b ∧ b ≤ J ∧ h ≤ k ∧ s ≤ J ∧
      0 < c ∧ 0 < a ∧ n = c*a*∏ i, t.left i ∧
      c ∈ pptPrimeProductFamily N s ∧ a ∈ pptPrimeProductFamily N h ∧
      a = ∏ i, tail i ∧ Function.Injective tail ∧
      (∀ i, IsNormalPrime W (tail i) ∧ (largestPrimeFactor (tail i-1) : ℝ) ≤ V) ∧
      (∀ i, ∃ j : Fin k, J ≤ j.val ∧ tail i = p j) ∧
      (∀ i, IsNormalPrime W (t.left i) ∧ IsNormalPrime W (t.right i) ∧
        3 ≤ t.left i ∧ 3 ≤ t.right i ∧ t.left i ≠ t.right i) ∧
      StrictAnti t.left ∧ StrictAnti t.right ∧
      0 < t.remainder ∧ (largestPrimeFactor t.remainder : ℝ) ≤ V ∧
      (d*a.totient)*shiftedProduct t.left = t.remainder*shiftedProduct t.right ∧
      (((d*a.totient)*shiftedProduct t.left : ℕ) : ℝ) ≤ z/c.totient ∧
      SquarefreeAbove ((d*a.totient)*shiftedProduct t.left) K ∧
      c = pptCanceledPrimeProduct (pptPrimePrefix p hJp) (pptPrimePrefix q hJq) ∧
      (∃ e : Fin b ↪o Fin J, ∀ i,
        t.left i = p ((e i).castLE hJp) ∧ t.right i = q ((e i).castLE hJq)) ∧
      (∃ ι : Fin b ↪o Fin k, ∀ i, t.left i = p (ι i)) ∧
      ∃ hb : 0 < b, t.left ⟨0,hb⟩ = p ⟨0,hJ.trans_le hJp⟩ := by
  classical
  let P := pptPrimePrefix p hJp
  let Q := pptPrimePrefix q hJq
  let c := pptCanceledPrimeProduct P Q
  let a := pptPrimeTailProduct p J
  let R := pptRightLowFactor q E J
  let b := (pptUnequalCoordinates P Q).card
  let s := (pptEqualCoordinates P Q).card
  let h := (pptTailIndices k J).card
  let t : ShiftedPair b := pptCanceledPair P Q R
  have hP (i : Fin J) : IsNormalPrime W (P i) := hp _
  have hQ (i : Fin J) : IsNormalPrime W (Q i) := hq _
  have hPa : StrictAnti P := ppt_prime_prefix_strictAnti p hJp hpa
  have hQa : StrictAnti Q := ppt_prime_prefix_strictAnti q hJq hqa
  have hPQ : P ⟨0,hJ⟩ ≠ Q ⟨0,hJ⟩ := hfirst
  obtain ⟨hb, hzero⟩ := ppt_coordinate_first_survives hJ P Q hPQ
  have hprefixeq : (d*a.totient)*shiftedProduct P = R*shiftedProduct Q :=
    ppt_equal_prefix_equation p q hJp hJq (fun i => (hp i).1) hpa.injective heq
  have hprefixvalue : (d*a.totient)*shiftedProduct P = d*n.totient := by
    rw [hn, ppt_totient_primeProduct p (fun i => (hp i).1) hpa.injective]
    dsimp only [a]
    rw [ppt_prime_tail_totient p (fun i => (hp i).1) hpa.injective]
    have hh := ppt_shifted_prefix_tail_split p hJp
    dsimp only [P]
    rw [mul_assoc, hh]
  have hprefixsize : (((d*a.totient)*shiftedProduct P : ℕ) : ℝ) ≤ z := by
    rw [hprefixvalue]
    exact hsize
  have hshiftdiv : shiftedProduct t.left ∣ shiftedProduct P := by
    rw [← ppt_canceled_totient_split P Q (fun i => (hP i).1) hPa.injective]
    exact dvd_mul_left _ _
  have htargetdiv : (d*a.totient)*shiftedProduct t.left ∣ d*n.totient := by
    rw [← hprefixvalue]
    exact Nat.mul_dvd_mul_left _ hshiftdiv
  have hR : 0 < R := by
    dsimp only [R, pptRightLowFactor]
    apply Nat.mul_pos hE
    apply Finset.prod_pos
    intro i _
    exact Nat.sub_pos_of_lt (hq i).1.one_lt
  have htailreal : a = ∏ i, pptTailList p J i := (ppt_tail_list_product p J).symm
  have htailinj : Function.Injective (pptTailList p J) :=
    hpa.injective.comp ((pptTailIndices k J).orderEmbOfFin rfl).injective
  have hreal : n = c*a*∏ i, t.left i := by
    rw [hn, ← ppt_prime_prefix_tail_split p hJp,
      ← ppt_canceled_prime_product_split P Q]
    dsimp only [a, c, t, pptCanceledPair, Function.comp_apply]
    ring
  refine ⟨b, h, s, c, a, t, pptTailList p J, hb, ?_, ?_, ?_,
    ppt_canceled_prime_product_pos P Q (fun i => (hP i).1), ?_, hreal,
    ?_, ?_, htailreal, htailinj, ?_, ppt_tail_list_mem p J, ?_, ?_, ?_, hR, ?_, ?_, ?_,
    squarefreeAbove_of_dvd htargetdiv hsq, rfl, ?_, ?_, ?_⟩
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  · apply Finset.prod_pos
    intro i _
    exact (hp i).1.pos
  · exact ppt_prime_sublist_label P (pptEqualCoordinates P Q)
      (fun i => ⟨hpN _, (hP i).1⟩)
  · exact ppt_prime_sublist_label p (pptTailIndices k J)
      (fun i => ⟨hpN i, (hp i).1⟩)
  · intro i
    obtain ⟨j, hj, he⟩ := ppt_tail_list_mem p J i
    rw [he]
    exact ⟨hp j, hptail j hj⟩
  · intro i
    exact ⟨hP _, hQ _, hp3 _, hq3 _, ppt_surviving_coordinates_unequal P Q i⟩
  · exact (ppt_surviving_coordinates_strictAnti P Q hPa hQa).1
  · exact (ppt_surviving_coordinates_strictAnti P Q hPa hQa).2
  · exact ppt_right_low_factor_smooth q hV hEV hqtail
  · exact ppt_cancel_matching_coordinates P Q (fun i => (hP i).1) hprefixeq
  · exact ppt_canceled_comparison_size P Q (fun i => (hP i).1) hPa.injective hprefixsize
  · exact ⟨pptCoordinateEmbedding P Q, fun _ => ⟨rfl,rfl⟩⟩
  · exact ⟨(pptCoordinateEmbedding P Q).trans (Fin.castLEOrderEmb hJp), fun _ => rfl⟩
  · refine ⟨hb, ?_⟩
    change P (pptCoordinateEmbedding P Q ⟨0,hb⟩) = _
    rw [hzero]
    rfl

end TotientAsymptotic

end

end OAI

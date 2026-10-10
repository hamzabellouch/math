import OAI.Analysis.OInfinity.EvenRowCAR

namespace OAI

/-! # CAR relations for the actual finite even-row shift

The seed and parity are formed from the two equally sized blocks of the
given row. Their iterates satisfy CAR and exact covariance on even products.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E] {n : ℕ}
variable (q : E) (r : Fin 2 × Fin n → E)
  (hqstar : star q = q) (hqq : q * q = q)
  (hrow : ∀ i j, star (r i) * r j = if i = j then q else 0)
  (hsum : (∑ i, r i * star (r i)) = q)

lemma evenRowShift_smul (x : E) (c : ℂ) : evenRowShift r (c • x) = c • evenRowShift r x := by
  simp only [evenRowShift, mul_smul_comm, smul_mul_assoc, Finset.smul_sum]

lemma evenRowShift_sum {I : Type*} [Fintype I] (x : I → E) :
    evenRowShift r (∑ i, x i) = ∑ i, evenRowShift r (x i) := by
  simp only [evenRowShift, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

include hqstar hqq hrow in
lemma evenRowCAR_succ_commute_parity (k : ℕ) :
    Commute (evenRowParity r) (evenRowCAR r (k + 1)) := by
  change Commute (evenRowParity r) (evenRowParity r * evenRowShift r (evenRowCAR r k))
  exact (Commute.refl _).mul_right (evenRowParity_commute_shift q r hqstar hqq hrow _)

include hqstar hqq hrow hsum in
lemma evenRowCAR_shift_single (k : ℕ) :
    evenRowShift r (evenRowCAR r k) = evenRowParity r * evenRowCAR r (k + 1) := by
  change _ = evenRowParity r * (evenRowParity r * evenRowShift r (evenRowCAR r k))
  rw [← mul_assoc, (evenRowParity_relations q r hqstar hqq hrow hsum).2.1,
    (evenRowShift_support q r hqstar hqq hrow hsum _).1]

include hqstar hqq hrow hsum in
lemma evenRowParity_shift_mul (x y : E) (hy : q * y = y) :
    (evenRowParity r * evenRowShift r x) * (evenRowParity r * evenRowShift r y) =
      evenRowShift r (x * y) := by
  have hc := evenRowParity_commute_shift q r hqstar hqq hrow x
  have hp := (evenRowParity_relations q r hqstar hqq hrow hsum).2.1
  have hs := (evenRowShift_support q r hqstar hqq hrow hsum x).2
  calc
    _ = evenRowShift r x * (evenRowParity r * evenRowParity r) * evenRowShift r y := by
      rw [hc.eq]
      noncomm_ring
    _ = evenRowShift r x * evenRowShift r y := by rw [hp, hs]
    _ = _ := evenRowShift_mul q r hrow x y hy

include hqstar hqq hrow hsum in
lemma evenRowParity_shift_star_mul (x y : E) (hy : q * y = y) :
    star (evenRowParity r * evenRowShift r x) *
      (evenRowParity r * evenRowShift r y) = evenRowShift r (star x * y) := by
  have hp := evenRowParity_relations q r hqstar hqq hrow hsum
  have hs := (evenRowShift_support q r hqstar hqq hrow hsum (star x)).2
  rw [star_mul, hp.1, evenRowShift_star]
  calc
    _ = evenRowShift r (star x) * (evenRowParity r * evenRowParity r) * evenRowShift r y := by
      noncomm_ring
    _ = evenRowShift r (star x) * evenRowShift r y := by rw [hp.2.1, hs]
    _ = _ := evenRowShift_mul q r hrow _ _ hy

include hqstar hqq hrow hsum in
lemma evenRowCAR_shift_even (i j : ℕ) :
    evenRowShift r (evenRowCAR r i * star (evenRowCAR r j)) =
      evenRowCAR r (i + 1) * star (evenRowCAR r (j + 1)) := by
  have hs := (evenRowCAR_support q r hqstar hqq hrow hsum j).2
  have hstar : q * star (evenRowCAR r j) = star (evenRowCAR r j) := by
    simpa only [star_mul, hqstar] using congrArg star hs
  have hci := evenRowParity_commute_shift q r hqstar hqq hrow (evenRowCAR r i)
  have hcj := evenRowParity_commute_shift q r hqstar hqq hrow (star (evenRowCAR r j))
  have hp := evenRowParity_relations q r hqstar hqq hrow hsum
  have hsupport := (evenRowShift_support q r hqstar hqq hrow hsum (star (evenRowCAR r j))).2
  rw [← evenRowShift_mul q r hrow _ _ hstar]
  simp only [evenRowCAR, star_mul, hp.1, evenRowShift_star]
  symm
  calc
    _ = evenRowShift r (evenRowCAR r i) *
        (evenRowParity r * evenRowShift r (star (evenRowCAR r j))) * evenRowParity r := by
      rw [hci.eq]
      noncomm_ring
    _ = evenRowShift r (evenRowCAR r i) *
        (evenRowShift r (star (evenRowCAR r j)) * evenRowParity r) * evenRowParity r := by
      rw [hcj.eq]
    _ = evenRowShift r (evenRowCAR r i) *
        (evenRowShift r (star (evenRowCAR r j)) * (evenRowParity r * evenRowParity r)) := by
      noncomm_ring
    _ = _ := by rw [hp.2.1, hsupport]

include hqstar hqq hrow hsum in
lemma evenRowCAR_seed_anticommute (k : ℕ) :
    evenRowCAR r 0 * evenRowCAR r (k + 1) + evenRowCAR r (k + 1) * evenRowCAR r 0 = 0 := by
  have hc := evenRowSeed_commute_shift q r hqstar hqq hrow (evenRowCAR r k)
  have hz := (evenRowSeed_relations q r hqstar hqq hrow hsum).2.2
  change evenRowSeed r * (evenRowParity r * evenRowShift r _) +
    (evenRowParity r * evenRowShift r _) * evenRowSeed r = 0
  calc
    _ = (evenRowSeed r * evenRowParity r) * evenRowShift r (evenRowCAR r k) +
        evenRowParity r * (evenRowShift r (evenRowCAR r k) * evenRowSeed r) := by
      noncomm_ring
    _ = (evenRowSeed r * evenRowParity r) * evenRowShift r (evenRowCAR r k) +
        evenRowParity r * (evenRowSeed r * evenRowShift r (evenRowCAR r k)) := by rw [← hc.eq]
    _ = (evenRowSeed r * evenRowParity r + evenRowParity r * evenRowSeed r) *
        evenRowShift r (evenRowCAR r k) := by noncomm_ring
    _ = 0 := by rw [hz]; simp

include hqstar hqq hrow hsum in
lemma evenRowCAR_anticommute : ∀ i j,
    evenRowCAR r i * evenRowCAR r j + evenRowCAR r j * evenRowCAR r i = 0 := by
  have hseed := (evenRowSeed_relations q r hqstar hqq hrow hsum).1
  intro i
  induction i with
  | zero =>
    intro j
    cases j with
    | zero => change evenRowSeed r * evenRowSeed r + evenRowSeed r * evenRowSeed r = 0
              rw [hseed, zero_add]
    | succ j => exact evenRowCAR_seed_anticommute q r hqstar hqq hrow hsum j
  | succ i ih =>
    intro j
    cases j with
    | zero =>
      rw [add_comm]
      exact evenRowCAR_seed_anticommute q r hqstar hqq hrow hsum i
    | succ j =>
      have hi := (evenRowCAR_support q r hqstar hqq hrow hsum i).1
      have hj := (evenRowCAR_support q r hqstar hqq hrow hsum j).1
      simp only [evenRowCAR]
      rw [evenRowParity_shift_mul q r hqstar hqq hrow hsum _ _ hj,
        evenRowParity_shift_mul q r hqstar hqq hrow hsum _ _ hi,
        ← evenRowShift_add, ih j, evenRowShift_zero]

include hqstar hqq hrow hsum in
lemma evenRowCAR_seed_star_anticommute (k : ℕ) :
    star (evenRowCAR r 0) * evenRowCAR r (k + 1) +
      evenRowCAR r (k + 1) * star (evenRowCAR r 0) = 0 := by
  have hc₀ := evenRowSeed_commute_shift q r hqstar hqq hrow (star (evenRowCAR r k))
  have hc : Commute (star (evenRowSeed r)) (evenRowShift r (evenRowCAR r k)) := by
    simpa only [evenRowShift_star, star_star] using hc₀.star_star
  have hz₀ := (evenRowSeed_relations q r hqstar hqq hrow hsum).2.2
  have hp := (evenRowParity_relations q r hqstar hqq hrow hsum).1
  have hz : star (evenRowSeed r) * evenRowParity r =
      -(evenRowParity r * star (evenRowSeed r)) := by
    simpa only [star_mul, star_neg, hp, mul_neg] using congrArg star hz₀
  change star (evenRowSeed r) * (evenRowParity r * evenRowShift r _) +
    (evenRowParity r * evenRowShift r _) * star (evenRowSeed r) = 0
  calc
    _ = (star (evenRowSeed r) * evenRowParity r) * evenRowShift r (evenRowCAR r k) +
        evenRowParity r * (evenRowShift r (evenRowCAR r k) * star (evenRowSeed r)) := by
      noncomm_ring
    _ = (star (evenRowSeed r) * evenRowParity r) * evenRowShift r (evenRowCAR r k) +
        evenRowParity r * (star (evenRowSeed r) * evenRowShift r (evenRowCAR r k)) := by
      rw [← hc.eq]
    _ = (star (evenRowSeed r) * evenRowParity r + evenRowParity r * star (evenRowSeed r)) *
        evenRowShift r (evenRowCAR r k) := by noncomm_ring
    _ = 0 := by rw [hz]; simp

include hqstar hqq hrow hsum in
lemma evenRowCAR_star_anticommute : ∀ i j,
    star (evenRowCAR r i) * evenRowCAR r j + evenRowCAR r j * star (evenRowCAR r i) =
      if i = j then q else 0 := by
  intro i
  induction i with
  | zero =>
    intro j
    cases j with
    | zero => simpa only [evenRowCAR, ite_true] using
                (evenRowSeed_relations q r hqstar hqq hrow hsum).2.1
    | succ j => simpa only [Nat.zero_ne_add_one, ite_false] using
                  evenRowCAR_seed_star_anticommute q r hqstar hqq hrow hsum j
  | succ i ih =>
    intro j
    cases j with
    | zero =>
      have h := congrArg star (evenRowCAR_seed_star_anticommute q r hqstar hqq hrow hsum i)
      simpa only [star_add, star_mul, star_star, star_zero, Nat.add_one_ne_zero, ite_false] using h
    | succ j =>
      have hj := (evenRowCAR_support q r hqstar hqq hrow hsum j).1
      have heven := evenRowCAR_shift_even q r hqstar hqq hrow hsum j i
      change star (evenRowParity r * evenRowShift r (evenRowCAR r i)) *
        (evenRowParity r * evenRowShift r (evenRowCAR r j)) +
        evenRowCAR r (j + 1) * star (evenRowCAR r (i + 1)) = _
      rw [evenRowParity_shift_star_mul q r hqstar hqq hrow hsum _ _ hj,
        ← heven, ← evenRowShift_add, ih j]
      by_cases hij : i = j
      · subst j
        simp only [ite_true, evenRowShift_unit q r hqstar hqq hrow hsum]
      · have hsij : i + 1 ≠ j + 1 := by omega
        simp only [hij, hsij, ite_false, evenRowShift_zero]

include hqstar hqq hrow hsum in
lemma evenRowCAR_synthesis_norm_sq_le {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → ℕ) (hf : Function.Injective f) (c : I → ℂ) :
    ‖carSynthesis (fun i => evenRowCAR r (f i)) c‖ *
      ‖carSynthesis (fun i => evenRowCAR r (f i)) c‖ ≤ ∑ i, ‖c i‖ ^ 2 := by
  apply carSynthesis_norm_sq_le q
  · intro i
    exact (evenRowCAR_support q r hqstar hqq hrow hsum (f i)).1
  · intro i j
    exact evenRowCAR_anticommute q r hqstar hqq hrow hsum (f i) (f j)
  · intro i j
    simpa only [hf.eq_iff] using
      evenRowCAR_star_anticommute q r hqstar hqq hrow hsum (f i) (f j)

end WeakPureInfiniteness

end

end OAI

import OAI.Analysis.OInfinity.CompressionTransfer

namespace OAI

/-! # The finite block flip and the actual row cocycle

The block flip permutes the composed row and is a selfadjoint relative
unitary. For commuting rows, multiplying the actual row cocycle by this
flip moves that cocycle into the shifted corner. The shifted cocycle is
retained: the identity does not make the cocycle finite-order.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E I : Type*} [CStarAlgebra E] [Fintype I] [DecidableEq I]

def finiteRowCocycle (s t : I → E) : E := ∑ i, t i * star (s i)

def finiteRowShift (s : I → E) (x : E) : E := ∑ i, s i * x * star (s i)

def finiteRowBlockFlip (s t : I → E) : E :=
  ∑ i, ∑ j, s i * t j * star (t i) * star (s j)

omit [DecidableEq I] in
lemma finiteRowCocycle_star (s t : I → E) :
    star (finiteRowCocycle s t) = finiteRowCocycle t s := by
  simp only [finiteRowCocycle, star_sum, star_mul, star_star]

omit [Fintype I] in
lemma finiteRow_right_support (q : E) (s : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0) (i : I) :
    s i * q = s i :=
  relativeIsometry_mul_support (s i) q (by simpa using hs i i) hqstar hqq

lemma finiteRow_left_support (q : E) (s : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q) (i : I) : q * s i = s i := by
  rw [← hsum, Finset.sum_mul]
  have hterm (j : I) : (s j * star (s j)) * s i = if j = i then s i else 0 := by
    rw [mul_assoc, hs]
    split_ifs with h
    · subst j
      exact finiteRow_right_support q s hqstar hqq hs i
    · exact mul_zero _
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma finiteRowCocycle_mul_row (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0) (i : I) :
    finiteRowCocycle s t * s i = t i := by
  rw [finiteRowCocycle, Finset.sum_mul]
  have hterm (j : I) : (t j * star (s j)) * s i = if j = i then t i else 0 := by
    rw [mul_assoc, hs]
    split_ifs with h
    · subst j
      exact finiteRow_right_support q t hqstar hqq ht i
    · exact mul_zero _
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma finiteRowCocycle_gram (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q) :
    star (finiteRowCocycle s t) * finiteRowCocycle s t = q ∧
      finiteRowCocycle s t * star (finiteRowCocycle s t) = q := by
  constructor
  · rw [finiteRowCocycle_star]
    change finiteRowCocycle t s * (∑ i, t i * star (s i)) = q
    rw [Finset.mul_sum]
    simp only [← mul_assoc, finiteRowCocycle_mul_row q t s hqstar hqq ht hs]
    exact hsum
  · rw [finiteRowCocycle_star]
    change finiteRowCocycle s t * (∑ i, s i * star (t i)) = q
    rw [Finset.mul_sum]
    simp only [← mul_assoc, finiteRowCocycle_mul_row q s t hqstar hqq hs ht]
    exact htsum

omit [DecidableEq I] in
lemma finiteRowBlockFlip_star (s t : I → E) :
    star (finiteRowBlockFlip s t) = finiteRowBlockFlip s t := by
  simp only [finiteRowBlockFlip, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  noncomm_ring

lemma finiteRow_composed_gram (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (htsum : (∑ i, t i * star (t i)) = q) (i j k l : I) :
    star (s i * t j) * (s k * t l) = if i = k ∧ j = l then q else 0 := by
  rw [star_mul]
  calc
    _ = star (t j) * (star (s i) * s k) * t l := by noncomm_ring
    _ = _ := by
      rw [hs]
      by_cases hik : i = k
      · subst k
        simp only [ite_true]
        rw [mul_assoc, finiteRow_left_support q t hqstar hqq ht htsum, ht]
        simp only [true_and]
      · simp only [hik, ite_false, mul_zero, zero_mul, false_and]

lemma finiteRowBlockFlip_mul_composed (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (htsum : (∑ i, t i * star (t i)) = q) (k l : I) :
    finiteRowBlockFlip s t * (s k * t l) = s l * t k := by
  rw [finiteRowBlockFlip, Finset.sum_mul]
  simp only [Finset.sum_mul]
  have hterm (i j : I) : (s i * t j * star (t i) * star (s j)) * (s k * t l) =
      if j = k ∧ i = l then s l * t k else 0 := by
    calc
      _ = (s i * t j) * (star (s j * t i) * (s k * t l)) := by
        rw [star_mul]
        noncomm_ring
      _ = _ := by
        rw [finiteRow_composed_gram q s t hqstar hqq hs ht htsum]
        split_ifs with h
        · rcases h with ⟨rfl, rfl⟩
          rw [mul_assoc, finiteRow_right_support q t hqstar hqq ht]
        · exact mul_zero _
  simp only [hterm]
  have hsum (i : I) :
      (∑ j, if j = k ∧ i = l then s l * t k else 0) =
        if i = l then s l * t k else 0 := by
    by_cases hil : i = l
    · simp only [hil, and_true, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · simp only [hil, and_false, ite_false, Finset.sum_const_zero]
  simp only [hsum, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma finiteRow_composed_sum (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q) :
    (∑ i, ∑ j, (s i * t j) * star (s i * t j)) = q := by
  calc
    _ = ∑ i, s i * (∑ j, t j * star (t j)) * star (s i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mul_sum, Finset.sum_mul, star_mul]
      apply Finset.sum_congr rfl
      intro j hj
      noncomm_ring
    _ = q := by
      simp only [htsum, finiteRow_right_support q s hqstar hqq hs]
      exact hsum

lemma finiteRowBlockFlip_sq (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q) :
    finiteRowBlockFlip s t * finiteRowBlockFlip s t = q := by
  have he : finiteRowBlockFlip s t = ∑ i, ∑ j, (s i * t j) * star (s j * t i) := by
    simp only [finiteRowBlockFlip, star_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    noncomm_ring
  calc
    _ = ∑ i, ∑ j, finiteRowBlockFlip s t * ((s i * t j) * star (s j * t i)) := by
      conv_lhs => rhs; rw [he]
      simp only [Finset.mul_sum]
    _ = ∑ i, ∑ j, (s j * t i) * star (s j * t i) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_assoc, finiteRowBlockFlip_mul_composed q s t hqstar hqq hs ht htsum]
    _ = q := by
      rw [Finset.sum_comm]
      exact finiteRow_composed_sum q s t hqstar hqq hs hsum htsum

/-- Commutation is needed here, in contrast to the flip's involution law. -/
lemma finiteRowBlockFlip_mul_target (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hc : ∀ i j, Commute (star (s i)) (t j)) (k : I) :
    finiteRowBlockFlip s t * t k = s k * finiteRowCocycle s t := by
  rw [finiteRowBlockFlip, Finset.sum_mul]
  simp only [Finset.sum_mul]
  have hterm (i j : I) : (s i * t j * star (t i) * star (s j)) * t k =
      if i = k then s k * t j * star (s j) else 0 := by
    calc
      _ = s i * t j * star (t i) * (star (s j) * t k) := by noncomm_ring
      _ = s i * t j * (star (t i) * t k) * star (s j) := by
        rw [(hc j k).eq]
        noncomm_ring
      _ = _ := by
        rw [ht]
        split_ifs with h
        · subst i
          rw [mul_assoc (s k), finiteRow_right_support q t hqstar hqq ht]
        · simp only [mul_zero, zero_mul]
  simp only [hterm]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [finiteRowCocycle, Finset.mul_sum, mul_assoc]

/-- Multiplying by the involution shifts the actual cocycle; its tail remains. -/
lemma finiteRowBlockFlip_mul_cocycle (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hc : ∀ i j, Commute (star (s i)) (t j)) :
    finiteRowBlockFlip s t * finiteRowCocycle s t = finiteRowShift s (finiteRowCocycle s t) := by
  rw [finiteRowCocycle, Finset.mul_sum]
  simp only [← mul_assoc, finiteRowBlockFlip_mul_target q s t hqstar hqq ht hc]
  rfl

/-- The cocycle has an involution factor and a shifted cocycle factor.
This equality retains the second factor rather than treating it as `q`. -/
lemma finiteRowCocycle_eq_flip_shift (q : E) (s t : I → E)
    (hqstar : star q = q) (hqq : q * q = q)
    (hs : ∀ i j, star (s i) * s j = if i = j then q else 0)
    (ht : ∀ i j, star (t i) * t j = if i = j then q else 0)
    (hsum : (∑ i, s i * star (s i)) = q)
    (htsum : (∑ i, t i * star (t i)) = q)
    (hc : ∀ i j, Commute (star (s i)) (t j)) :
    finiteRowCocycle s t = finiteRowBlockFlip s t * finiteRowShift s (finiteRowCocycle s t) := by
  have hqW : q * finiteRowCocycle s t = finiteRowCocycle s t := by
    simp only [finiteRowCocycle, Finset.mul_sum, ← mul_assoc,
      finiteRow_left_support q t hqstar hqq ht htsum]
  calc
    _ = q * finiteRowCocycle s t := hqW.symm
    _ = (finiteRowBlockFlip s t * finiteRowBlockFlip s t) * finiteRowCocycle s t := by
      rw [finiteRowBlockFlip_sq q s t hqstar hqq hs ht hsum htsum]
    _ = _ := by
      rw [mul_assoc, finiteRowBlockFlip_mul_cocycle q s t hqstar hqq ht hc]

end WeakPureInfiniteness

end

end OAI

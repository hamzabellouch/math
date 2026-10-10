import OAI.Analysis.PureInfiniteness.CollapseFiniteCompression

namespace OAI

/-! Finite orthogonal corner sums use relative support relations rather than
isometries in a unital algebra. These are the finite Cuntz-sum identities
needed for combining abelian-range maps on selected positive tests. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {D I : Type*} [NonUnitalCStarAlgebra D] [Fintype I] [DecidableEq I]

def relativeCornerSum (r x : I → D) : D := ∑ i, r i * x i * star (r i)

lemma relativeCornerSum_mul (r x y : I → D)
    (hrel : ∀ i j, (star (r i) * r j) * y j = if i = j then y j else 0) :
    relativeCornerSum r x * relativeCornerSum r y =
      relativeCornerSum r (fun i => x i * y i) := by
  have ht (i j : I) : (r i * x i * star (r i)) * (r j * y j * star (r j)) =
      if i = j then r i * (x i * y i) * star (r i) else 0 := by
    calc
      _ = r i * x i * ((star (r i) * r j) * y j) * star (r j) := by simp only [mul_assoc]
      _ = _ := by
        rw [hrel i j]
        by_cases hij : i = j
        · subst j
          simp only [ite_true, mul_assoc]
        · simp only [ite_eq_right hij, mul_zero, zero_mul]
  simp only [relativeCornerSum, Finset.sum_mul, Finset.mul_sum, ht]
  simp

lemma relativeCornerSum_commute (r x y : I → D)
    (hx : ∀ i j, (star (r i) * r j) * x j = if i = j then x j else 0)
    (hy : ∀ i j, (star (r i) * r j) * y j = if i = j then y j else 0)
    (hc : ∀ i, Commute (x i) (y i)) :
    Commute (relativeCornerSum r x) (relativeCornerSum r y) := by
  show _ * _ = _ * _
  rw [relativeCornerSum_mul r x y hy, relativeCornerSum_mul r y x hx]
  unfold relativeCornerSum
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [(hc i).eq]

lemma relativeCornerSum_coefficient (r x : I → D)
    (hx : ∀ i, IsSelfAdjoint (x i))
    (hrel : ∀ i j k, (star (r i) * r j) * x k = if i = j then x k else 0)
    (i j : I) :
    star (r i) * relativeCornerSum r x * r j = if i = j then x i else 0 := by
  have hright (i j k : I) : x k * (star (r i) * r j) = if i = j then x k else 0 := by
    have h := congrArg star (hrel j i k)
    by_cases hij : i = j
    · subst j
      simpa only [ite_eq_left rfl, ite_true, star_mul, star_star, (hx k).star_eq] using h
    · simpa only [ite_eq_right hij, ite_eq_right (Ne.symm hij), star_mul, star_star,
        (hx k).star_eq, star_zero] using h
  have ht (k : I) : star (r i) * (r k * x k * star (r k)) * r j =
      if k = i then (if i = j then x i else 0) else 0 := by
    calc
      _ = ((star (r i) * r k) * x k) * (star (r k) * r j) := by simp only [mul_assoc]
      _ = _ := by
        rw [hrel i k k]
        by_cases hki : k = i
        · subst k
          simpa only [ite_eq_left rfl, ite_true] using hright i j i
        · simp only [ite_eq_right hki, ite_eq_right (Ne.symm hki), zero_mul]
  simp only [relativeCornerSum, Finset.mul_sum, Finset.sum_mul, ht]
  simp

lemma relativeCornerSum_compression (r x a : I → D)
    (hx : ∀ i, IsSelfAdjoint (x i))
    (hrel : ∀ i j k, (star (r i) * r j) * x k = if i = j then x k else 0) :
    star (∑ i, r i * a i) * relativeCornerSum r x * (∑ i, r i * a i) =
      ∑ i, star (a i) * x i * a i := by
  calc
    _ = ∑ i, ∑ j, star (a i) *
        (star (r i) * relativeCornerSum r x * r j) * a j := by
      simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, star (a i) * (if i = j then x i else 0) * a j := by
      simp_rw [relativeCornerSum_coefficient r x hx hrel]
    _ = _ := by simp

end WeakPureInfiniteness

end

end OAI

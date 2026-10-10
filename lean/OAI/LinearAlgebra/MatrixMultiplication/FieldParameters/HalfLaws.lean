import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Compatibility
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.Traversal

namespace OAI

/-! Fixed rational distributions and their entropy and capacity formulas. -/

namespace MatrixMultiplication.AllFieldParameters

open scoped BigOperators

theorem stageBLaw_nonnegative (t u : Shape) : 0 ≤ stageBLaw t u := by
  by_cases hu : u ∈ below t
  · exact (stageBLaw_positive t u hu).le
  · simp [stageBLaw, splitLaw, hu]

theorem orderedPairs_mem_iff (t : Shape) (i j : Fin 6) :
    (i,j) ∈ orderedPairs t ↔ statisticWeight i + statisticWeight j = shapeMax t := by
  constructor
  · exact orderedPairs_support t (i,j)
  · intro h
    apply List.mem_flatMap.mpr
    refine ⟨i, by simp, ?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨j, by simp, by simp [h]⟩

theorem zeroPairLaw_nonnegative (t : Shape) (i j : Fin 6) : 0 ≤ zeroPairLaw t i j := by
  unfold zeroPairLaw
  split_ifs
  · exact div_nonneg (orderedPairWeight_positive t i j).le
      (list_sum_map_nonnegative _ _ (fun ij _ => (orderedPairWeight_positive t ij.1 ij.2).le))
  · exact le_rfl

theorem zeroPairLaw_full_normalized (t : Shape) (ht : t ∈ zeroSecond) :
    ∑ ij : PairSlot, zeroPairLaw t ij.1 ij.2 = 1 := by
  calc
    _ = ∑ ij ∈ (orderedPairs t).toFinset, zeroPairLaw t ij.1 ij.2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro ij _ hij
      have hs : statisticWeight ij.1 + statisticWeight ij.2 ≠ shapeMax t := by
        intro h
        exact hij (List.mem_toFinset.mpr ((orderedPairs_mem_iff t ij.1 ij.2).mpr h))
      simp [zeroPairLaw, hs]
    _ = ((orderedPairs t).map (fun ij => zeroPairLaw t ij.1 ij.2)).sum :=
      List.sum_toFinset _ (ordered_pairs_nodup t ht)
    _ = 1 := zeroPairLaw_normalized t ht

def positiveHalfLaw (t : Shape) (w : Fin 3) (ij : PairSlot) : ℚ :=
  ((below t).map fun u => stageBLaw t u * littleLaw t u w ij.1 *
    littleLaw t (complement t u) w ij.2).sum

theorem positiveHalfLaw_nonnegative (t : Shape) (w : Fin 3) (ij : PairSlot) :
    0 ≤ positiveHalfLaw t w ij := by
  apply list_sum_map_nonnegative
  intro u _
  exact mul_nonneg (mul_nonneg (stageBLaw_nonnegative t u)
    (littleLaw_nonnegative t u w ij.1))
    (littleLaw_nonnegative t (complement t u) w ij.2)

theorem sum_pair_mixture {A : Type*} (xs : List A) (mass : A → ℚ)
    (left right : A → Fin 6 → ℚ)
    (hl : ∀ x ∈ xs, ∑ i, left x i = 1)
    (hr : ∀ x ∈ xs, ∑ i, right x i = 1) :
    (∑ ij : PairSlot, (xs.map fun x => mass x * left x ij.1 * right x ij.2).sum) =
      (xs.map mass).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hleft := hl x (by simp)
    have hright := hr x (by simp)
    have hhead : (∑ ij : PairSlot, mass x * left x ij.1 * right x ij.2) = mass x := by
      simp [Fintype.sum_prod_type, ← Finset.mul_sum, hleft, hright]
    have htail := ih (fun y hy => hl y (by simp [hy])) (fun y hy => hr y (by simp [hy]))
    simpa only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, hhead] using
      congrArg (fun q : ℚ => mass x + q) htail

theorem positiveHalfLaw_normalized (t : Shape) (ht : t ∈ positiveSecond) (w : Fin 3) :
    ∑ ij : PairSlot, positiveHalfLaw t w ij = 1 := by
  unfold positiveHalfLaw
  rw [sum_pair_mixture _ _ _ _ (fun u _ => littleLaw_normalized t u w)
    (fun u _ => littleLaw_normalized t (complement t u) w)]
  exact stageBLaw_normalized t ht

theorem stageB_complement_permutation : ∀ t ∈ positiveSecond,
    ((below t).map (complement t)).Perm (below t) := by decide +kernel

theorem stageB_complement_involution (t : Shape) (ht : t ∈ positiveSecond)
    (u : Shape) (hu : u ∈ below t) : complement t (complement t u) = u := by
  funext w
  exact Nat.sub_sub_self ((stageB_support_complement t ht u hu).2 w)

theorem positiveHalfLaw_swap (t : Shape) (ht : t ∈ positiveSecond)
    (w : Fin 3) (i j : Fin 6) : positiveHalfLaw t w (i,j) = positiveHalfLaw t w (j,i) := by
  let f := fun u => stageBLaw t u * littleLaw t u w i * littleLaw t (complement t u) w j
  let g := fun u => stageBLaw t u * littleLaw t u w j * littleLaw t (complement t u) w i
  have hp := (stageB_complement_permutation t ht).map f
  have hm : ((below t).map (complement t)).map f = (below t).map g := by
    rw [List.map_map]
    apply List.map_congr_left
    intro u hu
    dsimp only [Function.comp_def, f, g]
    rw [stageBLaw_complement t u ht hu, stageB_complement_involution t ht u hu]
    ring
  change ((below t).map f).sum = ((below t).map g).sum
  rw [← hp.sum_eq, hm]

def halfMaxAxis (t : Shape) : Fin 3 :=
  (([0,1,2] : List (Fin 3)).find? (fun w => t w == shapeMax t)).getD 0

def halfLaw (t : Shape) (w : Fin 3) (ij : PairSlot) : ℚ :=
  if positive t then positiveHalfLaw t w ij
  else if t w = 0 then if ij = (0,0) then 1 else 0
  else if w = halfMaxAxis t then zeroPairLaw t ij.1 ij.2
  else zeroPairLaw t (kappa ij.1) (kappa ij.2)

theorem halfLaw_positive_parent (t : Shape) (ht : t ∈ positiveSecond)
    (w : Fin 3) (ij : PairSlot) : halfLaw t w ij = positiveHalfLaw t w ij := by
  have hp : positive t = true := (List.mem_filter.mp ht).2
  simp [halfLaw, hp]

theorem halfLaw_swap (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3) (i j : Fin 6) :
    halfLaw t w (i,j) = halfLaw t w (j,i) := by
  by_cases hp : positive t = true
  · simp only [halfLaw, hp, ite_true]
    exact positiveHalfLaw_swap t (List.mem_filter.mpr ⟨ht, hp⟩) w i j
  · unfold halfLaw
    simp only [hp, Bool.false_eq_true, ite_false]
    by_cases hw : t w = 0
    · simp [hw, Prod.mk.injEq, and_comm]
    · simp only [hw, ite_false]
      by_cases hm : w = halfMaxAxis t
      · simpa only [hm, ite_true] using zeroPairLaw_swap t i j
      · simpa only [hm, ite_false] using zeroPairLaw_swap t (kappa i) (kappa j)

theorem halfLaw_nonnegative (t : Shape) (w : Fin 3) (ij : PairSlot) :
    0 ≤ halfLaw t w ij := by
  unfold halfLaw
  split_ifs
  · exact positiveHalfLaw_nonnegative t w ij
  · norm_num
  · exact le_rfl
  · exact zeroPairLaw_nonnegative t ij.1 ij.2
  · exact zeroPairLaw_nonnegative t (kappa ij.1) (kappa ij.2)

def kappaEquiv : Fin 6 ≃ Fin 6 where
  toFun := kappa
  invFun := kappa
  left_inv := kappa_involution
  right_inv := kappa_involution

theorem sum_pair_kappa (f : PairSlot → ℚ) :
    (∑ ij : PairSlot, f (kappa ij.1, kappa ij.2)) = ∑ ij, f ij :=
  (Equiv.prodCongr kappaEquiv kappaEquiv).sum_comp f

theorem halfLaw_normalized (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3) :
    ∑ ij : PairSlot, halfLaw t w ij = 1 := by
  by_cases hp : positive t = true
  · simp only [halfLaw, hp, ite_true]
    exact positiveHalfLaw_normalized t (List.mem_filter.mpr ⟨ht, hp⟩) w
  · have hz : t ∈ zeroSecond := by simp [zeroSecond, ht, hp]
    simp only [halfLaw, hp, Bool.false_eq_true, ite_false]
    by_cases hw : t w = 0
    · simp [hw]
    · simp only [hw, ite_false]
      by_cases hm : w = halfMaxAxis t
      · simpa only [hm, ite_true] using zeroPairLaw_full_normalized t hz
      · simp only [hm, ite_false]
        rw [sum_pair_kappa (fun ij => zeroPairLaw t ij.1 ij.2)]
        exact zeroPairLaw_full_normalized t hz

theorem positiveHalfLaw_outside_support (t : Shape) (ht : t ∈ positiveSecond)
    (w : Fin 3) (ij : PairSlot)
    (h : statisticWeight ij.1 + statisticWeight ij.2 ≠ t w) :
    positiveHalfLaw t w ij = 0 := by
  unfold positiveHalfLaw
  have he : (below t).map (fun u => stageBLaw t u * littleLaw t u w ij.1 *
      littleLaw t (complement t u) w ij.2) = (below t).map (fun _ => (0 : ℚ)) := by
    apply List.map_congr_left
    intro u hu
    obtain ⟨hc, hb⟩ := stageB_support_complement t ht u hu
    by_cases hi : statisticWeight ij.1 = u w
    · have hj : statisticWeight ij.2 ≠ complement t u w := by
        intro hj
        apply h
        rw [hi, hj]
        change u w + (t w - u w) = t w
        have hw := hb w
        omega
      rw [littleLaw_outside_support t (complement t u) w
        (child_statistic_weight_bounded t ht (complement t u) hc w) ij.2 hj, mul_zero]
    · rw [littleLaw_outside_support t u w
        (child_statistic_weight_bounded t ht u hu w) ij.1 hi, mul_zero, zero_mul]
  rw [he]
  simp

theorem halfMaxAxis_spec : ∀ t ∈ shapes 8, t (halfMaxAxis t) = shapeMax t := by
  decide +kernel

theorem zero_other_axis_spec : ∀ t ∈ zeroSecond, ∀ w : Fin 3,
    t w ≠ 0 → w ≠ halfMaxAxis t → t w + shapeMax t = 8 := by decide +kernel

theorem statisticWeight_le_four (i : Fin 6) : statisticWeight i ≤ 4 := by
  revert i
  decide +kernel

theorem halfLaw_outside_support (t : Shape) (ht : t ∈ shapes 8)
    (w : Fin 3) (ij : PairSlot)
    (h : statisticWeight ij.1 + statisticWeight ij.2 ≠ t w) :
    halfLaw t w ij = 0 := by
  by_cases hp : positive t = true
  · simp only [halfLaw, hp, ite_true]
    exact positiveHalfLaw_outside_support t (List.mem_filter.mpr ⟨ht, hp⟩) w ij h
  · have hz : t ∈ zeroSecond := by simp [zeroSecond, ht, hp]
    simp only [halfLaw, hp, Bool.false_eq_true, ite_false]
    by_cases hw : t w = 0
    · have hij : ij ≠ (0,0) := by
        intro hij
        apply h
        rw [hij, hw]
        rfl
      rw [ite_eq_left hw, ite_eq_right hij]
    · simp only [hw, ite_false]
      by_cases hm : w = halfMaxAxis t
      · have hs : statisticWeight ij.1 + statisticWeight ij.2 ≠ shapeMax t := by
          simpa only [hm, halfMaxAxis_spec t ht] using h
        simp [hm, zeroPairLaw, hs]
      · have hs : statisticWeight (kappa ij.1) + statisticWeight (kappa ij.2) ≠
            shapeMax t := by
          have htotal := zero_other_axis_spec t hz w hw hm
          have hi := statisticWeight_le_four ij.1
          have hj := statisticWeight_le_four ij.2
          simp only [statisticWeight_kappa]
          omega
        simp [hm, zeroPairLaw, hs]

theorem zero_nonzero_axes_distinguished : ∀ t ∈ zeroSecond, ∀ w v : Fin 3,
    t w ≠ 0 → t v ≠ 0 → w ≠ v →
      (w = halfMaxAxis t ↔ v ≠ halfMaxAxis t) := by decide +kernel

theorem halfLaw_zero_complement (t : Shape) (ht : t ∈ zeroSecond)
    (w v : Fin 3) (hw : t w ≠ 0) (hv : t v ≠ 0) (hwv : w ≠ v) (ij : PairSlot) :
    halfLaw t w (kappa ij.1, kappa ij.2) = halfLaw t v ij := by
  have hp : positive t ≠ true := by
    have h := (List.mem_filter.mp ht).2
    simpa using h
  have hm := zero_nonzero_axes_distinguished t ht w v hw hv hwv
  by_cases ha : w = halfMaxAxis t
  · have hb : v ≠ halfMaxAxis t := hm.mp ha
    have hmax : t (halfMaxAxis t) ≠ 0 := by simpa only [ha] using hw
    simp [halfLaw, hp, hv, ha, hb, hmax]
  · have hb : v = halfMaxAxis t := by
      by_contra hne
      exact ha (hm.mpr hne)
    have hmax : t (halfMaxAxis t) ≠ 0 := by simpa only [hb] using hv
    simp [halfLaw, hp, hw, ha, hb, hmax, kappa_involution]

end MatrixMultiplication.AllFieldParameters

end OAI

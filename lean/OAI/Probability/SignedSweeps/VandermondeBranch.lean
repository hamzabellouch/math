import OAI.Probability.SignedSweeps.YoungRecurrence

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators Classical

def nodeVandermonde {I : Type*} [Fintype I] [LinearOrder I] (x : I → ℝ) : ℝ :=
  ∏ a, ∏ b, if a < b then x a - x b else 1

lemma nodeVandermonde_pos {I : Type*} [Fintype I] [LinearOrder I]
    (x : I → ℝ) (hx : StrictAnti x) : 0 < nodeVandermonde x := by
  apply Finset.prod_pos
  intro a _
  apply Finset.prod_pos
  intro b _
  split_ifs with h
  · exact sub_pos.mpr (hx h)
  · exact zero_lt_one

theorem nodeVandermonde_update {I : Type*} [Fintype I] [LinearOrder I]
    (x : I → ℝ) (hx : Function.Injective x) (i : I) :
    nodeVandermonde (Function.update x i (x i - 1)) =
      nodeVandermonde x * ∏ j ∈ Finset.univ.erase i,
        ((x i - x j - 1) / (x i - x j)) := by
  let r := fun j => (x i - x j - 1) / (x i - x j)
  have hp (a b : I) :
      (if a < b then Function.update x i (x i - 1) a -
          Function.update x i (x i - 1) b else 1) =
        (if a < b then x a - x b else 1) *
        (if a = i ∧ a < b then r b else 1) *
        (if b = i ∧ a < b then r a else 1) := by
    by_cases hab : a < b
    · have hne : a ≠ b := ne_of_lt hab
      have hn : x a - x b ≠ 0 := sub_ne_zero.mpr (hx.ne hne)
      by_cases ha : a = i
      · subst a
        have hb : b ≠ i := hne.symm
        simp only [hab, ite_true, Function.update_self, Function.update_of_ne hb,
          and_self, hb, false_and, ite_false, mul_one, r]
        field_simp
        ring
      · by_cases hb : b = i
        · subst b
          simp only [hab, ite_true, Function.update_self, Function.update_of_ne ha,
            ha, false_and, ite_false, and_self, mul_one, r]
          have hn' : x i - x a ≠ 0 := sub_ne_zero.mpr (hx.ne (Ne.symm ha))
          field_simp
          ring
        · simp [hab, ha, hb, Function.update_of_ne]
    · simp [hab]
  have hr : (∏ a, ∏ b, if a = i ∧ a < b then r b else 1) =
      ∏ b, if i < b then r b else 1 := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro b _
    simp_rw [ite_and]
    simp
  have hc : (∏ a, ∏ b, if b = i ∧ a < b then r a else 1) =
      ∏ a, if a < i then r a else 1 := by
    apply Finset.prod_congr rfl
    intro a _
    simp_rw [ite_and]
    simp
  have hrc : (∏ b, if i < b then r b else 1) *
      (∏ a, if a < i then r a else 1) = ∏ j ∈ Finset.univ.erase i, r j := by
    rw [← Finset.prod_mul_distrib]
    have he : (∏ j, (if i < j then r j else 1) * (if j < i then r j else 1)) =
        ∏ j, if j = i then 1 else r j := by
      apply Finset.prod_congr rfl
      intro j _
      rcases lt_trichotomy i j with hj | rfl | hj
      · simp [hj, not_lt.mpr hj.le, ne_of_gt hj]
      · simp
      · simp [hj, not_lt.mpr hj.le, ne_of_lt hj]
    rw [he, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [ite_true, one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    rw [ite_eq_right (Finset.mem_erase.mp hj).1]
  simp_rw [nodeVandermonde, hp, Finset.prod_mul_distrib]
  rw [hr, hc, mul_assoc, hrc]

theorem nodeVandermonde_branching {I : Type*} [Fintype I] [LinearOrder I]
    (x : I → ℝ) (hx : Function.Injective x) :
    ∑ i, x i * nodeVandermonde (Function.update x i (x i - 1)) =
      ((∑ i, x i) - (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) / 2) *
        nodeVandermonde x := by
  simp_rw [nodeVandermonde_update x hx]
  calc
    _ = (∑ i, x i * ∏ j ∈ Finset.univ.erase i,
        ((x i - x j - 1) / (x i - x j))) * nodeVandermonde x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intros
      ring
    _ = _ := by
      convert congrArg (· * nodeVandermonde x)
        (young_rational_recurrence (Finset.univ : Finset I) x hx.injOn) using 1
      simp

end SignedSweeps
end

end OAI

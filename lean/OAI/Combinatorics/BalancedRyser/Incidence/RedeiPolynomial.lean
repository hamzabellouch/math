import OAI.Combinatorics.BalancedRyser.Incidence.Affine
import OAI.Combinatorics.BalancedRyser.Incidence.StabilityPolynomial2
import OAI.Combinatorics.BalancedRyser.Profiles.FiniteGridVanishing

namespace OAI

namespace Balanced.StabilityPolynomial

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F]

noncomputable def redeiFactor (p : Point F) : MvPolynomial (Fin 2) F :=
  X 0 + C p.1 * X 1 - C p.2

noncomputable def redeiPolynomial (U : Finset (Point F)) : MvPolynomial (Fin 2) F :=
  ∏ p ∈ U, redeiFactor p

theorem eval_redeiFactor_eq_zero_iff (p : Point F) (z : Fin 2 → F) :
    eval z (redeiFactor p) = 0 ↔ OnLine p (some (z 1), z 0) := by
  simp only [redeiFactor, map_sub, map_add, map_mul, eval_X, eval_C,
    OnLine, lineEval]
  constructor <;> intro h <;> linear_combination -h

theorem redeiFactor_ne_zero (p : Point F) : redeiFactor p ≠ 0 := by
  intro h
  have he := congrArg (eval ![p.2 + 1, 0]) h
  simp [redeiFactor] at he

theorem redeiPolynomial_ne_zero (U : Finset (Point F)) : redeiPolynomial U ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun p _ => redeiFactor_ne_zero p)

theorem redeiFactor_totalDegree_le (p : Point F) : (redeiFactor p).totalDegree ≤ 1 := by
  have hmul : (C p.1 * (X 1 : MvPolynomial (Fin 2) F)).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by simp)
  exact (totalDegree_sub_C_le _ _).trans
    ((totalDegree_add _ _).trans (max_le (by simp) hmul))

theorem redeiFactor_coeff_X (p : Point F) :
    (redeiFactor p).coeff (Finsupp.single 0 1) = 1 := by
  have hzero : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro h
    have hz := congrArg (fun m : Fin 2 →₀ ℕ => m 0) h
    simp at hz
  simp [redeiFactor, coeff_X, coeff_C_mul, coeff_C, Finsupp.single_eq_single_iff, hzero]

theorem redeiFactor_totalDegree (p : Point F) : (redeiFactor p).totalDegree = 1 := by
  apply Nat.le_antisymm (redeiFactor_totalDegree_le p)
  have hm : Finsupp.single (0 : Fin 2) 1 ∈ (redeiFactor p).support := by
    rw [mem_support_iff, redeiFactor_coeff_X]
    exact one_ne_zero
  simpa using le_totalDegree hm

theorem redeiPolynomial_totalDegree (U : Finset (Point F)) :
    (redeiPolynomial U).totalDegree = U.card := by
  classical
  induction U using Finset.induction_on with
  | empty => simp [redeiPolynomial]
  | @insert p U hp ih =>
    rw [redeiPolynomial, Finset.prod_insert hp]
    change (redeiFactor p * redeiPolynomial U).totalDegree = (insert p U).card
    rw [totalDegree_mul_of_isDomain (redeiFactor_ne_zero p) (redeiPolynomial_ne_zero U),
      redeiFactor_totalDegree]
    rw [ih, Finset.card_insert_of_notMem hp]
    omega

theorem redeiPolynomial_totalDegree_le (U : Finset (Point F)) :
    (redeiPolynomial U).totalDegree ≤ U.card := by
  classical
  calc
    (redeiPolynomial U).totalDegree ≤ ∑ p ∈ U, (redeiFactor p).totalDegree :=
      totalDegree_finsetProd _ _
    _ ≤ ∑ _p ∈ U, 1 := Finset.sum_le_sum fun p _ => redeiFactor_totalDegree_le p
    _ = U.card := by simp

theorem redei_mul_vanishes
    (U : Finset (Point F)) (a : MvPolynomial (Fin 2) F)
    (ha : ∀ z : Fin 2 → F,
      (∀ p ∈ U, ¬ OnLine p (some (z 1), z 0)) → eval z a = 0) :
    ∀ z : Fin 2 → F, eval z (redeiPolynomial U * a) = 0 := by
  classical
  intro z
  by_cases h : ∃ p ∈ U, OnLine p (some (z 1), z 0)
  · obtain ⟨p, hp, hon⟩ := h
    rw [map_mul]
    have hz : eval z (redeiPolynomial U) = 0 := by
      rw [redeiPolynomial, map_prod]
      exact Finset.prod_eq_zero hp ((eval_redeiFactor_eq_zero_iff p z).mpr hon)
    rw [hz, zero_mul]
  · rw [map_mul, ha z (by simpa only [not_exists, not_and] using h), mul_zero]

theorem redei_mul_totalDegree_le
    (U : Finset (Point F)) (a : MvPolynomial (Fin 2) F) :
    (redeiPolynomial U * a).totalDegree ≤ U.card + a.totalDegree :=
  (totalDegree_mul _ _).trans (Nat.add_le_add_right (redeiPolynomial_totalDegree_le U) _)

theorem redei_mul_totalDegree
    (U : Finset (Point F)) (a : MvPolynomial (Fin 2) F) (ha : a ≠ 0) :
    (redeiPolynomial U * a).totalDegree = U.card + a.totalDegree := by
  rw [totalDegree_mul_of_isDomain (redeiPolynomial_ne_zero U) ha,
    redeiPolynomial_totalDegree]

variable [Fintype F]

noncomputable def nonverticalSkewCodes (U : Finset (Point F)) : Finset (Fin 2 → F) := by
  classical
  exact Finset.univ.filter fun z => ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0)

theorem mem_nonverticalSkewCodes (U : Finset (Point F)) (z : Fin 2 → F) :
    z ∈ nonverticalSkewCodes U ↔ ∀ p ∈ U, ¬ OnLine p (some (z 1), z 0) := by
  classical
  simp only [nonverticalSkewCodes, Finset.mem_filter, Finset.mem_univ, true_and]

theorem exists_redei_auxiliary (U : Finset (Point F)) (d : ℕ)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2)) :
    ∃ a : MvPolynomial (Fin 2) F, a ≠ 0 ∧ a.totalDegree ≤ d ∧
      ∀ z : Fin 2 → F,
        (∀ p ∈ U, ¬ OnLine p (some (z 1), z 0)) → eval z a = 0 := by
  obtain ⟨a, hne, hdeg, hvan⟩ := exists_bivariate_vanishing (nonverticalSkewCodes U) d hsize
  exact ⟨a, hne, hdeg, fun z hz => hvan z ((mem_nonverticalSkewCodes U z).mpr hz)⟩

theorem redei_mul_decomposition
    (U : Finset (Point F)) (a : MvPolynomial (Fin 2) F)
    (ha : ∀ z : Fin 2 → F,
      (∀ p ∈ U, ¬ OnLine p (some (z 1), z 0)) → eval z a = 0) :
    ∃ f g : MvPolynomial (Fin 2) F,
      f.totalDegree ≤ U.card + a.totalDegree - Fintype.card F ∧
      g.totalDegree ≤ U.card + a.totalDegree - Fintype.card F ∧
      redeiPolynomial U * a = ((X 0) ^ Fintype.card F - X 0) * f +
        ((X 1) ^ Fintype.card F - X 1) * g := by
  obtain ⟨f, g, hf, hg, heq⟩ := bivariate_grid_decomposition_degree
    (redeiPolynomial U * a) (redei_mul_vanishes U a ha)
  have hdeg := Nat.sub_le_sub_right (redei_mul_totalDegree_le U a) (Fintype.card F)
  exact ⟨f, g, hf.trans hdeg, hg.trans hdeg, heq⟩

theorem exists_redei_decomposition (U : Finset (Point F)) (d : ℕ)
    (hsize : 2 * (nonverticalSkewCodes U).card < (d + 1) * (d + 2)) :
    ∃ a f g : MvPolynomial (Fin 2) F,
      a ≠ 0 ∧ a.totalDegree ≤ d ∧ redeiPolynomial U * a ≠ 0 ∧
      f.totalDegree ≤ U.card + d - Fintype.card F ∧
      g.totalDegree ≤ U.card + d - Fintype.card F ∧
      redeiPolynomial U * a = ((X 0) ^ Fintype.card F - X 0) * f +
        ((X 1) ^ Fintype.card F - X 1) * g := by
  obtain ⟨a, hne, hdeg, hvan⟩ := exists_redei_auxiliary U d hsize
  obtain ⟨f, g, hf, hg, heq⟩ := redei_mul_decomposition U a hvan
  have hd := Nat.sub_le_sub_right (Nat.add_le_add_left hdeg U.card) (Fintype.card F)
  exact ⟨a, f, g, hne, hdeg, mul_ne_zero (redeiPolynomial_ne_zero U) hne,
    hf.trans hd, hg.trans hd, heq⟩

end Balanced.StabilityPolynomial

end OAI

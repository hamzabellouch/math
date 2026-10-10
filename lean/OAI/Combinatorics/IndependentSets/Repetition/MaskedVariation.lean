import Mathlib
import OAI.Combinatorics.IndependentSets.Repetition.Reveal

namespace OAI

namespace IndependentSetsGames.Foundations.Repetition
open scoped BigOperators
noncomputable section
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

def maskedJoint (p : S × (X × Y) → ℝ) : (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  (if z.1.2 = Sum.inl z.2.1 then p (z.1.1, z.2) / 2 else 0) +
  (if z.1.2 = Sum.inr z.2.2 then p (z.1.1, z.2) / 2 else 0)

def maskedModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    (S × (X ⊕ Y)) × (X × Y) → ℝ := fun z =>
  Information.firstMarginal (maskedJoint p) z.1 * (revealProfile μ z.1.2).weight z.2

def leftRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ y, p (z.1, (z.2.1, y))) * (revealProfile μ (Sum.inl z.2.1)).weight z.2

def rightRevealModel (μ : Games.FiniteDistribution (X × Y)) (p : S × (X × Y) → ℝ) :
    S × (X × Y) → ℝ := fun z =>
  (∑ x, p (z.1, (x, z.2.2))) * (revealProfile μ (Sum.inr z.2.2)).weight z.2

theorem sum_maskedJoint (p : S × (X × Y) → ℝ) :
    (∑ z, maskedJoint p z) = ∑ z, p z := by
  classical
  have hrow (s : S) (q : X × Y) :
      (∑ r : X ⊕ Y, maskedJoint p ((s,r),q)) = p (s,q) := by
    simp [maskedJoint]
  calc
    _ = ∑ s : S, ∑ r : X ⊕ Y, ∑ q : X × Y, maskedJoint p ((s,r),q) := by
      simp only [Fintype.sum_prod_type]
    _ = ∑ s : S, ∑ q : X × Y, p (s,q) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      simp_rw [hrow]
    _ = _ := (Fintype.sum_prod_type _).symm

theorem maskedJoint_isProbability_iff (p : S × (X × Y) → ℝ) :
    Information.IsProbability (maskedJoint p) ↔ Information.IsProbability p := by
  classical
  constructor
  · intro h
    constructor
    · intro z
      have hp := h.1 ((z.1,Sum.inl z.2.1),z.2)
      simp [maskedJoint] at hp
      linarith
    · rw [← sum_maskedJoint]
      exact h.2
  · intro h
    constructor
    · intro z
      have hp : 0 ≤ p (z.1.1,z.2) / 2 := div_nonneg (h.1 _) (by norm_num)
      dsimp [maskedJoint]
      split_ifs <;> linarith
    · rw [sum_maskedJoint]
      exact h.2

omit [Fintype S] in
theorem maskedJoint_firstMarginal_inl (p : S × (X × Y) → ℝ) (s : S) (x : X) :
    Information.firstMarginal (maskedJoint p) (s, Sum.inl x) =
      (∑ y, p (s, (x, y))) / 2 := by
  simp [Information.firstMarginal, maskedJoint, Fintype.sum_prod_type,
    div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp

omit [Fintype S] in
theorem maskedJoint_firstMarginal_inr (p : S × (X × Y) → ℝ) (s : S) (y : Y) :
    Information.firstMarginal (maskedJoint p) (s, Sum.inr y) =
      (∑ x, p (s, (x, y))) / 2 := by
  simp [Information.firstMarginal, maskedJoint, Fintype.sum_prod_type,
    div_eq_mul_inv, Finset.sum_mul]

private theorem abs_half_sub_half_mul (a b c : ℝ) :
    |a / 2 - b / 2 * c| = |a - b * c| / 2 := by
  rw [show a / 2 - b / 2 * c = (a - b * c) / 2 by ring, abs_div]
  norm_num

omit [Fintype S] in
theorem abs_masked_inl (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) (s : S) (u x : X) (y : Y) :
    |maskedJoint p ((s, Sum.inl u), (x, y)) - maskedModel μ p ((s, Sum.inl u), (x, y))| =
      if x = u then |p (s, (x, y)) - leftRevealModel μ p (s, (x, y))| / 2 else 0 := by
  by_cases hx : x = u
  · subst x
    simp only [maskedModel, maskedJoint_firstMarginal_inl]
    simpa [maskedJoint, leftRevealModel] using
      abs_half_sub_half_mul (p (s, (u, y))) (∑ v, p (s, (u, v)))
        ((revealProfile μ (Sum.inl u)).weight (u, y))
  · have hs := revealProfile_inl_support μ u (x, y) hx
    simp [maskedJoint, maskedModel, hs, hx, Ne.symm hx]

omit [Fintype S] in
theorem abs_masked_inr (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) (s : S) (v : Y) (x : X) (y : Y) :
    |maskedJoint p ((s, Sum.inr v), (x, y)) - maskedModel μ p ((s, Sum.inr v), (x, y))| =
      if y = v then |p (s, (x, y)) - rightRevealModel μ p (s, (x, y))| / 2 else 0 := by
  by_cases hy : y = v
  · subst y
    simp only [maskedModel, maskedJoint_firstMarginal_inr]
    simpa [maskedJoint, rightRevealModel] using
      abs_half_sub_half_mul (p (s, (x, v))) (∑ u, p (s, (u, v)))
        ((revealProfile μ (Sum.inr v)).weight (x, v))
  · have hs := revealProfile_inr_support μ v (x, y) hy
    simp [maskedJoint, maskedModel, hs, hy, Ne.symm hy]

theorem masked_totalVariation_identity (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) =
      Information.totalVariation p (leftRevealModel μ p) +
        Information.totalVariation p (rightRevealModel μ p) := by
  have hleft (s : S) :
      (∑ u : X, ∑ q : X × Y,
        |maskedJoint p ((s, Sum.inl u), q) - maskedModel μ p ((s, Sum.inl u), q)|) =
      (∑ q : X × Y, |p (s, q) - leftRevealModel μ p (s, q)|) / 2 := by
    simp_rw [Fintype.sum_prod_type, abs_masked_inl]
    simp [Finset.sum_ite_irrel, div_eq_mul_inv, Finset.sum_mul]
  have hright (s : S) :
      (∑ v : Y, ∑ q : X × Y,
        |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|) =
      (∑ q : X × Y, |p (s, q) - rightRevealModel μ p (s, q)|) / 2 := by
    have hcollapse :
        (∑ v : Y, ∑ q : X × Y,
          |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|) =
        ∑ v : Y, ∑ x : X, |p (s, (x, v)) - rightRevealModel μ p (s, (x, v))| / 2 := by
      simp [Fintype.sum_prod_type, abs_masked_inr]
    rw [hcollapse, Finset.sum_comm]
    simp [Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_mul]
  have hmass :
      (∑ z : (S × (X ⊕ Y)) × (X × Y), |maskedJoint p z - maskedModel μ p z|) =
      ((∑ z : S × (X × Y), |p z - leftRevealModel μ p z|) +
       (∑ z : S × (X × Y), |p z - rightRevealModel μ p z|)) / 2 := by
    calc
      _ = ∑ s : S,
          ((∑ u : X, ∑ q : X × Y, |maskedJoint p ((s, Sum.inl u), q) - maskedModel μ p ((s, Sum.inl u), q)|) +
           (∑ v : Y, ∑ q : X × Y, |maskedJoint p ((s, Sum.inr v), q) - maskedModel μ p ((s, Sum.inr v), q)|)) := by
        simp only [Fintype.sum_prod_type, Fintype.sum_sum_type]
      _ = ∑ s : S,
          ((∑ q : X × Y, |p (s, q) - leftRevealModel μ p (s, q)|) / 2 +
           (∑ q : X × Y, |p (s, q) - rightRevealModel μ p (s, q)|) / 2) := by
        simp_rw [hleft, hright]
      _ = _ := by
        simp [Fintype.sum_prod_type, div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul, add_mul]
  unfold Information.totalVariation
  rw [hmass]
  ring

theorem leftRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (leftRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (rightRevealModel μ p)]

theorem rightRevealModel_totalVariation_le (μ : Games.FiniteDistribution (X × Y))
    (p : S × (X × Y) → ℝ) :
    Information.totalVariation p (rightRevealModel μ p) ≤
      2 * Information.totalVariation (maskedJoint p) (maskedModel μ p) := by
  rw [masked_totalVariation_identity]
  linarith [Information.totalVariation_nonneg p (leftRevealModel μ p)]

end
end IndependentSetsGames.Foundations.Repetition

end OAI

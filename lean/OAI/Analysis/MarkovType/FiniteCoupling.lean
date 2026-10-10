import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace OAI

open scoped BigOperators

namespace MarkovSuperreflexivity

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v w

structure FiniteCoupling {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) where
  weight : A → B → ℝ
  nonneg : ∀ a b, 0 ≤ weight a b
  row_sum : ∀ a, ∑ b, weight a b = p a
  col_sum : ∀ b, ∑ a, weight a b = q b

namespace FiniteCoupling

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
variable {p : A → ℝ} {q : B → ℝ}

theorem weight_le_row (k : FiniteCoupling p q) (a : A) (b : B) :
    k.weight a b ≤ p a := by
  rw [← k.row_sum a]
  exact Finset.single_le_sum (fun j _ => k.nonneg a j) (Finset.mem_univ b)

theorem weight_le_col (k : FiniteCoupling p q) (a : A) (b : B) :
    k.weight a b ≤ q b := by
  rw [← k.col_sum b]
  exact Finset.single_le_sum (fun i _ => k.nonneg i b) (Finset.mem_univ a)

theorem weight_eq_zero_of_row (k : FiniteCoupling p q) {a : A}
    (h : p a = 0) (b : B) : k.weight a b = 0 :=
  le_antisymm (h ▸ k.weight_le_row a b) (k.nonneg a b)

theorem weight_eq_zero_of_col (k : FiniteCoupling p q) (a : A) {b : B}
    (h : q b = 0) : k.weight a b = 0 :=
  le_antisymm (h ▸ k.weight_le_col a b) (k.nonneg a b)

def transpose (k : FiniteCoupling p q) : FiniteCoupling q p where
  weight b a := k.weight a b
  nonneg b a := k.nonneg a b
  row_sum := k.col_sum
  col_sum := k.row_sum

def average (k l : FiniteCoupling p q) : FiniteCoupling p q where
  weight a b := (k.weight a b + l.weight a b) / 2
  nonneg a b := div_nonneg (add_nonneg (k.nonneg a b) (l.nonneg a b)) (by norm_num)
  row_sum a := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, k.row_sum, l.row_sum]
    ring
  col_sum b := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, k.col_sum, l.col_sum]
    ring

end FiniteCoupling

def finitePushforward {A : Type u} {T : Type v} [Fintype A]
    (p : A → ℝ) (f : A → T) (t : T) : ℝ :=
  ∑ a, if f a = t then p a else 0

theorem finitePushforward_nonneg {A : Type u} {T : Type v} [Fintype A]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → T) (t : T) :
    0 ≤ finitePushforward p f t := by
  classical
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hp a
  · exact le_rfl

theorem finitePushforward_sum {A : Type u} {T : Type v} [Fintype A] [Fintype T]
    (p : A → ℝ) (f : A → T) : ∑ t, finitePushforward p f t = ∑ a, p a := by
  classical
  simp only [finitePushforward]
  rw [Finset.sum_comm]
  simp

theorem weight_le_finitePushforward {A : Type u} {T : Type v} [Fintype A]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → T) (a : A) :
    p a ≤ finitePushforward p f (f a) := by
  classical
  have h := Finset.single_le_sum
    (s := Finset.univ) (f := fun b => if f b = f a then p b else 0)
    (fun b _ => by
      change 0 ≤ if f b = f a then p b else 0
      split_ifs
      · exact hp b
      · exact le_rfl) (Finset.mem_univ a)
  simpa [finitePushforward] using h

def finiteTotalVariation {A : Type u} [Fintype A] (p q : A → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

def finiteOverlap {A : Type u} (p q : A → ℝ) (a : A) : ℝ := min (p a) (q a)

def finiteResidualMass {A : Type u} [Fintype A] (p q : A → ℝ) : ℝ :=
  1 - ∑ a, finiteOverlap p q a

theorem residual_left_sum {A : Type u} [Fintype A] (p q : A → ℝ)
    (hp : ∑ a, p a = 1) :
    ∑ a, (p a - finiteOverlap p q a) = finiteResidualMass p q := by
  rw [Finset.sum_sub_distrib, hp]
  rfl

theorem residual_right_sum {A : Type u} [Fintype A] (p q : A → ℝ)
    (hq : ∑ a, q a = 1) :
    ∑ a, (q a - finiteOverlap p q a) = finiteResidualMass p q := by
  rw [Finset.sum_sub_distrib, hq]
  rfl

theorem finiteResidualMass_nonneg {A : Type u} [Fintype A] (p q : A → ℝ)
    (hp : ∑ a, p a = 1) : 0 ≤ finiteResidualMass p q := by
  rw [← residual_left_sum p q hp]
  exact Finset.sum_nonneg (fun a _ => sub_nonneg.mpr (min_le_left _ _))

theorem residual_product_zero {A : Type u} (p q : A → ℝ) (a : A) :
    (p a - finiteOverlap p q a) * (q a - finiteOverlap p q a) = 0 := by
  rcases le_total (p a) (q a) with h | h
  · simp [finiteOverlap, min_eq_left h]
  · simp [finiteOverlap, min_eq_right h]

theorem finiteTotalVariation_eq_residual {A : Type u} [Fintype A]
    (p q : A → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    finiteTotalVariation p q = finiteResidualMass p q := by
  have habs (a : A) : |p a - q a| = p a + q a - 2 * finiteOverlap p q a := by
    rcases le_total (p a) (q a) with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      simp only [finiteOverlap, min_eq_left h]
      ring
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      simp only [finiteOverlap, min_eq_right h]
      ring
  simp only [finiteTotalVariation, habs, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, hp, hq, finiteResidualMass]
  rw [← Finset.mul_sum]
  ring

def maximalFiniteCouplingWeight {A : Type u} [Fintype A]
    (p q : A → ℝ) (a b : A) : ℝ :=
  (if a = b then finiteOverlap p q a else 0) +
    (p a - finiteOverlap p q a) * (q b - finiteOverlap p q b) /
      finiteResidualMass p q

theorem maximalFiniteCouplingWeight_nonneg {A : Type u} [Fintype A]
    {p q : A → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (a b : A) :
    0 ≤ maximalFiniteCouplingWeight p q a b := by
  classical
  apply add_nonneg
  · split_ifs
    · exact le_min (hp a) (hq a)
    · exact le_rfl
  · exact div_nonneg
      (mul_nonneg (sub_nonneg.mpr (min_le_left _ _))
        (sub_nonneg.mpr (min_le_right _ _)))
      (finiteResidualMass_nonneg p q hpsum)

theorem maximalFiniteCouplingWeight_row {A : Type u} [Fintype A]
    (p q : A → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) (a : A) :
    ∑ b, maximalFiniteCouplingWeight p q a b = p a := by
  classical
  have hrow : ∑ b, maximalFiniteCouplingWeight p q a b =
      finiteOverlap p q a + (p a - finiteOverlap p q a) *
        finiteResidualMass p q / finiteResidualMass p q := by
    simp only [maximalFiniteCouplingWeight, Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.mul_sum, residual_right_sum p q hq]
    simp
  rw [hrow]
  by_cases hd : finiteResidualMass p q = 0
  · have ha : p a - finiteOverlap p q a = 0 := by
      apply le_antisymm _ (sub_nonneg.mpr (min_le_left _ _))
      have hle := Finset.single_le_sum
        (fun b (_ : b ∈ (Finset.univ : Finset A)) =>
          sub_nonneg.mpr (min_le_left (p b) (q b))) (Finset.mem_univ a)
      change p a - finiteOverlap p q a ≤ ∑ b, (p b - finiteOverlap p q b) at hle
      rw [residual_left_sum p q hp, hd] at hle
      exact hle
    rw [hd]
    simp only [mul_zero, zero_div, add_zero]
    linarith
  · rw [mul_div_cancel_right₀ _ hd]
    ring

theorem maximalFiniteCouplingWeight_transpose {A : Type u} [Fintype A]
    (p q : A → ℝ) (a b : A) :
    maximalFiniteCouplingWeight q p b a = maximalFiniteCouplingWeight p q a b := by
  classical
  have hover : finiteResidualMass q p = finiteResidualMass p q := by
    simp only [finiteResidualMass, finiteOverlap, min_comm]
  simp only [maximalFiniteCouplingWeight, hover, finiteOverlap]
  by_cases hab : a = b
  · subst b
    simp only [min_comm]
    ring
  · simp only [ite_eq_right hab, ite_eq_right (Ne.symm hab), min_comm, zero_add]
    ring

def maximalFiniteCoupling {A : Type u} [Fintype A]
    (p q : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1) : FiniteCoupling p q where
  weight := maximalFiniteCouplingWeight p q
  nonneg := maximalFiniteCouplingWeight_nonneg hp hq hpsum
  row_sum := maximalFiniteCouplingWeight_row p q hpsum hqsum
  col_sum b := by
    simp_rw [← maximalFiniteCouplingWeight_transpose p q]
    exact maximalFiniteCouplingWeight_row q p hqsum hpsum b

theorem maximalFiniteCoupling_diagonal {A : Type u} [Fintype A]
    (p q : A → ℝ) (a : A) :
    maximalFiniteCouplingWeight p q a a = finiteOverlap p q a := by
  classical
  simp [maximalFiniteCouplingWeight, residual_product_zero]

theorem maximalFiniteCoupling_matching_mass {A : Type u} [Fintype A]
    (p q : A → ℝ) (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    ∑ a, maximalFiniteCouplingWeight p q a a = 1 - finiteTotalVariation p q := by
  simp_rw [maximalFiniteCoupling_diagonal]
  rw [finiteTotalVariation_eq_residual p q hp hq]
  simp only [finiteResidualMass]
  ring

theorem finiteCoupling_matching_mass_le {A : Type u} [Fintype A]
    {p q : A → ℝ} (k : FiniteCoupling p q)
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    ∑ a, k.weight a a ≤ 1 - finiteTotalVariation p q := by
  rw [← maximalFiniteCoupling_matching_mass p q hp hq]
  apply Finset.sum_le_sum
  intro a _
  rw [maximalFiniteCoupling_diagonal]
  exact le_min (k.weight_le_row a a) (k.weight_le_col a a)

def finiteConditional {A : Type u} {T : Type v} [Fintype A]
    (p : A → ℝ) (f : A → T) (t : T) (a : A) : ℝ :=
  if finitePushforward p f t = 0 then p a
  else if f a = t then p a / finitePushforward p f t else 0

theorem finiteConditional_nonneg {A : Type u} {T : Type v} [Fintype A]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → T) (t : T) (a : A) :
    0 ≤ finiteConditional p f t a := by
  classical
  unfold finiteConditional
  split_ifs
  · exact hp a
  · exact div_nonneg (hp a) (finitePushforward_nonneg hp f t)
  · exact le_rfl

theorem finiteConditional_sum {A : Type u} {T : Type v} [Fintype A]
    (p : A → ℝ) (f : A → T) (hpsum : ∑ a, p a = 1) (t : T) :
    ∑ a, finiteConditional p f t a = 1 := by
  classical
  by_cases ht : finitePushforward p f t = 0
  · simpa [finiteConditional, ht] using hpsum
  · simp only [finiteConditional, ht, ite_false]
    have hterm (a : A) :
        (if f a = t then p a / finitePushforward p f t else 0) =
        (if f a = t then p a else 0) / finitePushforward p f t := by
      split_ifs <;> simp
    simp_rw [hterm]
    rw [← Finset.sum_div]
    exact div_self ht

theorem finiteConditional_weighted {A : Type u} {T : Type v} [Fintype A]
    {p : A → ℝ} (hp : ∀ a, 0 ≤ p a) (f : A → T) (t : T) (a : A) :
    finitePushforward p f t * finiteConditional p f t a =
      if f a = t then p a else 0 := by
  classical
  by_cases ht : finitePushforward p f t = 0
  · have hzero : f a = t → p a = 0 := by
      intro ha
      have hle := weight_le_finitePushforward hp f a
      rw [ha, ht] at hle
      exact le_antisymm hle (hp a)
    by_cases ha : f a = t
    · simp [finiteConditional, ht, ha, hzero ha]
    · simp [finiteConditional, ht, ha]
  · by_cases ha : f a = t
    · simp only [finiteConditional, ht, ite_false, ite_eq_left ha]
      field_simp
    · simp [finiteConditional, ht, ha]

theorem finiteConditional_reconstruct {A : Type u} {T : Type v}
    [Fintype A] [Fintype T] {p : A → ℝ} (hp : ∀ a, 0 ≤ p a)
    (f : A → T) (a : A) :
    ∑ t, finitePushforward p f t * finiteConditional p f t a = p a := by
  classical
  simp_rw [finiteConditional_weighted hp]
  simp

def liftFiniteCouplingWeight {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (k : FiniteCoupling (finitePushforward p f) (finitePushforward q g))
    (a : A) (b : B) : ℝ :=
  ∑ t, ∑ u, k.weight t u * finiteConditional p f t a * finiteConditional q g u b

def liftFiniteCoupling {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ b, q b = 1)
    (k : FiniteCoupling (finitePushforward p f) (finitePushforward q g)) :
    FiniteCoupling p q where
  weight := liftFiniteCouplingWeight p q f g k
  nonneg a b := Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun u _ =>
    mul_nonneg (mul_nonneg (k.nonneg t u) (finiteConditional_nonneg hp f t a))
      (finiteConditional_nonneg hq g u b)
  row_sum a := by
    unfold liftFiniteCouplingWeight
    rw [Finset.sum_comm]
    calc
      _ = ∑ t, ∑ u, ∑ b,
          k.weight t u * finiteConditional p f t a * finiteConditional q g u b := by
        apply Finset.sum_congr rfl
        intro t _
        exact Finset.sum_comm
      _ = ∑ t, ∑ u, k.weight t u * finiteConditional p f t a := by
        simp_rw [← Finset.mul_sum, finiteConditional_sum q g hqsum, mul_one]
      _ = ∑ t, finitePushforward p f t * finiteConditional p f t a := by
        simp_rw [← Finset.sum_mul, k.row_sum]
      _ = p a := finiteConditional_reconstruct hp f a
  col_sum b := by
    unfold liftFiniteCouplingWeight
    rw [Finset.sum_comm]
    calc
      _ = ∑ t, ∑ u, ∑ a,
          k.weight t u * finiteConditional p f t a * finiteConditional q g u b := by
        apply Finset.sum_congr rfl
        intro t _
        exact Finset.sum_comm
      _ = ∑ t, ∑ u, k.weight t u * finiteConditional q g u b := by
        simp_rw [← Finset.sum_mul, ← Finset.mul_sum,
          finiteConditional_sum p f hpsum, mul_one]
      _ = ∑ u, ∑ t, k.weight t u * finiteConditional q g u b := Finset.sum_comm
      _ = ∑ u, finitePushforward q g u * finiteConditional q g u b := by
        simp_rw [← Finset.sum_mul, k.col_sum]
      _ = q b := finiteConditional_reconstruct hq g b

theorem finiteConditional_feature_sum {A : Type u} {T : Type v} [Fintype A]
    (p : A → ℝ) (f : A → T) (hpsum : ∑ a, p a = 1)
    {t : T} (ht : finitePushforward p f t ≠ 0) (H : T → ℝ) :
    ∑ a, finiteConditional p f t a * H (f a) = H t := by
  classical
  calc
    _ = ∑ a, finiteConditional p f t a * H t := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : f a = t
      · rw [ha]
      · simp [finiteConditional, ht, ha]
    _ = H t := by rw [← Finset.sum_mul, finiteConditional_sum p f hpsum, one_mul]

theorem finiteCoupling_conditional_feature_sum {A : Type u} {T : Type v}
    {U : Type w} [Fintype A] [Fintype T] [Fintype U]
    (p : A → ℝ) (f : A → T) (hpsum : ∑ a, p a = 1) {q : U → ℝ}
    (k : FiniteCoupling (finitePushforward p f) q) (t : T) (u : U) (H : T → ℝ) :
    k.weight t u * (∑ a, finiteConditional p f t a * H (f a)) =
      k.weight t u * H t := by
  by_cases ht : finitePushforward p f t = 0
  · rw [k.weight_eq_zero_of_row ht u]
    simp
  · rw [finiteConditional_feature_sum p f hpsum ht H]

theorem liftFiniteCoupling_feature_expectation {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ b, q b = 1)
    (k : FiniteCoupling (finitePushforward p f) (finitePushforward q g)) (H : T → T → ℝ) :
    (∑ a, ∑ b, liftFiniteCouplingWeight p q f g k a b * H (f a) (g b)) =
      ∑ t, ∑ u, k.weight t u * H t u := by
  classical
  have hentry (t u : T) :
      (∑ a, ∑ b, (k.weight t u * finiteConditional p f t a *
        finiteConditional q g u b) * H (f a) (g b)) = k.weight t u * H t u := by
    by_cases ht : finitePushforward p f t = 0
    · simp [k.weight_eq_zero_of_row ht u]
    by_cases hu : finitePushforward q g u = 0
    · simp [k.weight_eq_zero_of_col t hu]
    calc
      _ = k.weight t u * (∑ a, finiteConditional p f t a *
          (∑ b, finiteConditional q g u b * H (f a) (g b))) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = k.weight t u * H t u := by
        simp_rw [finiteConditional_feature_sum q g hqsum hu]
        rw [finiteConditional_feature_sum p f hpsum ht (fun v => H v u)]
  calc
    _ = ∑ a, ∑ b, ∑ t, ∑ u,
        (k.weight t u * finiteConditional p f t a * finiteConditional q g u b) *
          H (f a) (g b) := by simp only [liftFiniteCouplingWeight, Finset.sum_mul]
    _ = ∑ t, ∑ u, ∑ a, ∑ b,
        (k.weight t u * finiteConditional p f t a * finiteConditional q g u b) *
          H (f a) (g b) := by
      calc
        _ = ∑ a, ∑ t, ∑ b, ∑ u,
            (k.weight t u * finiteConditional p f t a * finiteConditional q g u b) *
              H (f a) (g b) := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = ∑ t, ∑ a, ∑ b, ∑ u,
            (k.weight t u * finiteConditional p f t a * finiteConditional q g u b) *
              H (f a) (g b) := Finset.sum_comm
        _ = ∑ t, ∑ a, ∑ u, ∑ b,
            (k.weight t u * finiteConditional p f t a * finiteConditional q g u b) *
              H (f a) (g b) := by
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro t _
          exact Finset.sum_comm
    _ = ∑ t, ∑ u, k.weight t u * H t u := by simp_rw [hentry]

theorem liftFiniteCoupling_matching_mass {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ b, q b = 1)
    (k : FiniteCoupling (finitePushforward p f) (finitePushforward q g)) :
    (∑ a, ∑ b, if f a = g b then liftFiniteCouplingWeight p q f g k a b else 0) =
      ∑ t, k.weight t t := by
  classical
  have h := liftFiniteCoupling_feature_expectation p q f g hpsum hqsum k
    (fun t u => if t = u then 1 else 0)
  simpa [mul_ite] using h

def maximalFeatureCoupling {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ b, q b = 1) : FiniteCoupling p q :=
  liftFiniteCoupling p q f g hp hq hpsum hqsum
    (maximalFiniteCoupling (finitePushforward p f) (finitePushforward q g)
      (finitePushforward_nonneg hp f) (finitePushforward_nonneg hq g)
      ((finitePushforward_sum p f).trans hpsum) ((finitePushforward_sum q g).trans hqsum))

theorem maximalFeatureCoupling_matching_mass {A : Type u} {B : Type v} {T : Type w}
    [Fintype A] [Fintype B] [Fintype T]
    (p : A → ℝ) (q : B → ℝ) (f : A → T) (g : B → T)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ b, q b = 1) :
    (∑ a, ∑ b, if f a = g b then
      (maximalFeatureCoupling p q f g hp hq hpsum hqsum).weight a b else 0) =
      1 - finiteTotalVariation (finitePushforward p f) (finitePushforward q g) := by
  classical
  unfold maximalFeatureCoupling
  change (∑ a, ∑ b, if f a = g b then liftFiniteCouplingWeight p q f g _ a b else 0) = _
  rw [liftFiniteCoupling_matching_mass p q f g hpsum hqsum]
  exact maximalFiniteCoupling_matching_mass _ _
    ((finitePushforward_sum p f).trans hpsum) ((finitePushforward_sum q g).trans hqsum)

end

end MarkovSuperreflexivity

end OAI

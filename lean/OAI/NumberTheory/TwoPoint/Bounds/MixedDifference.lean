import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling

namespace OAI

/-!
# Exact singleton centering

The product sampling law is kept fixed. Forcing a coordinate overwrites
that coordinate of the same sample, rather than drawing fresh coordinates
at different sites. This is the algebraic part of `q:mixed-difference`.
-/

namespace TwoPointCorrelations

open Finset

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

def forceCoordinates (S : Finset ι) (a x : ι → A) : ι → A := S.piecewise a x

omit [Fintype ι] [Fintype A] [DecidableEq A] in
@[simp] lemma forceCoordinates_apply (S : Finset ι) (a x : ι → A) (i : ι) :
    forceCoordinates S a x i = if i ∈ S then a i else x i := rfl

noncomputable def mixedDifference (a : ι → A) (F : (ι → A) → ℝ) (x : ι → A) : ℝ :=
  ∑ S : Finset ι, (-1 : ℝ) ^ Sᶜ.card * F (forceCoordinates S a x)

namespace FiniteLaw

omit [DecidableEq A] in
lemma average_const_mul (μ : FiniteLaw A) (c : ℝ) (f : A → ℝ) :
    μ.average (fun x => c * f x) = c * μ.average f := by
  simp only [average, Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  ring

omit [DecidableEq A] in
lemma abs_average_le (μ : FiniteLaw A) (f : A → ℝ) :
    |μ.average f| ≤ μ.average (fun x => |f x|) := by
  unfold average
  apply (abs_sum_le_sum_abs _ _).trans_eq
  apply sum_congr rfl
  intro x _
  rw [abs_mul, abs_of_nonneg (μ.nonneg x)]

lemma average_singleton_pin (μ : FiniteLaw A) (a : A) (F : A → ℝ) :
    μ.average (fun x => (if x = a then (1 : ℝ) else 0) * F x) = μ.weight a * F a := by
  simp [average]

lemma singleton_centering (μ : FiniteLaw A) (a : A) (F : A → ℝ) :
    μ.average (fun x => ((if x = a then (1 : ℝ) else 0) - μ.weight a) * F x) =
      μ.weight a * μ.average (fun x => F a - F x) := by
  have hexp : μ.average (fun x => ((if x = a then (1 : ℝ) else 0) - μ.weight a) * F x) =
      μ.average (fun x => (if x = a then (1 : ℝ) else 0) * F x) - μ.weight a * μ.average F := by
    simp only [average, mul_sub, sub_mul, sum_sub_distrib, mul_sum]
    congr 1
    apply sum_congr rfl
    intro x _
    ring
  rw [hexp, average_singleton_pin]
  have hsub : μ.average (fun x => F a - F x) = F a - μ.average F := by
    simp only [average, mul_sub, sum_sub_distrib, ← sum_mul, μ.total, one_mul]
  rw [hsub]
  ring

lemma independent_average_pin (μ : ι → FiniteLaw A) (a : ι → A) (F : (ι → A) → ℝ) :
    (independent μ).average (fun x => (∏ i, if x i = a i then (1 : ℝ) else 0) * F x) =
      (∏ i, (μ i).weight (a i)) * F a := by
  have hpin (x : ι → A) : (∏ i, if x i = a i then (1 : ℝ) else 0) =
      if x = a then (1 : ℝ) else 0 := by
    by_cases hx : x = a
    · simp [hx]
    · have hn : ¬∀ i, x i = a i := fun h => hx (funext h)
      simp [Fintype.prod_boole, hx, hn]
  simp only [hpin]
  exact average_singleton_pin (independent μ) a F

omit [Fintype ι] [Fintype A] [DecidableEq A] in
lemma force_join (S : Finset ι) (a : ι → A)
    (x : S → A) (y : {i // i ∉ S} → A) :
    forceCoordinates S a (joinCoordinates S x y) =
      joinCoordinates S (fun i : S => a i) y := by
  funext i
  by_cases hi : i ∈ S <;> simp [forceCoordinates, piecewise, joinCoordinates, hi]

/-- Forcing a selected set has precisely the product mass of its forced
atoms, even when the observable depends on every other coordinate. -/
theorem independent_forcing (μ : ι → FiniteLaw A) (S : Finset ι)
    (a : ι → A) (F : (ι → A) → ℝ) :
    (independent μ).average (fun x =>
      (∏ i ∈ S, if x i = a i then (1 : ℝ) else 0) * F x) =
      (∏ i ∈ S, (μ i).weight (a i)) *
        (independent μ).average (fun x => F (forceCoordinates S a x)) := by
  rw [independent_average_split μ S]
  have hin (y : {i // i ∉ S} → A) :
      (independent (fun i : S => μ i)).average (fun x =>
        (∏ i ∈ S, if joinCoordinates S x y i = a i then (1 : ℝ) else 0) *
          F (joinCoordinates S x y)) =
        (∏ i ∈ S, (μ i).weight (a i)) * F (joinCoordinates S (fun i : S => a i) y) := by
    have hpin := independent_average_pin (fun i : S => μ i) (fun i : S => a i)
      (fun x => F (joinCoordinates S x y))
    have hp (x : S → A) :
        (∏ i ∈ S, if joinCoordinates S x y i = a i then (1 : ℝ) else 0) =
          ∏ i : S, if x i = a i then (1 : ℝ) else 0 := by
      rw [← Finset.prod_coe_sort S]
      simp only [joinCoordinates_mem]
    simp_rw [hp]
    rw [← Finset.prod_coe_sort S]
    exact hpin
  simp_rw [hin]
  rw [average_const_mul, independent_average_split μ S (fun x => F (forceCoordinates S a x))]
  congr 1
  apply congrArg (independent (fun i : {i // i ∉ S} => μ i)).average
  funext y
  simp only [force_join, average_const]

/-- Centering every singleton is exactly the alternating sum over forcing
subsets, before any absolute value is taken. -/
theorem exact_mixed_centering (μ : ι → FiniteLaw A) (a : ι → A)
    (F : (ι → A) → ℝ) :
    (independent μ).average (fun x =>
      (∏ i, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x) =
      (∏ i, (μ i).weight (a i)) * (independent μ).average (mixedDifference a F) := by
  have hexp (x : ι → A) :
      (∏ i, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) =
      ∑ S : Finset ι, (-1 : ℝ) ^ Sᶜ.card * (∏ i ∈ Sᶜ, (μ i).weight (a i)) *
        ∏ i ∈ S, if x i = a i then (1 : ℝ) else 0 := by
    simp only [sub_eq_add_neg, Fintype.prod_add, prod_neg]
    apply sum_congr rfl
    intro S _
    ring
  have hm : (independent μ).average (mixedDifference a F) =
      ∑ S : Finset ι, (-1 : ℝ) ^ Sᶜ.card *
        (independent μ).average (fun x => F (forceCoordinates S a x)) := by
    unfold mixedDifference
    rw [average_sum]
    simp_rw [average_const_mul]
  simp_rw [hexp, sum_mul]
  rw [average_sum, hm, mul_sum]
  apply sum_congr rfl
  intro S _
  have hc : (∏ i ∈ Sᶜ, (μ i).weight (a i)) *
      (∏ i ∈ S, (μ i).weight (a i)) = ∏ i, (μ i).weight (a i) := by
    rw [mul_comm, prod_mul_prod_compl]
  calc
    _ = ((-1 : ℝ) ^ Sᶜ.card * (∏ i ∈ Sᶜ, (μ i).weight (a i))) *
        (independent μ).average (fun x =>
          (∏ i ∈ S, if x i = a i then (1 : ℝ) else 0) * F x) := by
      rw [← average_const_mul]
      congr 1
      funext x
      ring
    _ = ((-1 : ℝ) ^ Sᶜ.card * (∏ i ∈ Sᶜ, (μ i).weight (a i))) *
        ((∏ i ∈ S, (μ i).weight (a i)) *
          (independent μ).average (fun x => F (forceCoordinates S a x))) := by
      rw [independent_forcing]
    _ = (-1 : ℝ) ^ Sᶜ.card *
        ((∏ i ∈ Sᶜ, (μ i).weight (a i)) * (∏ i ∈ S, (μ i).weight (a i))) *
          (independent μ).average (fun x => F (forceCoordinates S a x)) := by ring
    _ = _ := by rw [hc]; ring

theorem mixed_centering_bound (μ : ι → FiniteLaw A) (a : ι → A)
    (F : (ι → A) → ℝ) :
    |(independent μ).average (fun x =>
      (∏ i, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x)| ≤
      (∏ i, (μ i).weight (a i)) *
        (independent μ).average (fun x => |mixedDifference a F x|) := by
  rw [exact_mixed_centering, abs_mul, abs_of_nonneg
    (prod_nonneg (fun i _ => (μ i).nonneg _))]
  exact mul_le_mul_of_nonneg_left (abs_average_le _ _)
    (prod_nonneg (fun i _ => (μ i).nonneg _))

/-- A designated trace term: lit nonsingletons are pinned and singleton
coordinates are centered. The scalar includes all unlit signs and every
factor independent of these residue draws. -/
theorem exact_designated_centering {κ C : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype C] [DecidableEq C]
    (μ : ι → FiniteLaw A) (ν : κ → FiniteLaw C) (a : ι → A) (b : κ → C)
    (s : ℝ) (F : (ι → A) → (κ → C) → ℝ) :
    (independent μ).average (fun x => (independent ν).average (fun y =>
      s * (∏ i, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) *
        (∏ j, if y j = b j then (1 : ℝ) else 0) * F x y)) =
      s * (∏ j, (ν j).weight (b j)) * (∏ i, (μ i).weight (a i)) *
        (independent μ).average (mixedDifference a (fun x => F x b)) := by
  have hpin (x : ι → A) :
      (independent ν).average (fun y =>
        s * (∏ i, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) *
          (∏ j, if y j = b j then (1 : ℝ) else 0) * F x y) =
        s * (∏ j, (ν j).weight (b j)) *
          ((∏ i, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i))) * F x b) := by
    calc
      _ = (s * (∏ i, ((if x i = a i then (1 : ℝ) else 0) - (μ i).weight (a i)))) *
          (independent ν).average (fun y =>
            (∏ j, if y j = b j then (1 : ℝ) else 0) * F x y) := by
        rw [← average_const_mul]
        congr 1
        funext y
        ring
      _ = _ := by rw [independent_average_pin]; ring
  simp_rw [hpin]
  rw [average_const_mul, exact_mixed_centering]
  ring

end FiniteLaw

omit [Fintype A] [DecidableEq A] in
theorem abs_mixedDifference_le (a : ι → A) (F : (ι → A) → ℝ)
    (hF : ∀ x, |F x| ≤ 1) (x : ι → A) :
    |mixedDifference a F x| ≤ 2 ^ Fintype.card ι := by
  unfold mixedDifference
  calc
    _ ≤ ∑ S : Finset ι, |(-1 : ℝ) ^ Sᶜ.card * F (forceCoordinates S a x)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S : Finset ι, (1 : ℝ) := by
      apply sum_le_sum
      intro S _
      simpa only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] using
        hF (forceCoordinates S a x)
    _ = _ := by simp

omit [Fintype A] [DecidableEq A] in
/-- A nonzero alternating difference has a nonzero hybrid term. -/
theorem exists_forced_value_ne_zero (a : ι → A) (F : (ι → A) → ℝ) (x : ι → A)
    (h : mixedDifference a F x ≠ 0) :
    ∃ S : Finset ι, F (forceCoordinates S a x) ≠ 0 := by
  by_contra! hc
  apply h
  unfold mixedDifference
  apply sum_eq_zero
  intro S _
  rw [hc S, mul_zero]

end TwoPointCorrelations

end OAI

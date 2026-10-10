import Mathlib

namespace OAI

/-!
# FiniteLaw

Finite laws, common-reference total variation, Hellinger affinity, overlap, scalar moments, hypercontractivity, clipping, and leaf densities.
-/

open scoped ENNReal
noncomputable section

noncomputable section
namespace TraceReconstruction

/-- Finite probability laws used for the exact statistical transfer. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

def tv (P Q : FiniteLaw α) : ℝ := (1 / 2 : ℝ) * ∑ a, |P.mass a - Q.mass a|
def hellingerSq (P Q : FiniteLaw α) : ℝ :=
  ∑ a, (Real.sqrt (P.mass a) - Real.sqrt (Q.mass a)) ^ 2
def affinity (P Q : FiniteLaw α) : ℝ :=
  ∑ a, Real.sqrt (P.mass a) * Real.sqrt (Q.mass a)

theorem affinity_nonneg (P Q : FiniteLaw α) : 0 ≤ affinity P Q := by
  apply Finset.sum_nonneg
  intro a _; positivity

theorem hellingerSq_nonneg (P Q : FiniteLaw α) : 0 ≤ hellingerSq P Q := by
  apply Finset.sum_nonneg
  intro a _; positivity

theorem hellingerSq_eq (P Q : FiniteLaw α) :
    hellingerSq P Q = 2 - 2 * affinity P Q := by
  unfold hellingerSq affinity
  calc
    _ = (∑ a, P.mass a) + (∑ a, Q.mass a) - 2 * ∑ a,
        Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      have hp := Real.sq_sqrt (P.nonneg a)
      have hq := Real.sq_sqrt (Q.nonneg a)
      nlinarith only [hp, hq]
    _ = _ := by rw [P.total, Q.total]; ring

theorem affinity_le_one (P Q : FiniteLaw α) : affinity P Q ≤ 1 := by
  have h := hellingerSq_nonneg P Q
  rw [hellingerSq_eq] at h
  linarith

theorem tv_nonneg (P Q : FiniteLaw α) : 0 ≤ tv P Q := by unfold tv; positivity

theorem tv_sq_le_hellingerSq (P Q : FiniteLaw α) :
    tv P Q ^ 2 ≤ hellingerSq P Q := by
  have hpoint (a : α) : |P.mass a - Q.mass a| ^ 2 ≤
      (Real.sqrt (P.mass a) - Real.sqrt (Q.mass a)) ^ 2 *
        (Real.sqrt (P.mass a) + Real.sqrt (Q.mass a)) ^ 2 := by
    rw [sq_abs]
    have hp := Real.sq_sqrt (P.nonneg a)
    have hq := Real.sq_sqrt (Q.nonneg a)
    nlinarith only [hp, hq, sq_nonneg (P.mass a - Q.mass a)]
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ)
    (r := fun a => |P.mass a - Q.mass a|)
    (f := fun a => (Real.sqrt (P.mass a) - Real.sqrt (Q.mass a)) ^ 2)
    (g := fun a => (Real.sqrt (P.mass a) + Real.sqrt (Q.mass a)) ^ 2)
    (fun a _ => sq_nonneg _) (fun a _ => sq_nonneg _) (fun a _ => hpoint a)
  have hplus : (∑ a, (Real.sqrt (P.mass a) + Real.sqrt (Q.mass a)) ^ 2) =
      2 + 2 * affinity P Q := by
    unfold affinity
    calc
      _ = (∑ a, P.mass a) + (∑ a, Q.mass a) + 2 * ∑ a,
          Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        have hp := Real.sq_sqrt (P.nonneg a)
        have hq := Real.sq_sqrt (Q.nonneg a)
        nlinarith only [hp, hq]
      _ = _ := by rw [P.total, Q.total]; ring
  rw [hplus] at h
  change (∑ a, |P.mass a - Q.mass a|) ^ 2 ≤ hellingerSq P Q * (2 + 2 * affinity P Q) at h
  have hbound := mul_le_mul_of_nonneg_left (affinity_le_one P Q) (hellingerSq_nonneg P Q)
  unfold tv
  nlinarith only [h, hbound]

theorem tv_le_sqrt_hellingerSq (P Q : FiniteLaw α) :
    tv P Q ≤ Real.sqrt (hellingerSq P Q) := by
  have h := tv_sq_le_hellingerSq P Q
  have hs := Real.sq_sqrt (hellingerSq_nonneg P Q)
  have hn := Real.sqrt_nonneg (hellingerSq P Q)
  nlinarith only [h, hs, hn]

def product (P : FiniteLaw α) (m : ℕ) : FiniteLaw (Fin m → α) where
  mass a := ∏ j, P.mass (a j)
  nonneg a := Finset.prod_nonneg fun j _ => P.nonneg (a j)
  total := by
    rw [← Fintype.prod_sum]
    simp [P.total]

theorem affinity_product (P Q : FiniteLaw α) (m : ℕ) :
    affinity (P.product m) (Q.product m) = affinity P Q ^ m := by
  unfold affinity product
  simp only
  have hexp (a : Fin m → α) :
      Real.sqrt (∏ j, P.mass (a j)) * Real.sqrt (∏ j, Q.mass (a j)) =
        ∏ j, (Real.sqrt (P.mass (a j)) * Real.sqrt (Q.mass (a j))) := by
    rw [Real.sqrt_prod _ (fun j _ => P.nonneg (a j)),
      Real.sqrt_prod _ (fun j _ => Q.nonneg (a j)), Finset.prod_mul_distrib]
  simp_rw [hexp]
  rw [← Fintype.prod_sum (fun (_ : Fin m) a => Real.sqrt (P.mass a) * Real.sqrt (Q.mass a))]
  simp

theorem hellingerSq_product_le (P Q : FiniteLaw α) (m : ℕ) :
    hellingerSq (P.product m) (Q.product m) ≤ (m : ℝ) * hellingerSq P Q := by
  rw [hellingerSq_eq, affinity_product, hellingerSq_eq]
  have ha := affinity_nonneg P Q
  have hb := affinity_le_one P Q
  have hpow : 1 - affinity P Q ^ m ≤ (m : ℝ) * (1 - affinity P Q) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have hmul := mul_le_mul_of_nonneg_right ih ha
      have hm : (0 : ℝ) ≤ (m : ℝ) * (1 - affinity P Q) := by positivity
      have hmon := mul_le_mul_of_nonneg_left hb hm
      nlinarith only [hmul, hmon]
  linarith


theorem sqrt_sub_one_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t - 1) ^ 2 ≤ (t - 1) ^ 2 := by
  have hs2 := Real.sq_sqrt ht
  have hprod := mul_nonneg (Real.sqrt_nonneg t)
    (mul_nonneg (show 0 ≤ Real.sqrt t + 2 by positivity) (sq_nonneg (Real.sqrt t - 1)))
  conv_rhs => rw [← hs2]
  nlinarith only [hprod]

theorem hellingerSq_le_score (P Q : FiniteLaw α) (Z : α → ℝ)
    (hZ : ∀ a, Q.mass a = P.mass a * (1 + Z a)) :
    hellingerSq P Q ≤ ∑ a, P.mass a * Z a ^ 2 := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hp0 : P.mass a = 0
  · have hq0 : Q.mass a = 0 := by rw [hZ, hp0, zero_mul]
    simp [hp0, hq0]
  have hp : 0 < P.mass a := lt_of_le_of_ne (P.nonneg a) (Ne.symm hp0)
  have ht : 0 ≤ 1 + Z a := by
    have hq := Q.nonneg a
    rw [hZ] at hq
    exact nonneg_of_mul_nonneg_right hq hp
  have hs := sqrt_sub_one_sq_le ht
  have hmul := mul_le_mul_of_nonneg_left hs (P.nonneg a)
  have hp2 := Real.sq_sqrt (P.nonneg a)
  rw [hZ, Real.sqrt_mul (P.nonneg a)]
  calc
    _ = P.mass a * (Real.sqrt (1 + Z a) - 1) ^ 2 := by
      calc
        _ = Real.sqrt (P.mass a) ^ 2 * (Real.sqrt (1 + Z a) - 1) ^ 2 := by ring
        _ = _ := by rw [hp2]
    _ ≤ P.mass a * ((1 + Z a) - 1) ^ 2 := hmul
    _ = _ := by ring

theorem tv_product_le_sqrt_score (P Q : FiniteLaw α) (Z : α → ℝ)
    (hZ : ∀ a, Q.mass a = P.mass a * (1 + Z a)) (m : ℕ) :
    tv (P.product m) (Q.product m) ≤ Real.sqrt ((m : ℝ) * ∑ a, P.mass a * Z a ^ 2) := by
  apply (tv_le_sqrt_hellingerSq _ _).trans
  apply Real.sqrt_le_sqrt
  exact (hellingerSq_product_le P Q m).trans
    (mul_le_mul_of_nonneg_left (hellingerSq_le_score P Q Z hZ) (by positivity))

def bind (P : FiniteLaw α) (K : α → FiniteLaw β) : FiniteLaw β where
  mass b := ∑ a, P.mass a * (K a).mass b
  nonneg b := Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) ((K a).nonneg b)
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (K _).total, mul_one]
    exact P.total

theorem tv_bind_le (P Q : FiniteLaw α) (K : α → FiniteLaw β) :
    tv (P.bind K) (Q.bind K) ≤ tv P Q := by
  unfold tv bind
  simp only
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ = ∑ b, |∑ a, (P.mass a - Q.mass a) * (K a).mass b| := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _; ring
    _ ≤ ∑ b, ∑ a, |(P.mass a - Q.mass a) * (K a).mass b| :=
      Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |P.mass a - Q.mass a| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [abs_mul, abs_of_nonneg ((K a).nonneg _), ← Finset.mul_sum, (K a).total, mul_one]

theorem tv_triangle (P Q R : FiniteLaw α) : tv P R ≤ tv P Q + tv Q R := by
  unfold tv
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro a _
  exact abs_sub_le _ _ _

theorem tv_symm (P Q : FiniteLaw α) : tv P Q = tv Q P := by
  unfold tv
  congr 1
  apply Finset.sum_congr rfl
  intro a _; exact abs_sub_comm _ _

theorem expectation_diff_le_tv (P Q : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ a, f a ∈ Set.Icc 0 1) :
    (∑ a, P.mass a * f a) - (∑ a, Q.mass a * f a) ≤ tv P Q := by
  have hz : (∑ a, (P.mass a - Q.mass a)) = 0 := by
    rw [Finset.sum_sub_distrib, P.total, Q.total, sub_self]
  have h (a : α) : (P.mass a - Q.mass a) * f a ≤
      (|P.mass a - Q.mass a| + (P.mass a - Q.mass a)) / 2 := by
    by_cases hd : 0 ≤ P.mass a - Q.mass a
    · rw [abs_of_nonneg hd]
      have := mul_le_mul_of_nonneg_left (hf a).2 hd
      linarith
    · rw [abs_of_neg (lt_of_not_ge hd)]
      have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hd) (hf a).1
      linarith
  calc
    _ = ∑ a, (P.mass a - Q.mass a) * f a := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _; ring
    _ ≤ ∑ a, (|P.mass a - Q.mass a| + (P.mass a - Q.mass a)) / 2 :=
      Finset.sum_le_sum fun a _ => h a
    _ = tv P Q := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, hz, add_zero]
      unfold tv
      ring

theorem binary_testing_bound (P Q : FiniteLaw α) (f : α → ℝ)
    (hf : ∀ a, f a ∈ Set.Icc 0 1) :
    ((∑ a, P.mass a * f a) + (∑ a, Q.mass a * (1 - f a))) / 2 ≤
      (1 + tv P Q) / 2 := by
  have h := expectation_diff_le_tv P Q f hf
  have heq : (∑ a, Q.mass a * (1 - f a)) = 1 - ∑ a, Q.mass a * f a := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, Q.total]
  rw [heq]
  linarith


theorem sum_max_eq (P Q : FiniteLaw α) :
    (∑ a, max (P.mass a) (Q.mass a)) = 1 + tv P Q := by
  have hpoint (a : α) : max (P.mass a) (Q.mass a) =
      (P.mass a + Q.mass a + |P.mass a - Q.mass a|) / 2 := by
    by_cases h : P.mass a ≤ Q.mass a
    · rw [max_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [max_eq_left (le_of_not_ge h), abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]; ring
  simp_rw [hpoint]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, P.total, Q.total]
  unfold tv
  ring

/-- Joint exact recovery of independent binary choices, allowing arbitrary
randomized estimators. No coordinatewise decision rule is assumed. -/
theorem independent_binary_testing (P Q : FiniteLaw α) (g : ℕ)
    (A : (Fin g → α) → (Fin g → Bool) → ℝ)
    (hA0 : ∀ z θ, 0 ≤ A z θ) (hA1 : ∀ z, ∑ θ, A z θ = 1) :
    (1 / (2 : ℝ) ^ g) * ∑ θ : Fin g → Bool, ∑ z : Fin g → α,
      (∏ j, (if θ j then P.mass (z j) else Q.mass (z j))) * A z θ ≤
        ((1 + tv P Q) / 2) ^ g := by
  classical
  have hpoint (z : Fin g → α) (θ : Fin g → Bool) :
      (∏ j, (if θ j then P.mass (z j) else Q.mass (z j))) ≤
        ∏ j, max (P.mass (z j)) (Q.mass (z j)) := by
    apply Finset.prod_le_prod₀
    · intro j _; split <;> first | exact P.nonneg _ | exact Q.nonneg _
    · intro j _; split <;> first | exact le_max_left _ _ | exact le_max_right _ _
  have hsum (z : Fin g → α) :
      (∑ θ : Fin g → Bool,
        (∏ j, (if θ j then P.mass (z j) else Q.mass (z j))) * A z θ) ≤
          ∏ j, max (P.mass (z j)) (Q.mass (z j)) := by
    calc
      _ ≤ ∑ θ : Fin g → Bool,
          (∏ j, max (P.mass (z j)) (Q.mass (z j))) * A z θ := by
        apply Finset.sum_le_sum
        intro θ _
        exact mul_le_mul_of_nonneg_right (hpoint z θ) (hA0 z θ)
      _ = _ := by rw [← Finset.mul_sum, hA1, mul_one]
  rw [Finset.sum_comm]
  calc
    _ ≤ (1 / (2 : ℝ) ^ g) * ∑ z : Fin g → α, ∏ j,
        max (P.mass (z j)) (Q.mass (z j)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun z _ => hsum z) (by positivity)
    _ = (1 / (2 : ℝ) ^ g) * (∑ a, max (P.mass a) (Q.mass a)) ^ g := by
      rw [← Fintype.prod_sum (fun (_ : Fin g) a => max (P.mass a) (Q.mass a))]
      simp
    _ = _ := by rw [sum_max_eq, div_pow]; ring

def tensor (P : FiniteLaw α) (R : FiniteLaw β) : FiniteLaw (α × β) where
  mass z := P.mass z.1 * R.mass z.2
  nonneg z := mul_nonneg (P.nonneg z.1) (R.nonneg z.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, R.total, mul_one]
    exact P.total

theorem tv_tensor_le (P Q : FiniteLaw α) (R S : FiniteLaw β) :
    tv (P.tensor R) (Q.tensor S) ≤ tv P Q + tv R S := by
  unfold tv tensor
  simp only
  rw [Fintype.sum_prod_type, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hpoint (a : α) (b : β) :
      |P.mass a * R.mass b - Q.mass a * S.mass b| ≤
        |P.mass a - Q.mass a| * R.mass b + Q.mass a * |R.mass b - S.mass b| := by
    calc
      _ = |(P.mass a - Q.mass a) * R.mass b + Q.mass a * (R.mass b - S.mass b)| := by
        congr 1; ring
      _ ≤ |(P.mass a - Q.mass a) * R.mass b| + |Q.mass a * (R.mass b - S.mass b)| :=
        abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (R.nonneg b), abs_of_nonneg (Q.nonneg a)]
  calc
    _ ≤ ∑ a, ∑ b, (|P.mass a - Q.mass a| * R.mass b + Q.mass a * |R.mass b - S.mass b|) := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.sum_le_sum fun b _ => hpoint a b
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, R.total, mul_one]
      rw [← Finset.sum_mul, Q.total, one_mul]

theorem tv_product_succ (P Q : FiniteLaw α) (m : ℕ) :
    tv (P.product (m + 1)) (Q.product (m + 1)) =
      tv (P.tensor (P.product m)) (Q.tensor (Q.product m)) := by
  unfold tv product tensor
  simp only
  congr 1
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => α)).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Fin.prod_univ_succ, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]

theorem tv_product_le (P Q : FiniteLaw α) (m : ℕ) :
    tv (P.product m) (Q.product m) ≤ (m : ℝ) * tv P Q := by
  induction m with
  | zero => simp [tv, product]
  | succ m ih =>
    rw [tv_product_succ]
    apply (tv_tensor_le P Q (P.product m) (Q.product m)).trans
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using
      add_le_add_left ih (tv P Q)


theorem affinity_bind_ge (P Q : FiniteLaw α) (K : α → FiniteLaw β) :
    affinity P Q ≤ affinity (P.bind K) (Q.bind K) := by
  have hpoint (b : β) :
      (∑ a, Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) * (K a).mass b) ≤
        Real.sqrt ((P.bind K).mass b) * Real.sqrt ((Q.bind K).mass b) := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
      (r := fun a => Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) * (K a).mass b)
      (f := fun a => P.mass a * (K a).mass b) (g := fun a => Q.mass a * (K a).mass b)
      (fun a _ => mul_nonneg (P.nonneg a) ((K a).nonneg b))
      (fun a _ => mul_nonneg (Q.nonneg a) ((K a).nonneg b)) (by
        intro a _
        rw [mul_pow, mul_pow, Real.sq_sqrt (P.nonneg a), Real.sq_sqrt (Q.nonneg a)]
        nlinarith only [sq_nonneg ((K a).mass b)])
    have hp2 := Real.sq_sqrt ((P.bind K).nonneg b)
    have hq2 := Real.sq_sqrt ((Q.bind K).nonneg b)
    have hsq : (Real.sqrt ((P.bind K).mass b) * Real.sqrt ((Q.bind K).mass b)) ^ 2 =
        (P.bind K).mass b * (Q.bind K).mass b := by rw [mul_pow, hp2, hq2]
    change (∑ a, Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) * (K a).mass b) ^ 2 ≤
      (P.bind K).mass b * (Q.bind K).mass b at hcs
    have hn : 0 ≤ Real.sqrt ((P.bind K).mass b) * Real.sqrt ((Q.bind K).mass b) := by positivity
    nlinarith only [hcs, hsq, hn]
  calc
    affinity P Q = ∑ b, ∑ a, Real.sqrt (P.mass a) * Real.sqrt (Q.mass a) * (K a).mass b := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, (K _).total, mul_one]
      rfl
    _ ≤ _ := Finset.sum_le_sum fun b _ => hpoint b

theorem hellingerSq_bind_le (P Q : FiniteLaw α) (K : α → FiniteLaw β) :
    hellingerSq (P.bind K) (Q.bind K) ≤ hellingerSq P Q := by
  rw [hellingerSq_eq, hellingerSq_eq]
  linarith [affinity_bind_ge P Q K]

/-- Restoration of approximate oracle simulations before taking independent
complete observations; the simulation error is charged once per sample. -/
theorem approximate_score_transfer (P Q : FiniteLaw α) (K : α → FiniteLaw β)
    (R S : FiniteLaw β) (Z : α → ℝ)
    (hZ : ∀ a, Q.mass a = P.mass a * (1 + Z a)) (E : ℝ)
    (hR : tv R (P.bind K) ≤ E) (hS : tv S (Q.bind K) ≤ E) (m : ℕ) :
    tv (R.product m) (S.product m) ≤
      Real.sqrt ((m : ℝ) * ∑ a, P.mass a * Z a ^ 2) + 2 * m * E := by
  have hmid : tv ((P.bind K).product m) ((Q.bind K).product m) ≤
      Real.sqrt ((m : ℝ) * ∑ a, P.mass a * Z a ^ 2) := by
    apply (tv_le_sqrt_hellingerSq _ _).trans
    apply Real.sqrt_le_sqrt
    apply (hellingerSq_product_le _ _ m).trans
    exact mul_le_mul_of_nonneg_left
      ((hellingerSq_bind_le P Q K).trans (hellingerSq_le_score P Q Z hZ)) (by positivity)
  have hr := (tv_product_le R (P.bind K) m).trans
    (mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ m))
  have hs := (tv_product_le S (Q.bind K) m).trans
    (mul_le_mul_of_nonneg_left hS (by positivity : (0 : ℝ) ≤ m))
  rw [tv_symm (S.product m)] at hs
  have htri1 := tv_triangle (R.product m) ((P.bind K).product m) (S.product m)
  have htri2 := tv_triangle ((P.bind K).product m) ((Q.bind K).product m) (S.product m)
  linarith

def overlap (P Q : FiniteLaw α) : ℝ := ∑ a, min (P.mass a) (Q.mass a)

theorem overlap_eq_one_sub_tv (P Q : FiniteLaw α) : overlap P Q = 1 - tv P Q := by
  have hm : overlap P Q + (∑ a, max (P.mass a) (Q.mass a)) = 2 := by
    rw [overlap, ← Finset.sum_add_distrib]
    simp_rw [min_add_max]
    rw [Finset.sum_add_distrib, P.total, Q.total]
    norm_num
  rw [sum_max_eq] at hm
  linarith

theorem overlap_nonneg (P Q : FiniteLaw α) : 0 ≤ overlap P Q := by
  apply Finset.sum_nonneg
  intro a _
  exact le_min (P.nonneg a) (Q.nonneg a)

def commonPart (P Q : FiniteLaw α) (h : 0 < overlap P Q) : FiniteLaw α where
  mass a := min (P.mass a) (Q.mass a) / overlap P Q
  nonneg a := div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le
  total := by rw [← Finset.sum_div]; exact div_self h.ne'

theorem commonPart_le_left (P Q : FiniteLaw α) (h : 0 < overlap P Q)
    {ω : ℝ} (hω : ω ≤ overlap P Q) (a : α) :
    ω * (commonPart P Q h).mass a ≤ P.mass a := by
  change ω * (min (P.mass a) (Q.mass a) / overlap P Q) ≤ _
  calc
    _ ≤ overlap P Q * (min (P.mass a) (Q.mass a) / overlap P Q) :=
      mul_le_mul_of_nonneg_right hω (div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le)
    _ = min (P.mass a) (Q.mass a) := by field_simp
    _ ≤ _ := min_le_left _ _

def remainderLaw (P H : FiniteLaw α) (ω : ℝ) (hω : ω < 1)
    (hdom : ∀ a, ω * H.mass a ≤ P.mass a) : FiniteLaw α where
  mass a := (P.mass a - ω * H.mass a) / (1 - ω)
  nonneg a := div_nonneg (sub_nonneg.mpr (hdom a)) (sub_pos.mpr hω).le
  total := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, P.total, H.total, mul_one]
    exact div_self (sub_pos.mpr hω).ne'

theorem common_part_decomposition (P Q : FiniteLaw α) {ω : ℝ}
    (hω : ω ∈ Set.Ioo 0 1) (hov : ω ≤ overlap P Q) :
    ∃ H P' Q' : FiniteLaw α,
      (∀ a, P.mass a = ω * H.mass a + (1 - ω) * P'.mass a) ∧
      (∀ a, Q.mass a = ω * H.mass a + (1 - ω) * Q'.mass a) := by
  have h : 0 < overlap P Q := lt_of_lt_of_le hω.1 hov
  let H := commonPart P Q h
  have hP : ∀ a, ω * H.mass a ≤ P.mass a := commonPart_le_left P Q h hov
  have hQ : ∀ a, ω * H.mass a ≤ Q.mass a := by
    intro a
    change ω * (min (P.mass a) (Q.mass a) / overlap P Q) ≤ _
    calc
      _ ≤ overlap P Q * (min (P.mass a) (Q.mass a) / overlap P Q) :=
        mul_le_mul_of_nonneg_right hov (div_nonneg (le_min (P.nonneg a) (Q.nonneg a)) h.le)
      _ = min (P.mass a) (Q.mass a) := by field_simp
      _ ≤ _ := min_le_right _ _
  refine ⟨H, remainderLaw P H ω hω.2 hP, remainderLaw Q H ω hω.2 hQ, ?_, ?_⟩
  · intro a
    change P.mass a = ω * H.mass a + (1 - ω) * ((P.mass a - ω * H.mass a) / (1 - ω))
    field_simp [(sub_pos.mpr hω.2).ne']
    ring
  · intro a
    change Q.mass a = ω * H.mass a + (1 - ω) * ((Q.mass a - ω * H.mass a) / (1 - ω))
    field_simp [(sub_pos.mpr hω.2).ne']
    ring

end FiniteLaw
end TraceReconstruction

namespace TraceReconstruction.FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

def prod (P : FiniteLaw α) (Q : FiniteLaw β) : FiniteLaw (α × β) where
  mass x := P.mass x.1 * Q.mass x.2
  nonneg x := mul_nonneg (P.nonneg _) (Q.nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, Q.total, mul_one]
    exact P.total

def expect (P : FiniteLaw α) (f : α → ℝ) : ℝ := ∑ a, P.mass a * f a

theorem expect_const (P : FiniteLaw α) (c : ℝ) : P.expect (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, P.total, one_mul]

theorem expect_mono (P : FiniteLaw α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    P.expect f ≤ P.expect g := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (h a) (P.nonneg a)

theorem expect_prod (P : FiniteLaw α) (Q : FiniteLaw β) (f : α × β → ℝ) :
    (P.prod Q).expect f = P.expect (fun a => Q.expect (fun b => f (a, b))) := by
  unfold expect prod
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, mul_assoc]

/-- Association is only used for increasing likelihood-threshold events. -/
def Associated [Preorder α] (P : FiniteLaw α) : Prop :=
  ∀ f g : α → ℝ, Monotone f → Monotone g →
    P.expect f * P.expect g ≤ P.expect (fun a => f a * g a)

theorem associated_linearOrder [LinearOrder α] (P : FiniteLaw α) : P.Associated := by
  intro f g hf hg
  have hn (a b : α) : 0 ≤ (f a - f b) * (g a - g b) := by
    rcases le_total a b with hab | hba
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hab))
        (sub_nonpos.mpr (hg hab))
    · exact mul_nonneg (sub_nonneg.mpr (hf hba)) (sub_nonneg.mpr (hg hba))
  have h := Finset.sum_nonneg (s := Finset.univ) (fun a _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun b _ => mul_nonneg (mul_nonneg (P.nonneg a)
      (P.nonneg b)) (hn a b)))
  have hid : (∑ a, ∑ b, P.mass a * P.mass b * ((f a - f b) * (g a - g b))) =
      2 * (P.expect (fun a => f a * g a) - P.expect f * P.expect g) := by
    have hp (a b : α) : P.mass a * P.mass b * ((f a - f b) * (g a - g b)) =
        (P.mass a * (f a * g a)) * P.mass b + P.mass a * (P.mass b * (f b * g b)) -
        (P.mass a * f a) * (P.mass b * g b) - (P.mass a * g a) * (P.mass b * f b) := by ring
    simp_rw [hp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, P.total, one_mul, mul_one]
    unfold expect
    ring
  rw [hid] at h
  linarith

theorem Associated.prod [Preorder α] [Preorder β] {P : FiniteLaw α} {Q : FiniteLaw β}
    (hP : P.Associated) (hQ : Q.Associated) : (P.prod Q).Associated := by
  intro f g hf hg
  rw [expect_prod, expect_prod, expect_prod]
  calc
    _ ≤ P.expect (fun a => Q.expect (fun b => f (a, b)) * Q.expect (fun b => g (a, b))) := by
      apply hP
      · intro a a' ha
        exact Q.expect_mono (fun b => hf ⟨ha, le_rfl⟩)
      · intro a a' ha
        exact Q.expect_mono (fun b => hg ⟨ha, le_rfl⟩)
    _ ≤ _ := by
      apply P.expect_mono
      intro a
      apply hQ
      · intro b b' hb; exact hf ⟨le_rfl, hb⟩
      · intro b b' hb; exact hg ⟨le_rfl, hb⟩

theorem product_succ_expect (P : FiniteLaw α) (n : ℕ) (f : (Fin (n + 1) → α) → ℝ) :
    (P.product (n + 1)).expect f =
      P.expect (fun a => (P.product n).expect (fun b => f (Fin.cons a b))) := by
  unfold expect product
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => α)).sum_comp, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change (∏ j, P.mass ((Fin.cons a b : Fin (n + 1) → α) j)) * f (Fin.cons a b) = _
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  ring

theorem associated_product [Preorder α] (P : FiniteLaw α) (hP : P.Associated) (n : ℕ) :
    (P.product n).Associated := by
  induction n with
  | zero =>
    intro f g _ _
    simp [expect, product]
  | succ n ih =>
    intro f g hf hg
    rw [product_succ_expect, product_succ_expect, product_succ_expect]
    have hcons {a a' : α} {b b' : Fin n → α} (ha : a ≤ a') (hb : b ≤ b') :
        (Fin.cons a b : Fin (n + 1) → α) ≤ (Fin.cons a' b' : Fin (n + 1) → α) := by
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact ha
      · exact hb i
    calc
      _ ≤ P.expect (fun a => (P.product n).expect (fun b => f (Fin.cons a b)) *
          (P.product n).expect (fun b => g (Fin.cons a b))) := by
        apply hP
        · intro a a' ha
          exact (P.product n).expect_mono (fun b => hf (hcons ha le_rfl))
        · intro a a' ha
          exact (P.product n).expect_mono (fun b => hg (hcons ha le_rfl))
      _ ≤ _ := by
        apply P.expect_mono
        intro a
        apply ih
        · intro b b' hb; exact hf (hcons le_rfl hb)
        · intro b b' hb; exact hg (hcons le_rfl hb)

/-- An elementary Paley--Zygmund bound at threshold 1/2, for a density. -/
theorem density_threshold_mass (P : FiniteLaw α) (f : α → ℝ)
    (hmean : P.expect f = 1) :
    (1 : ℝ) / 4 ≤
      (P.expect (fun a => if 1 / 2 ≤ f a then 1 else 0)) * P.expect (fun a => f a ^ 2) := by
  classical
  let S : Finset α := Finset.univ.filter (fun a => 1 / 2 ≤ f a)
  have hsmall : (∑ a ∈ Finset.univ \ S, P.mass a * f a) ≤ 1 / 2 := by
    calc
      _ ≤ ∑ a ∈ Finset.univ \ S, P.mass a * (1 / 2) := by
        apply Finset.sum_le_sum
        intro a ha
        have hnot : ¬ 1 / 2 ≤ f a := by simpa [S] using (Finset.mem_sdiff.mp ha).2
        exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hnot)) (P.nonneg a)
      _ ≤ ∑ a, P.mass a * (1 / 2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset)
        intro a _ _; positivity [P.nonneg a]
      _ = 1 / 2 := P.expect_const _
  have hlarge : 1 / 2 ≤ ∑ a ∈ S, P.mass a * f a := by
    have hsplit := Finset.sum_sdiff (Finset.subset_univ S) (f := fun a => P.mass a * f a)
    change (∑ a, P.mass a * f a) = 1 at hmean
    rw [hmean] at hsplit
    linarith
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := S)
    (r := fun a => P.mass a * f a) (f := P.mass) (g := fun a => P.mass a * f a ^ 2)
    (fun a _ => P.nonneg a) (fun a _ => by positivity [P.nonneg a])
    (fun a _ => by nlinarith)
  have ht : (∑ a ∈ S, P.mass a * f a ^ 2) ≤ P.expect (fun a => f a ^ 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    intro a _ _; positivity [P.nonneg a]
  have hmass : P.expect (fun a => if 1 / 2 ≤ f a then 1 else 0) = ∑ a ∈ S, P.mass a := by
    unfold expect S
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_filter]
  rw [hmass]
  have hm := mul_le_mul_of_nonneg_left ht (Finset.sum_nonneg (s := S) (fun a _ => P.nonneg a))
  nlinarith

/-- The common-density overlap used for consecutive pure primitive runs. -/
theorem increasing_density_overlap [Preorder α] (P : FiniteLaw α) (hP : P.Associated)
    (f g : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a)
    (hfm : Monotone f) (hgm : Monotone g)
    (hf1 : P.expect f = 1) (hg1 : P.expect g = 1) :
    (1 : ℝ) / 32 ≤ P.expect (fun a => min (f a) (g a)) *
      P.expect (fun a => f a ^ 2) * P.expect (fun a => g a ^ 2) := by
  let F : α → ℝ := fun a => if 1 / 2 ≤ f a then 1 else 0
  let G : α → ℝ := fun a => if 1 / 2 ≤ g a then 1 else 0
  have hF : Monotone F := by
    intro a b hab
    dsimp [F]
    split_ifs with ha hb hb
    · rfl
    · exact False.elim (hb (ha.trans (hfm hab)))
    · norm_num
    · rfl
  have hG : Monotone G := by
    intro a b hab
    dsimp [G]
    split_ifs with ha hb hb
    · rfl
    · exact False.elim (hb (ha.trans (hgm hab)))
    · norm_num
    · rfl
  have hcorr := hP F G hF hG
  have hpoint : ∀ a, (1 / 2 : ℝ) * (F a * G a) ≤ min (f a) (g a) := by
    intro a
    dsimp [F, G]
    split_ifs <;> simp only [mul_one, mul_zero]
    · exact le_min ‹_› ‹_›
    all_goals exact le_min (hf a) (hg a)
  have hint := P.expect_mono hpoint
  have heq : P.expect (fun a => (1 / 2 : ℝ) * (F a * G a)) =
      (1 / 2 : ℝ) * P.expect (fun a => F a * G a) := by
    unfold expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _; ring
  rw [heq] at hint
  have hfm2 : 0 ≤ P.expect (fun a => f a ^ 2) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  have hgm2 : 0 ≤ P.expect (fun a => g a ^ 2) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (sq_nonneg _))
  have hff := density_threshold_mass P f hf1
  have hgg := density_threshold_mass P g hg1
  change 1 / 4 ≤ P.expect F * P.expect (fun a => f a ^ 2) at hff
  change 1 / 4 ≤ P.expect G * P.expect (fun a => g a ^ 2) at hgg
  have hmul := mul_le_mul hff hgg (by norm_num : (0 : ℝ) ≤ 1 / 4) (by linarith :
    0 ≤ P.expect F * P.expect (fun a => f a ^ 2))
  have hcomb : (1 / 2 : ℝ) * (P.expect F * P.expect G) ≤
      P.expect (fun a => min (f a) (g a)) := by linarith
  have hmul2 := mul_le_mul_of_nonneg_right hcomb (mul_nonneg hfm2 hgm2)
  nlinarith only [hmul, hmul2]

end TraceReconstruction.FiniteLaw

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]
/-- Orientation `false` uses P,Q in chronological order; true reverses them. -/
def orientedProd (P Q : FiniteLaw α) (b : Bool) : FiniteLaw (α × α) :=
  if b then Q.prod P else P.prod Q

def pairedHiddenMass (H : FiniteLaw α) (ω : ℝ) (z : α × α) : ℝ :=
  ω ^ 2 * H.mass z.1 * H.mass z.2

theorem sum_pairedHiddenMass (H : FiniteLaw α) (ω : ℝ) :
    (∑ z, pairedHiddenMass H ω z) = ω ^ 2 := by
  unfold pairedHiddenMass
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, H.total, mul_one]
  rw [← Finset.mul_sum, H.total, mul_one]

theorem pairedHiddenMass_le (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω * H.mass a ≤ P.mass a) (hQ : ∀ a, ω * H.mass a ≤ Q.mass a)
    (b : Bool) (z : α × α) : pairedHiddenMass H ω z ≤ (orientedProd P Q b).mass z := by
  have hm (R S : FiniteLaw α) (hR : ∀ a, ω * H.mass a ≤ R.mass a)
      (hS : ∀ a, ω * H.mass a ≤ S.mass a) :
      pairedHiddenMass H ω z ≤ R.mass z.1 * S.mass z.2 := by
    calc
      _ = (ω * H.mass z.1) * (ω * H.mass z.2) := by unfold pairedHiddenMass; ring
      _ ≤ _ := mul_le_mul (hR z.1) (hS z.2)
        (mul_nonneg hω (H.nonneg _)) (R.nonneg _)
  cases b
  · exact hm P Q hP hQ
  · exact hm Q P hQ hP

/-- None is the joint hidden flag; a visible flag reports the true orientation. -/
def pairedFlagMass (P Q H : FiniteLaw α) (ω : ℝ) (b : Bool)
    (z : Option Bool × (α × α)) : ℝ :=
  match z.1 with
  | none => pairedHiddenMass H ω z.2
  | some c => if c = b then (orientedProd P Q b).mass z.2 - pairedHiddenMass H ω z.2 else 0

theorem pairedFlagMass_nonneg (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω * H.mass a ≤ P.mass a) (hQ : ∀ a, ω * H.mass a ≤ Q.mass a)
    (b : Bool) (z : Option Bool × (α × α)) : 0 ≤ pairedFlagMass P Q H ω b z := by
  unfold pairedFlagMass
  split
  · unfold pairedHiddenMass
    positivity [H.nonneg z.2.1, H.nonneg z.2.2]
  · split_ifs
    · exact sub_nonneg.mpr (pairedHiddenMass_le P Q H hω hP hQ b z.2)
    · rfl

theorem pairedFlagMass_sum (P Q H : FiniteLaw α) (ω : ℝ) (b : Bool) :
    (∑ z, pairedFlagMass P Q H ω b z) = 1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hp (z : α × α) : (∑ c : Option Bool, pairedFlagMass P Q H ω b (c, z)) =
      (orientedProd P Q b).mass z := by
    cases b <;> simp [pairedFlagMass, Fintype.sum_option ]
  simp_rw [hp]
  exact (orientedProd P Q b).total

def pairedFlagLaw (P Q H : FiniteLaw α) {ω : ℝ} (hω : 0 ≤ ω)
    (hP : ∀ a, ω * H.mass a ≤ P.mass a) (hQ : ∀ a, ω * H.mass a ≤ Q.mass a)
    (b : Bool) : FiniteLaw (Option Bool × (α × α)) :=
  ⟨pairedFlagMass P Q H ω b, pairedFlagMass_nonneg P Q H hω hP hQ b,
    pairedFlagMass_sum P Q H ω b⟩

/-- Forgetting the report recovers conditional independence for each orientation. -/
theorem pairedFlag_simulation (P Q H : FiniteLaw α) (ω : ℝ) (b : Bool) (z : α × α) :
    (∑ c : Option Bool, pairedFlagMass P Q H ω b (c, z)) =
      (orientedProd P Q b).mass z := by
  cases b <;> simp [pairedFlagMass, Fintype.sum_option ]

/-- Hidden reports carry exactly zero information about the fair orientation,
even after both strings have been observed. -/
theorem pairedFlag_hidden_joint (P Q H : FiniteLaw α) (ω : ℝ) (b : Bool) (z : α × α) :
    (1 / 2 : ℝ) * pairedFlagMass P Q H ω b (none, z) =
      (1 / 2 : ℝ) * (ω ^ 2 * (H.prod H).mass z) := by
  unfold pairedFlagMass pairedHiddenMass prod
  ring

theorem pairedFlag_hidden_probability (P Q H : FiniteLaw α) (ω : ℝ) (b : Bool) :
    (∑ z, pairedFlagMass P Q H ω b (none, z)) = ω ^ 2 := sum_pairedHiddenMass H ω

end TraceReconstruction.FiniteLaw

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]
theorem small_geometric_sum (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / 2)) :
    (∑ j ∈ Finset.range n, x ^ j) ≤ 2 := by
  have he := geom_sum_mul x n
  have hn : 0 ≤ ∑ j ∈ Finset.range n, x ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hx.1 j)
  have hp := pow_nonneg hx.1 n
  nlinarith [mul_le_mul_of_nonneg_left hx.2 hn]

/-- Elementary tail of a binomial polynomial after cancelling orders zero and one. -/
theorem small_binomial_tail (n : ℕ) {x : ℝ} (hx : 0 ≤ x) (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (∑ j ∈ Finset.range (n - 1), (n.choose (j + 2) : ℝ) * x ^ (j + 2)) ≤
      2 * ((n : ℝ) * x) ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range (n - 1), ((n : ℝ) * x) ^ 2 * ((n : ℝ) * x) ^ j := by
      apply Finset.sum_le_sum
      intro j _
      have hc : (n.choose (j + 2) : ℝ) ≤ (n : ℝ) ^ (j + 2) := by
        exact_mod_cast Nat.choose_le_pow n (j + 2)
      calc
        _ ≤ (n : ℝ) ^ (j + 2) * x ^ (j + 2) :=
          mul_le_mul_of_nonneg_right hc (pow_nonneg hx _)
        _ = _ := by rw [← mul_pow, pow_add]; ring
    _ = ((n : ℝ) * x) ^ 2 * ∑ j ∈ Finset.range (n - 1), ((n : ℝ) * x) ^ j := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      have h := small_geometric_sum (n - 1) ⟨mul_nonneg (Nat.cast_nonneg n) hx, hsmall⟩
      nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ((n : ℝ) * x))]

theorem expect_pow_expansion (P : FiniteLaw α) (Z : α → ℝ) (u : ℝ) (t : ℕ) :
    P.expect (fun a => (1 + u * Z a) ^ t) =
      ∑ j ∈ Finset.range (t + 1), (t.choose j : ℝ) * u ^ j * P.expect (fun a => Z a ^ j) := by
  unfold expect
  simp_rw [add_comm (1 : ℝ), add_pow, one_pow, mul_one, mul_pow, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expect_small_affine_pow (P : FiniteLaw α) (Z : α → ℝ) (t : ℕ) (ht : 2 ≤ t)
    (hcenter : P.expect Z = 0)
    (hmom : ∀ j ≤ t, |P.expect (fun a => Z a ^ j)| ≤ 2)
    {u : ℝ} (hu : (t : ℝ) * |u| ≤ 1 / 2) :
    P.expect (fun a => (1 + u * Z a) ^ t) ≤ 1 + 4 * ((t : ℝ) * u) ^ 2 := by
  rw [expect_pow_expansion]
  have ht' : t + 1 = 2 + (t - 1) := by omega
  rw [ht', Finset.sum_range_add]
  have hz : P.expect (fun _ : α => (1 : ℝ)) = 1 := by simp [expect, P.total]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_mul,
    Nat.choose_one_right, pow_one]
  rw [hz, hcenter]
  simp only [mul_zero, add_zero]
  have hb : (∑ j ∈ Finset.range (t - 1), (t.choose (2 + j) : ℝ) * u ^ (2 + j) *
      P.expect (fun a => Z a ^ (2 + j))) ≤
      2 * ∑ j ∈ Finset.range (t - 1), (t.choose (j + 2) : ℝ) * |u| ^ (j + 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjt : 2 + j ≤ t := by have := Finset.mem_range.mp hj; omega
    have hm := hmom (2 + j) hjt
    calc
      _ ≤ |(t.choose (2 + j) : ℝ) * u ^ (2 + j) * P.expect (fun a => Z a ^ (2 + j))| :=
        le_abs_self _
      _ ≤ (t.choose (2 + j) : ℝ) * |u| ^ (2 + j) * 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
        exact mul_le_mul_of_nonneg_left hm (by positivity)
      _ = _ := by rw [Nat.add_comm 2 j]; ring
  have htail := small_binomial_tail t (abs_nonneg u) hu
  have he : ((t : ℝ) * |u|) ^ 2 = ((t : ℝ) * u) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  rw [he] at htail
  linarith

/-- Only the centered first moment must vanish; lower absolute moments
are obtained from the one available source moment, without boundedness. -/
theorem expect_lower_moment_le_two (P : FiniteLaw α) (Z : α → ℝ) (t : ℕ)
    (ht : P.expect (fun a => |Z a| ^ t) ≤ 1) (j : ℕ) (hj : j ≤ t) :
    |P.expect (fun a => Z a ^ j)| ≤ 2 := by
  have hpoint (a : α) : |Z a| ^ j ≤ 1 + |Z a| ^ t := by
    by_cases hx : |Z a| ≤ 1
    · have h := pow_le_one₀ (n := j) (abs_nonneg _) hx
      nlinarith [pow_nonneg (abs_nonneg (Z a)) t]
    · have h := pow_le_pow_right₀ (le_of_lt (lt_of_not_ge hx)) hj
      linarith
  calc
    _ ≤ ∑ a, |P.mass a * Z a ^ j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, P.mass a * |Z a| ^ j := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg (P.nonneg a), abs_pow]
    _ ≤ ∑ a, P.mass a * (1 + |Z a| ^ t) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hpoint a) (P.nonneg a)
    _ = 1 + P.expect (fun a => |Z a| ^ t) := by
      simp_rw [mul_add, mul_one, Finset.sum_add_distrib, P.total]
      rfl
    _ ≤ 2 := by linarith

theorem expect_affine_pow_le (P : FiniteLaw α) (Z : α → ℝ) (t : ℕ)
    (hmom : ∀ j ≤ t, |P.expect (fun a => Z a ^ j)| ≤ 2) (u : ℝ) :
    P.expect (fun a => (1 + u * Z a) ^ t) ≤ 2 * (1 + |u|) ^ t := by
  rw [expect_pow_expansion, add_comm (1 : ℝ), add_pow, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have h := hmom j (by have := Finset.mem_range.mp hj; omega)
  calc
    _ ≤ |(t.choose j : ℝ) * u ^ j * P.expect (fun a => Z a ^ j)| := le_abs_self _
    _ ≤ (t.choose j : ℝ) * |u| ^ j * 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), abs_pow]
      exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by simp only [one_pow, mul_one]; ring

/-- Scalar two-smoothness at even moment order; its constant is linear
in that order after taking the square root, as required for tensorization. -/
theorem scalar_even_moment_unit (P : FiniteLaw α) (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hcenter : P.expect Z = 0) (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1) (u : ℝ) :
    P.expect (fun a => (1 + u * Z a) ^ (2 * k)) ≤
      (1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2) ^ k := by
  have hmom := expect_lower_moment_le_two P Z (2 * k) ht
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have htR : (1 : ℝ) ≤ (2 * k : ℕ) := by exact_mod_cast (show 1 ≤ 2 * k by omega)
  have hbase : 1 ≤ 1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2 := by nlinarith [mul_nonneg (sq_nonneg (6 * ((2 * k : ℕ) : ℝ))) (sq_nonneg u)]
  by_cases hu : ((2 * k : ℕ) : ℝ) * |u| ≤ 1 / 2
  · have hs := expect_small_affine_pow P Z (2 * k) (by omega) hcenter hmom hu
    have hb : 1 + 4 * (((2 * k : ℕ) : ℝ) * u) ^ 2 ≤
        1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2 := by nlinarith [sq_nonneg (((2 * k : ℕ) : ℝ) * u)]
    exact hs.trans (hb.trans (le_self_pow₀ hbase (by omega)))
  · have hu' : 1 / 2 ≤ ((2 * k : ℕ) : ℝ) * |u| := le_of_lt (lt_of_not_ge hu)
    have hsum : 1 + |u| ≤ 3 * ((2 * k : ℕ) : ℝ) * |u| := by
      have hh := mul_le_mul_of_nonneg_right htR (abs_nonneg u)
      nlinarith
    have hc : (2 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := le_self_pow₀ (by norm_num) (by omega)
    calc
      _ ≤ 2 * (1 + |u|) ^ (2 * k) := expect_affine_pow_le P Z (2 * k) hmom u
      _ ≤ 2 * (3 * ((2 * k : ℕ) : ℝ) * |u|) ^ (2 * k) := by gcongr
      _ ≤ 2 ^ (2 * k) * (3 * ((2 * k : ℕ) : ℝ) * |u|) ^ (2 * k) := by
        exact mul_le_mul_of_nonneg_right hc (by positivity)
      _ = ((6 * (2 * k : ℕ) : ℝ) ^ 2 * u ^ 2) ^ k := by
        rw [← mul_pow, pow_mul]
        congr 1
        simp only [mul_pow, sq_abs]
        ring
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (by linarith) k

/-- Homogeneous version of the scalar even-moment inequality. -/
theorem scalar_even_moment (P : FiniteLaw α) (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hcenter : P.expect Z = 0) (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1) (b v : ℝ) :
    P.expect (fun a => (b + v * Z a) ^ (2 * k)) ≤
      (b ^ 2 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * v ^ 2) ^ k := by
  have heven (a : α) : |Z a| ^ (2 * k) = Z a ^ (2 * k) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  have hmoment : P.expect (fun a => Z a ^ (2 * k)) ≤ 1 := by
    simpa only [heven] using ht
  have hc : 1 ≤ (6 * (2 * k : ℕ) : ℝ) ^ 2 := by
    have hn : (1 : ℝ) ≤ (2 * k : ℕ) := by exact_mod_cast (show 1 ≤ 2 * k by omega)
    nlinarith
  by_cases hb : b = 0
  · subst b
    simp only [zero_add, zero_pow (by omega : 2 ≠ 0)]
    have he : P.expect (fun a => (v * Z a) ^ (2 * k)) =
        v ^ (2 * k) * P.expect (fun a => Z a ^ (2 * k)) := by
      simp only [expect, mul_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [he]
    calc
      _ ≤ v ^ (2 * k) := by
        have hv : 0 ≤ v ^ (2 * k) := by rw [pow_mul]; positivity
        nlinarith [mul_le_mul_of_nonneg_left hmoment hv]
      _ = (v ^ 2) ^ k := pow_mul v 2 k
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg v) (by nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg v)]) k
  · have hs := scalar_even_moment_unit P Z k hk hcenter ht (v / b)
    have hbpow : 0 ≤ b ^ (2 * k) := by rw [pow_mul]; positivity
    have he : P.expect (fun a => (b + v * Z a) ^ (2 * k)) =
        b ^ (2 * k) * P.expect (fun a => (1 + v / b * Z a) ^ (2 * k)) := by
      unfold expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      have h : b + v * Z a = b * (1 + v / b * Z a) := by field_simp [hb]
      dsimp only
      rw [h, mul_pow]
      ring
    rw [he]
    calc
      _ ≤ b ^ (2 * k) * (1 + (6 * (2 * k : ℕ) : ℝ) ^ 2 * (v / b) ^ 2) ^ k :=
        mul_le_mul_of_nonneg_left hs hbpow
      _ = _ := by
        rw [pow_mul, ← mul_pow]
        congr 1
        field_simp [hb]

theorem weighted_minkowski_bound (P : FiniteLaw α) (k : ℕ) (hk : 1 ≤ k)
    (f g : α → ℝ) (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfa : P.expect (fun a => f a ^ k) ≤ A ^ k)
    (hgb : P.expect (fun a => g a ^ k) ≤ B ^ k) :
    P.expect (fun a => (f a + g a) ^ k) ≤ (A + B) ^ k := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  let w : α → ℝ := fun a => P.mass a ^ (1 / (k : ℝ))
  have hw (a : α) : 0 ≤ w a := Real.rpow_nonneg (P.nonneg a) _
  have hwk (a : α) : w a ^ k = P.mass a := by
    dsimp [w]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (P.nonneg a), one_div_mul_cancel hk0, Real.rpow_one]
  have hsingle (F : α → ℝ) (hF : ∀ a, 0 ≤ F a) :
      (∑ a, |w a * F a| ^ (k : ℝ)) = P.expect (fun a => F a ^ k) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [abs_of_nonneg (mul_nonneg (hw a) (hF a)), Real.rpow_natCast, mul_pow, hwk]
  have hsum : (∑ a, |w a * f a + w a * g a| ^ (k : ℝ)) =
      P.expect (fun a => (f a + g a) ^ k) := by
    simp_rw [← mul_add]
    exact hsingle _ (fun a => add_nonneg (hf a) (hg a))
  have hm := Real.Lp_add_le Finset.univ (fun a => w a * f a) (fun a => w a * g a) hkR
  rw [hsum, hsingle f hf, hsingle g hg] at hm
  have hroots (F : α → ℝ) (hF : ∀ a, 0 ≤ F a) (C : ℝ) (hC : 0 ≤ C)
      (hFC : P.expect (fun a => F a ^ k) ≤ C ^ k) :
      (P.expect (fun a => F a ^ k)) ^ (1 / (k : ℝ)) ≤ C := by
    calc
      _ ≤ (C ^ k) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow (Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (pow_nonneg (hF a) k))) hFC (by positivity)
      _ = C := by
        rw [← Real.rpow_natCast, one_div, Real.rpow_rpow_inv hC hk0]
  have hroot : (P.expect (fun a => (f a + g a) ^ k)) ^ (1 / (k : ℝ)) ≤ A + B :=
    hm.trans (add_le_add (hroots f hf A hA hfa) (hroots g hg B hB hgb))
  have hexp : 0 ≤ P.expect (fun a => (f a + g a) ^ k) :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (P.nonneg a) (pow_nonneg (add_nonneg (hf a) (hg a)) k))
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hexp _) hroot k
  rw [← Real.rpow_natCast, ← Real.rpow_mul hexp, one_div_mul_cancel hk0, Real.rpow_one] at hp
  exact hp
theorem product_succ_expect_tail (P : FiniteLaw α) (n : ℕ) (f : (Fin (n + 1) → α) → ℝ) :
    (P.product (n + 1)).expect f =
      (P.product n).expect (fun b => P.expect (fun a => f (Fin.cons a b))) := by
  rw [product_succ_expect]
  unfold expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end TraceReconstruction.FiniteLaw
namespace TraceReconstruction
variable {α : Type*}
def multilinear {n : ℕ} (A : (Fin n → Bool) → ℝ) (Z : α → ℝ) (x : Fin n → α) : ℝ :=
  ∑ σ, A σ * ∏ j, if σ j then Z (x j) else 1

def multilinearEnergy {n : ℕ} (A : (Fin n → Bool) → ℝ) (R : ℝ) : ℝ :=
  ∑ σ, A σ ^ 2 * ∏ j, if σ j then R ^ 2 else 1

theorem multilinearEnergy_nonneg {n : ℕ} (A : (Fin n → Bool) → ℝ) (R : ℝ) :
    0 ≤ multilinearEnergy A R := by
  apply Finset.sum_nonneg
  intro σ _
  apply mul_nonneg (sq_nonneg _)
  apply Finset.prod_nonneg
  intro j _
  split <;> positivity

theorem multilinear_cons {n : ℕ} (A : (Fin (n + 1) → Bool) → ℝ) (Z : α → ℝ)
    (x : Fin n → α) (a : α) :
    multilinear A Z (Fin.cons a x) =
      multilinear (fun σ => A (Fin.cons false σ)) Z x +
      Z a * multilinear (fun σ => A (Fin.cons true σ)) Z x := by
  unfold multilinear
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_bool, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem multilinearEnergy_cons {n : ℕ} (A : (Fin (n + 1) → Bool) → ℝ) (R : ℝ) :
    multilinearEnergy A R =
      multilinearEnergy (fun σ => A (Fin.cons false σ)) R +
      R ^ 2 * multilinearEnergy (fun σ => A (Fin.cons true σ)) R := by
  unfold multilinearEnergy
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp, Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_bool, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- The finite-product moment inequality used for every score expansion.
The order-cost is linear per degree, and no boundedness assumption is needed. -/
theorem multilinear_even_moment {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k) (hcenter : P.expect Z = 0)
    (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1)
    (n : ℕ) (A : (Fin n → Bool) → ℝ) :
    (P.product n).expect (fun x => multilinear A Z x ^ (2 * k)) ≤
      (multilinearEnergy A (6 * (2 * k : ℕ))) ^ k := by
  induction n with
  | zero =>
    simp only [FiniteLaw.expect, FiniteLaw.product, multilinear, multilinearEnergy,
      Fintype.prod_empty, mul_one, one_mul]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact le_of_eq (pow_mul _ 2 k)
  | succ n ih =>
    let A0 : (Fin n → Bool) → ℝ := fun σ => A (Fin.cons false σ)
    let A1 : (Fin n → Bool) → ℝ := fun σ => A (Fin.cons true σ)
    let R : ℝ := 6 * (2 * k : ℕ)
    let F0 : (Fin n → α) → ℝ := fun x => multilinear A0 Z x
    let F1 : (Fin n → α) → ℝ := fun x => multilinear A1 Z x
    have h0 := ih A0
    have h1 := ih A1
    have hA0 := multilinearEnergy_nonneg A0 R
    have hA1 := multilinearEnergy_nonneg A1 R
    rw [FiniteLaw.product_succ_expect_tail, multilinearEnergy_cons]
    calc
      _ ≤ (P.product n).expect (fun x => (F0 x ^ 2 + R ^ 2 * F1 x ^ 2) ^ k) := by
        apply FiniteLaw.expect_mono
        intro x
        simp_rw [multilinear_cons]
        have hs := FiniteLaw.scalar_even_moment P Z k hk hcenter ht (F0 x) (F1 x)
        simpa only [F0, F1, A0, A1, R, mul_comm] using hs
      _ ≤ (multilinearEnergy A0 R + R ^ 2 * multilinearEnergy A1 R) ^ k := by
        apply FiniteLaw.weighted_minkowski_bound (P.product n) k hk
          (fun x => F0 x ^ 2) (fun x => R ^ 2 * F1 x ^ 2)
          (fun x => sq_nonneg _) (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (multilinearEnergy A0 R) (R ^ 2 * multilinearEnergy A1 R) hA0
          (mul_nonneg (sq_nonneg _) hA1)
        · simpa only [← pow_mul] using h0
        · have he : (P.product n).expect (fun x => (R ^ 2 * F1 x ^ 2) ^ k) =
              (R ^ 2) ^ k * (P.product n).expect (fun x => F1 x ^ (2 * k)) := by
            unfold FiniteLaw.expect
            simp only [mul_pow, ← pow_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
          rw [he, mul_pow (R ^ 2) (multilinearEnergy A1 R)]
          exact mul_le_mul_of_nonneg_left h1 (pow_nonneg (sq_nonneg R) k)
      _ = _ := rfl

def monomialDegree {n : ℕ} (σ : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun j => σ j = true)).card

theorem monomial_weight {n : ℕ} (σ : Fin n → Bool) (R : ℝ) :
    (∏ j, if σ j then R ^ 2 else 1) = R ^ (2 * monomialDegree σ) := by
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, ← pow_mul, monomialDegree]

theorem multilinearEnergy_homogeneous {n : ℕ} (A : (Fin n → Bool) → ℝ)
    (r : ℕ) (hA : ∀ σ, monomialDegree σ ≠ r → A σ = 0) (R : ℝ) :
    multilinearEnergy A R = R ^ (2 * r) * ∑ σ, A σ ^ 2 := by
  unfold multilinearEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [monomial_weight]
  by_cases hd : monomialDegree σ = r
  · rw [hd, mul_comm]
  · rw [hA σ hd, zero_pow (by omega : 2 ≠ 0), zero_mul, mul_zero]

theorem homogeneous_even_moment {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k) (hcenter : P.expect Z = 0)
    (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1)
    (n r : ℕ) (A : (Fin n → Bool) → ℝ)
    (hA : ∀ σ, monomialDegree σ ≠ r → A σ = 0) :
    (P.product n).expect (fun x => multilinear A Z x ^ (2 * k)) ≤
      ((6 * (2 * k : ℕ) : ℝ) ^ (2 * r) * ∑ σ, A σ ^ 2) ^ k := by
  have h := multilinear_even_moment P Z k hk hcenter ht n A
  rw [multilinearEnergy_homogeneous A r hA] at h
  exact h

/-- Squared L^(2k)-norm for a finite law, expressed without measure coercions. -/
def FiniteLaw.evenMomentSq {α : Type*} [Fintype α] (P : FiniteLaw α)
    (f : α → ℝ) (k : ℕ) : ℝ :=
  (P.expect (fun a => |f a| ^ (2 * k))) ^ (1 / (k : ℝ))

theorem homogeneous_moment_sq {α : Type*} [Fintype α] (P : FiniteLaw α)
    (Z : α → ℝ) (k : ℕ) (hk : 1 ≤ k) (hcenter : P.expect Z = 0)
    (ht : P.expect (fun a => |Z a| ^ (2 * k)) ≤ 1)
    (n r : ℕ) (A : (Fin n → Bool) → ℝ)
    (hA : ∀ σ, monomialDegree σ ≠ r → A σ = 0) :
    (P.product n).evenMomentSq (multilinear A Z) k ≤
      (6 * (2 * k : ℕ) : ℝ) ^ (2 * r) * ∑ σ, A σ ^ 2 := by
  have h := homogeneous_even_moment P Z k hk hcenter ht n r A hA
  have he (x : Fin n → α) : |multilinear A Z x| ^ (2 * k) =
      multilinear A Z x ^ (2 * k) := by rw [pow_mul, sq_abs, ← pow_mul]
  unfold FiniteLaw.evenMomentSq
  simp_rw [he]
  have hn : 0 ≤ (P.product n).expect (fun x => multilinear A Z x ^ (2 * k)) := by
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg ((P.product n).nonneg _)
    change 0 ≤ multilinear A Z x ^ (2 * k)
    rw [pow_mul]
    positivity
  have hb : 0 ≤ (6 * (2 * k : ℕ) : ℝ) ^ (2 * r) * ∑ σ, A σ ^ 2 := by positivity
  calc
    _ ≤ (((6 * (2 * k : ℕ) : ℝ) ^ (2 * r) * ∑ σ, A σ ^ 2) ^ k) ^ (1 / (k : ℝ)) :=
      Real.rpow_le_rpow hn h (by positivity)
    _ = _ := by rw [← Real.rpow_natCast, one_div, Real.rpow_rpow_inv hb (by positivity)]
end TraceReconstruction

namespace TraceReconstruction.FiniteLaw
variable {α : Type*} [Fintype α]
def eventMass (P : FiniteLaw α) (A : Finset α) : ℝ := ∑ a ∈ A, P.mass a

theorem eventMass_nonneg (P : FiniteLaw α) (A : Finset α) : 0 ≤ P.eventMass A :=
  Finset.sum_nonneg (fun a _ => P.nonneg a)

theorem eventMass_le_one (P : FiniteLaw α) (A : Finset α) : P.eventMass A ≤ 1 := by
  rw [← P.total]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun a _ _ => P.nonneg a)

def condition (P : FiniteLaw α) (A : Finset α) (hA : 0 < P.eventMass A) : FiniteLaw α := by
  classical
  exact {
    mass := fun a => if a ∈ A then P.mass a / P.eventMass A else 0
    nonneg := fun a => by split <;> positivity [P.nonneg a]
    total := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hA) }

theorem overlap_condition (P : FiniteLaw α) (A : Finset α) (hA : 0 < P.eventMass A) :
    overlap P (condition P A hA) = P.eventMass A := by
  classical
  have he (a : α) : min (P.mass a) ((condition P A hA).mass a) =
      if a ∈ A then P.mass a else 0 := by
    by_cases ha : a ∈ A
    · simp only [condition, ha, ↓reduceIte]
      apply min_eq_left
      apply (le_div_iff₀ hA).mpr
      have h := mul_le_mul_of_nonneg_left (P.eventMass_le_one A) (P.nonneg a)
      simpa only [mul_one] using h
    · simp only [condition, ha, ↓reduceIte, min_eq_right (P.nonneg a)]
  unfold overlap
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, eventMass]

theorem tv_condition (P : FiniteLaw α) (A : Finset α) (hA : 0 < P.eventMass A) :
    tv P (condition P A hA) = 1 - P.eventMass A := by
  have he := P.overlap_condition A hA
  rw [overlap_eq_one_sub_tv] at he
  linarith

/-- Densities relative to one finite reference, preserving the exact normalization. -/
def withDensity (P : FiniteLaw α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hmean : P.expect f = 1) : FiniteLaw α where
  mass a := P.mass a * f a
  nonneg a := mul_nonneg (P.nonneg a) (hf a)
  total := hmean

theorem density_bad_mass_sq (P : FiniteLaw α) (f : α → ℝ) (A : Finset α) :
    (∑ a ∈ A, P.mass a * f a) ^ 2 ≤
      (P.eventMass A) * P.expect (fun a => f a ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq A (fun a => Real.sqrt (P.mass a))
    (fun a => Real.sqrt (P.mass a) * f a)
  simp only [mul_pow, Real.sq_sqrt (P.nonneg _)] at h
  have he : (∑ a ∈ A, Real.sqrt (P.mass a) * (Real.sqrt (P.mass a) * f a)) =
      ∑ a ∈ A, P.mass a * f a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (P.nonneg a)]
  rw [he] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (P.eventMass_nonneg A)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ =>
    mul_nonneg (P.nonneg a) (sq_nonneg _))

/-- Loss from the small-reference-density event by the exact available moment. -/
theorem low_density_reference_mass (P : FiniteLaw α) (f : α → ℝ) (t : ℕ)
    (A : Finset α) (hA : ∀ a ∈ A, f a < 1 / 2) :
    P.eventMass A ≤ (2 : ℝ) ^ t * P.expect (fun a => |f a - 1| ^ t) := by
  have hlocal (a : α) (ha : a ∈ A) : 1 ≤ (2 : ℝ) ^ t * |f a - 1| ^ t := by
    rw [← mul_pow]
    apply one_le_pow₀
    have hh := neg_le_abs (f a - 1)
    linarith [hA a ha]
  calc
    _ ≤ ∑ a ∈ A, (2 : ℝ) ^ t * (P.mass a * |f a - 1| ^ t) := by
      apply Finset.sum_le_sum
      intro a ha
      nlinarith [mul_le_mul_of_nonneg_left (hlocal a ha) (P.nonneg a)]
    _ ≤ ∑ a, (2 : ℝ) ^ t * (P.mass a * |f a - 1| ^ t) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => by positivity [P.nonneg a])
    _ = _ := by rw [← Finset.mul_sum]; rfl

/-- Exact common-event likelihood ratio: no lower bound is imposed off the event. -/
theorem conditioned_density_identity (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hg : ∀ a, 0 ≤ g a)
    (hfm : R.expect f = 1) (hgm : R.expect g = 1)
    (A : Finset α) (hAf : ∀ a ∈ A, 0 < f a)
    (hP : 0 < (R.withDensity f hf hfm).eventMass A)
    (hQ : 0 < (R.withDensity g hg hgm).eventMass A) (a : α) :
    (condition (R.withDensity g hg hgm) A hQ).mass a =
      (condition (R.withDensity f hf hfm) A hP).mass a *
      ((R.withDensity f hf hfm).eventMass A /
        (R.withDensity g hg hgm).eventMass A * (g a / f a)) := by
  classical
  by_cases ha : a ∈ A
  · simp only [condition, ha, ↓reduceIte]
    change R.mass a * g a / (R.withDensity g hg hgm).eventMass A =
      R.mass a * f a / (R.withDensity f hf hfm).eventMass A *
        ((R.withDensity f hf hfm).eventMass A /
          (R.withDensity g hg hgm).eventMass A * (g a / f a))
    field_simp [ne_of_gt hP, ne_of_gt hQ, ne_of_gt (hAf a ha)]
  · simp only [condition, ha, ↓reduceIte, zero_mul]

/-- The raw likelihood score on a common clipping event, at every integer moment. -/
theorem clipped_raw_moment (R : FiniteLaw α) (f g : α → ℝ)
    (hf : ∀ a, 0 ≤ f a) (hfm : R.expect f = 1)
    (A : Finset α) (hAf : ∀ a ∈ A, 1 / 2 ≤ f a)
    (hP : 0 < (R.withDensity f hf hfm).eventMass A) (k : ℕ) :
    (condition (R.withDensity f hf hfm) A hP).expect
        (fun a => |g a / f a - 1| ^ (k + 1)) ≤
      (2 : ℝ) ^ k / (R.withDensity f hf hfm).eventMass A *
        R.expect (fun a => |g a - f a| ^ (k + 1)) := by
  classical
  have hpoint (a : α) (ha : a ∈ A) :
      f a * |g a / f a - 1| ^ (k + 1) ≤
        (2 : ℝ) ^ k * |g a - f a| ^ (k + 1) := by
    have hp : 0 < f a := lt_of_lt_of_le (by norm_num) (hAf a ha)
    rw [div_sub_one (ne_of_gt hp), abs_div, abs_of_pos hp]
    have hi : 0 ≤ 1 / f a := by positivity
    have hi2 : 1 / f a ≤ 2 := (div_le_iff₀ hp).mpr (by linarith [hAf a ha])
    calc
      _ = |g a - f a| ^ (k + 1) * (1 / f a) ^ k := by
        rw [div_pow, div_pow, one_pow, pow_succ (f a)]
        field_simp [ne_of_gt hp]
      _ ≤ _ := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hi hi2 k) (show 0 ≤ |g a - f a| ^ (k + 1) by positivity)
  unfold expect
  calc
    _ = ∑ a ∈ A, (R.mass a * (f a * |g a / f a - 1| ^ (k + 1))) /
          (R.withDensity f hf hfm).eventMass A := by
      simp only [condition, withDensity]
      simp_rw [ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ ∑ a ∈ A, ((2 : ℝ) ^ k * (R.mass a * |g a - f a| ^ (k + 1))) /
          (R.withDensity f hf hfm).eventMass A := by
      apply Finset.sum_le_sum
      intro a ha
      apply div_le_div_of_nonneg_right _ hP.le
      nlinarith [mul_le_mul_of_nonneg_left (hpoint a ha) (R.nonneg a)]
    _ ≤ ∑ a, ((2 : ℝ) ^ k * (R.mass a * |g a - f a| ^ (k + 1))) /
          (R.withDensity f hf hfm).eventMass A := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro a _ _
      positivity [R.nonneg a]
    _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]; ring

/-- Normalizing the second conditioned law costs only its scalar normalization error. -/
theorem score_rescaling_moment (P : FiniteLaw α) (u : α → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (k : ℕ) :
    P.expect (fun a => |c * u a - 1| ^ (k + 1)) ≤
      2 ^ k * (c ^ (k + 1) * P.expect (fun a => |u a - 1| ^ (k + 1)) +
        |c - 1| ^ (k + 1)) := by
  have hb (a : α) : |c * u a - 1| ^ (k + 1) ≤
      2 ^ k * (c ^ (k + 1) * |u a - 1| ^ (k + 1) + |c - 1| ^ (k + 1)) := by
    have he : c * u a - 1 = c * (u a - 1) + (c - 1) := by ring
    rw [he]
    calc
      _ ≤ (|c * (u a - 1)| + |c - 1|) ^ (k + 1) :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) _
      _ ≤ _ := by
        have h := add_pow_le (abs_nonneg (c * (u a - 1))) (abs_nonneg (c - 1)) (k + 1)
        simpa only [Nat.add_sub_cancel, abs_mul, abs_of_nonneg hc, mul_pow] using h
  unfold expect
  calc
    _ ≤ ∑ a, P.mass a * (2 ^ k * (c ^ (k + 1) * |u a - 1| ^ (k + 1) +
        |c - 1| ^ (k + 1))) := Finset.sum_le_sum (fun a _ =>
          mul_le_mul_of_nonneg_left (hb a) (P.nonneg a))
    _ = 2 ^ k * (c ^ (k + 1) * (∑ a, P.mass a * |u a - 1| ^ (k + 1)) +
        |c - 1| ^ (k + 1) * ∑ a, P.mass a) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
    _ = _ := by rw [P.total, mul_one]
end TraceReconstruction.FiniteLaw

namespace TraceReconstruction
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]
def coordinateProduct {n : ℕ} (P : Fin n → FiniteLaw α) : FiniteLaw (Fin n → α) where
  mass x := ∏ i, (P i).mass (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (P i).nonneg (x i))
  total := by rw [← Fintype.prod_sum]; simp only [FiniteLaw.total, Finset.prod_const_one]

def mixture (R : FiniteLaw β) (P : β → FiniteLaw α) : FiniteLaw α where
  mass a := ∑ b, R.mass b * (P b).mass a
  nonneg a := Finset.sum_nonneg (fun b _ => mul_nonneg (R.nonneg b) ((P b).nonneg a))
  total := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, FiniteLaw.total, mul_one]
    exact R.total
end FiniteLaw
variable {α Ω : Type*} [Fintype Ω]

def selectionCoefficient {n : ℕ} (θ σ : Fin n → Bool) : ℝ :=
  ∏ i, if σ i then (if θ i then 1 else 0) else 1

def selectionDensity {n : ℕ} (θ : Fin n → Bool) (Z : α → ℝ) (x : Fin n → α) : ℝ :=
  ∏ i, if θ i then 1 + Z (x i) else 1

def averagedCoefficient {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (σ : Fin n → Bool) : ℝ := R.expect (fun ω => selectionCoefficient (θ ω) σ)

def averagedDensity {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (Z : α → ℝ) (x : Fin n → α) : ℝ := R.expect (fun ω => selectionDensity (θ ω) Z x)

theorem selectionDensity_expansion {n : ℕ} (θ : Fin n → Bool) (Z : α → ℝ)
    (x : Fin n → α) : selectionDensity θ Z x = multilinear (selectionCoefficient θ) Z x := by
  unfold selectionDensity multilinear selectionCoefficient
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    (if b then (if θ i then (1 : ℝ) else 0) else 1) * (if b then Z (x i) else 1))]
  apply Finset.prod_congr rfl
  intro i _
  cases θ i <;> simp [add_comm]

theorem averagedDensity_expansion {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (Z : α → ℝ) (x : Fin n → α) :
    averagedDensity R θ Z x = multilinear (averagedCoefficient R θ) Z x := by
  unfold averagedDensity averagedCoefficient
  simp_rw [selectionDensity_expansion]
  unfold multilinear FiniteLaw.expect
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem averagedDensity_difference {n : ℕ} (R : FiniteLaw Ω)
    (θ φ : Ω → Fin n → Bool) (Z : α → ℝ) (x : Fin n → α) :
    averagedDensity R θ Z x - averagedDensity R φ Z x =
      multilinear (fun σ => averagedCoefficient R θ σ - averagedCoefficient R φ σ) Z x := by
  rw [averagedDensity_expansion, averagedDensity_expansion]
  simp only [multilinear, sub_mul, Finset.sum_sub_distrib]

theorem coefficient_nonneg {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (σ : Fin n → Bool) : 0 ≤ averagedCoefficient R θ σ := by
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg (R.nonneg ω)
  apply Finset.prod_nonneg
  intro i _
  cases σ i <;> cases θ ω i <;> norm_num

theorem coefficient_le_one {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool)
    (σ : Fin n → Bool) : averagedCoefficient R θ σ ≤ 1 := by
  rw [← R.total]
  apply Finset.sum_le_sum
  intro ω _
  have h : selectionCoefficient (θ ω) σ ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i _; cases σ i <;> cases θ ω i <;> norm_num
    · intro i _; cases σ i <;> cases θ ω i <;> norm_num
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h (R.nonneg ω)

/-- The coefficient for the empty subset is exactly one, before or after averaging. -/
theorem averagedCoefficient_empty {n : ℕ} (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) :
    averagedCoefficient R θ (fun _ => false) = 1 := by
  simp [averagedCoefficient, selectionCoefficient, FiniteLaw.expect, R.total]

/-- Exact density of the conditionally independent leaf oracle used in the source. -/
theorem leaf_oracle_density [Fintype α] {n : ℕ} (P Q : FiniteLaw α) (Z : α → ℝ)
    (hscore : ∀ a, Q.mass a = P.mass a * (1 + Z a))
    (R : FiniteLaw Ω) (θ : Ω → Fin n → Bool) (x : Fin n → α) :
    (R.mixture (fun ω => FiniteLaw.coordinateProduct (fun i => if θ ω i then Q else P))).mass x =
      (∏ i, P.mass (x i)) * averagedDensity R θ Z x := by
  unfold FiniteLaw.mixture FiniteLaw.coordinateProduct averagedDensity FiniteLaw.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  have he : (∏ i, (if θ ω i then Q else P).mass (x i)) =
      (∏ i, P.mass (x i)) * selectionDensity (θ ω) Z x := by
    rw [selectionDensity, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases θ ω i <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one, hscore]
  change R.mass ω * (∏ i, (if θ ω i then Q else P).mass (x i)) =
    (∏ i, P.mass (x i)) * (R.mass ω * selectionDensity (θ ω) Z x)
  rw [he]
  ring
end TraceReconstruction

end
end

end OAI

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

namespace MatrixMultiplication.PermutationMatching

open scoped BigOperators
open Classical

noncomputable section

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def average (f : Ω → ℝ) : ℝ := (∑ ω, f ω) / Fintype.card Ω

theorem average_congr {f g : Ω → ℝ} (h : ∀ ω, f ω = g ω) :
    average f = average g := by
  unfold average
  congr 1
  exact Finset.sum_congr rfl (fun ω _ => h ω)

@[simp] theorem average_const [Nonempty Ω] (c : ℝ) :
    average (fun _ : Ω => c) = c := by
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [average, hcard]

@[simp] theorem average_zero : average (fun _ : Ω => (0 : ℝ)) = 0 := by
  simp [average]

theorem average_add (f g : Ω → ℝ) :
    average (fun ω => f ω + g ω) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

theorem average_sub (f g : Ω → ℝ) :
    average (fun ω => f ω - g ω) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, sub_div]

theorem average_mul_const (f : Ω → ℝ) (c : ℝ) :
    average (fun ω => f ω * c) = average f * c := by
  simp only [average, ← Finset.sum_mul]
  ring

theorem average_const_mul (c : ℝ) (f : Ω → ℝ) :
    average (fun ω => c * f ω) = c * average f := by
  simp only [average, ← Finset.mul_sum]
  ring

theorem average_finset_sum {I : Type*} (s : Finset I) (f : I → Ω → ℝ) :
    average (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, average (f i) := by
  unfold average
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem average_sum {I : Type*} (s : Finset I) (f : Ω → I → ℝ) :
    average (fun ω => ∑ i ∈ s, f ω i) = ∑ i ∈ s, average (fun ω => f ω i) :=
  average_finset_sum s (fun i ω => f ω i)

theorem average_nonneg {f : Ω → ℝ} (h : ∀ ω, 0 ≤ f ω) : 0 ≤ average f := by
  exact div_nonneg (Finset.sum_nonneg (fun ω _ => h ω)) (Nat.cast_nonneg _)

theorem average_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω))
    (Nat.cast_nonneg _)

theorem average_indicator_eq (P : Ω → Prop) [DecidablePred P] :
    average (fun ω => if P ω then (1 : ℝ) else 0) =
      ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ) := by
  simp [average]

theorem average_equiv (e : Ω ≃ Γ) (f : Γ → ℝ) :
    average (fun ω => f (e ω)) = average f := by
  unfold average
  rw [Fintype.card_congr e, e.sum_comp]

theorem average_prod (f : Ω → ℝ) (g : Γ → ℝ) :
    average (fun p : Ω × Γ => f p.1 * g p.2) = average f * average g := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  exact mul_div_mul_comm _ _ _ _

theorem average_prod_average (f : Ω × Γ → ℝ) :
    average f = average (fun ω => average (fun γ => f (ω, γ))) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    div_eq_mul_inv, ← Finset.sum_mul, mul_inv_rev]
  ring

@[simp] theorem average_prod_fst [Nonempty Γ] (f : Ω → ℝ) :
    average (fun p : Ω × Γ => f p.1) = average f := by
  simpa using average_prod f (fun _ : Γ => (1 : ℝ))

@[simp] theorem average_prod_snd [Nonempty Ω] (g : Γ → ℝ) :
    average (fun p : Ω × Γ => g p.2) = average g := by
  simpa using average_prod (fun _ : Ω => (1 : ℝ)) g

theorem average_centered_sq [Nonempty Ω] (f : Ω → ℝ) :
    average (fun ω => (f ω - average f) ^ 2) =
      average (fun ω => f ω ^ 2) - (average f) ^ 2 := by
  calc
    average (fun ω => (f ω - average f) ^ 2) =
        average (fun ω => f ω ^ 2 - (2 * average f) * f ω + (average f) ^ 2) := by
      apply average_congr
      intro ω
      ring
    _ = _ := by rw [average_add, average_sub, average_const_mul, average_const]; ring

section Coordinates

variable {I : Type*} [Fintype I] [DecidableEq I] {X : I → Type*}
  [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]

theorem average_pi_eval (i : I) (f : X i → ℝ) :
    average (fun ω : ∀ i, X i => f (ω i)) = average f := by
  classical
  change average (fun ω => (fun p : X i × (∀ j : {j // j ≠ i}, X j) => f p.1)
    ((Equiv.piSplitAt i X) ω)) = average f
  rw [average_equiv (Equiv.piSplitAt i X)
    (fun p : X i × (∀ j : {j // j ≠ i}, X j) => f p.1), average_prod_fst]

theorem average_pi_restrict (D : Finset I) (f : (∀ i : {i // i ∈ D}, X i) → ℝ) :
    average (fun ω : ∀ i, X i => f (fun i => ω i)) = average f := by
  classical
  change average (fun ω =>
    (fun p : (∀ i : {i // i ∈ D}, X i) × (∀ i : {i // i ∉ D}, X i) => f p.1)
      ((Equiv.piEquivPiSubtypeProd (fun i => i ∈ D) X) ω)) = average f
  rw [average_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ D) X)
    (fun p : (∀ i : {i // i ∈ D}, X i) × (∀ i : {i // i ∉ D}, X i) => f p.1),
    average_prod_fst]

theorem average_prod_pi_restrict (D : Finset I)
    (f : ((∀ i : {i // i ∈ D}, X i) × (∀ i : {i // i ∈ D}, X i)) → ℝ) :
    average (fun p : (∀ i, X i) × (∀ i, X i) =>
      f ((fun i => p.1 i), (fun i => p.2 i))) = average f := by
  classical
  rw [average_prod_average]
  calc
    _ = average (fun x : ∀ i, X i =>
        average (fun y : ∀ i : {i // i ∈ D}, X i => f ((fun i => x i), y))) := by
      apply average_congr
      intro x
      exact average_pi_restrict D (fun y => f ((fun i => x i), y))
    _ = average (fun x : ∀ i : {i // i ∈ D}, X i => average (fun y => f (x, y))) :=
      average_pi_restrict D (fun x => average (fun y => f (x, y)))
    _ = average f := (average_prod_average f).symm

theorem average_pi_eval_mul (i j : I) (hij : i ≠ j) (f : X i → ℝ) (g : X j → ℝ) :
    average (fun ω : ∀ i, X i => f (ω i) * g (ω j)) = average f * average g := by
  classical
  change average (fun ω =>
    (fun p : X i × (∀ k : {k // k ≠ i}, X k) =>
      f p.1 * g (p.2 ⟨j, Ne.symm hij⟩)) ((Equiv.piSplitAt i X) ω)) = _
  rw [average_equiv (Equiv.piSplitAt i X)
    (fun p : X i × (∀ k : {k // k ≠ i}, X k) =>
      f p.1 * g (p.2 ⟨j, Ne.symm hij⟩)),
    average_prod f (fun k : ∀ k : {k // k ≠ i}, X k => g (k ⟨j, Ne.symm hij⟩))]
  exact congrArg (fun t => average f * t)
    (average_pi_eval (X := fun k : {k // k ≠ i} => X k) ⟨j, Ne.symm hij⟩ g)

theorem average_pi_sum_centered_sq (f : ∀ i, X i → ℝ) :
    average (fun ω : ∀ i, X i => (∑ i, (f i (ω i) - average (f i))) ^ 2) =
      ∑ i, average (fun x => (f i x - average (f i)) ^ 2) := by
  classical
  let c : ∀ i, X i → ℝ := fun i x => f i x - average (f i)
  have hc (i : I) : average (c i) = 0 := by
    simp [c, average_sub]
  change average (fun ω : ∀ i, X i => (∑ i, c i (ω i)) ^ 2) =
    ∑ i, average (fun x => (c i x) ^ 2)
  calc
    _ = ∑ i, ∑ j, average (fun ω : ∀ i, X i => c i (ω i) * c j (ω j)) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum, average_finset_sum]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        (∑ j, average (fun ω : ∀ i, X i => c i (ω i) * c j (ω j))) =
            average (fun ω : ∀ i, X i => c i (ω i) * c i (ω i)) := by
          apply Finset.sum_eq_single i
          · intro j hj hji
            rw [average_pi_eval_mul i j (Ne.symm hji), hc, hc, zero_mul]
          · simp
        _ = average (fun x => (c i x) ^ 2) := by
          simp only [pow_two]
          exact average_pi_eval i (fun x => c i x * c i x)

end Coordinates

theorem deviation_bound (f : Ω → ℝ) (μ δ : ℝ) (hδ : 0 < δ) :
    average (fun ω => if δ ≤ |f ω - μ| then (1 : ℝ) else 0) * δ ^ 2 ≤
      average (fun ω => (f ω - μ) ^ 2) := by
  rw [← average_mul_const]
  apply average_mono
  intro ω
  split_ifs with h
  · simp only [one_mul]
    have hh := (sq_le_sq₀ (le_of_lt hδ) (abs_nonneg (f ω - μ))).2 h
    simpa only [sq_abs] using hh
  · simp only [zero_mul]
    exact sq_nonneg _

theorem average_indicator_exists_le_sum {I : Type*} [Fintype I]
    (P : I → Ω → Prop) [∀ i ω, Decidable (P i ω)] :
    average (fun ω => if ∃ i, P i ω then (1 : ℝ) else 0) ≤
      ∑ i, average (fun ω => if P i ω then (1 : ℝ) else 0) := by
  classical
  rw [← average_finset_sum]
  apply average_mono
  intro ω
  by_cases h : ∃ i, P i ω
  · rw [ite_eq_left h]
    obtain ⟨i, hi⟩ := h
    calc
      (1 : ℝ) = (if P i ω then (1 : ℝ) else 0) := by simp [hi]
      _ ≤ ∑ j, if P j ω then (1 : ℝ) else 0 :=
        Finset.single_le_sum (f := fun j => if P j ω then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)

end

end MatrixMultiplication.PermutationMatching

end OAI

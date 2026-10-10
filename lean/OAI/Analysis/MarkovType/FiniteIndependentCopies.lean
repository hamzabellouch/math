import OAI.Analysis.MarkovType.FiniteProbability
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith

namespace OAI

noncomputable section

open scoped BigOperators

namespace MarkovSuperreflexivity
namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

def independentCopies (μ : FiniteLaw Ω) (m : ℕ) : FiniteLaw (Fin m → Ω) where
  mass x := ∏ i, μ.mass (x i)
  mass_nonneg x := Finset.prod_nonneg fun i _ => μ.mass_nonneg (x i)
  sum_mass := by
    rw [← Fintype.prod_sum]
    simp only [μ.sum_mass, Finset.prod_const_one]

@[simp]
theorem independentCopies_mass (μ : FiniteLaw Ω) (m : ℕ) (x : Fin m → Ω) :
    (μ.independentCopies m).mass x = ∏ i, μ.mass (x i) := rfl

@[simp]
theorem prob_true (μ : FiniteLaw Ω) : μ.prob (fun _ => True) = 1 := by
  simp [prob, μ.sum_mass]

@[simp]
theorem prob_false (μ : FiniteLaw Ω) : μ.prob (fun _ => False) = 0 := by
  simp [prob]

theorem prob_not (μ : FiniteLaw Ω) (A : Ω → Prop) :
    μ.prob (fun ω => ¬ A ω) = 1 - μ.prob A := by
  classical
  have hadd : μ.prob A + μ.prob (fun ω => ¬ A ω) = 1 := by
    unfold prob
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ ω, μ.mass ω := by
        apply Finset.sum_congr rfl
        intro ω _
        by_cases h : A ω <;> simp [h]
      _ = 1 := μ.sum_mass
  linarith

theorem independentCopies_prob_rect (μ : FiniteLaw Ω) (m : ℕ)
    (A : Fin m → Ω → Prop) :
    (μ.independentCopies m).prob (fun x => ∀ i, A i (x i)) =
      ∏ i, μ.prob (A i) := by
  classical
  unfold prob
  simp only [independentCopies_mass]
  trans (∑ x : Fin m → Ω, ∏ i, if A i (x i) then μ.mass (x i) else 0)
  · apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ∀ i, A i (x i)
    · simpa only [ite_eq_left hx] using
        (Fintype.prod_ite_zero (p := fun i => A i (x i))
          (f := fun i => μ.mass (x i))).symm
    · simpa only [ite_eq_right hx] using
        (Fintype.prod_ite_zero (p := fun i => A i (x i))
          (f := fun i => μ.mass (x i))).symm
  · exact (Fintype.prod_sum (fun i ω => if A i ω then μ.mass ω else 0)).symm

theorem independentCopies_prob_coord (μ : FiniteLaw Ω) {m : ℕ}
    (j : Fin m) (A : Ω → Prop) :
    (μ.independentCopies m).prob (fun x => A (x j)) = μ.prob A := by
  classical
  have h := μ.independentCopies_prob_rect m
    (fun i ω => if i = j then A ω else True)
  have hevent : (fun x : Fin m → Ω => ∀ i, if i = j then A (x i) else True) =
      (fun x => A (x j)) := by
    funext x
    apply propext
    constructor
    · intro hx
      simpa using hx j
    · intro hx i
      by_cases hij : i = j
      · subst i
        simpa using hx
      · simp [hij]
  rw [hevent] at h
  calc
    (μ.independentCopies m).prob (fun x => A (x j)) =
        ∏ i, μ.prob (fun ω => if i = j then A ω else True) := h
    _ = μ.prob (fun ω => if j = j then A ω else True) := by
      apply Finset.prod_eq_single j
      · intro i _ hij
        simp only [ite_eq_right hij, prob_true]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    _ = μ.prob A := by simp

theorem independentCopies_prob_all (μ : FiniteLaw Ω) (m : ℕ) (A : Ω → Prop) :
    (μ.independentCopies m).prob (fun x => ∀ i, A (x i)) = (μ.prob A) ^ m := by
  simpa using μ.independentCopies_prob_rect m (fun _ => A)

theorem independentCopies_expect_prod (μ : FiniteLaw Ω) (m : ℕ)
    (f : Fin m → Ω → ℝ) :
    (μ.independentCopies m).expect (fun x => ∏ i, f i (x i)) =
      ∏ i, μ.expect (f i) := by
  classical
  unfold expect
  simp only [independentCopies_mass, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => μ.mass ω * f i ω)).symm

theorem independentCopies_expect_coord (μ : FiniteLaw Ω) {m : ℕ}
    (j : Fin m) (f : Ω → ℝ) :
    (μ.independentCopies m).expect (fun x => f (x j)) = μ.expect f := by
  classical
  have h := μ.independentCopies_expect_prod m (fun i ω => if i = j then f ω else 1)
  have hprod (x : Fin m → Ω) : (∏ i, if i = j then f (x i) else 1) = f (x j) := by
    rw [Finset.prod_eq_single j]
    · simp
    · intro i _ hij
      simp only [ite_eq_right hij]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  simp_rw [hprod] at h
  calc
    (μ.independentCopies m).expect (fun x => f (x j)) =
        ∏ i, μ.expect (fun ω => if i = j then f ω else 1) := h
    _ = μ.expect (fun ω => if j = j then f ω else 1) := by
      apply Finset.prod_eq_single j
      · intro i _ hij
        simp only [ite_eq_right hij, expect_const]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    _ = μ.expect f := by simp

theorem independentCopies_prob_all_norm_le {E : Type*} [SeminormedAddCommGroup E]
    (μ : FiniteLaw Ω) (m : ℕ) (F : Ω → E) (t : ℝ) :
    (μ.independentCopies m).prob (fun x => ∀ i, ‖F (x i)‖ ≤ t) =
      (1 - μ.prob (fun ω => t < ‖F ω‖)) ^ m := by
  calc
    _ = (μ.prob (fun ω => ‖F ω‖ ≤ t)) ^ m :=
      μ.independentCopies_prob_all m (fun ω => ‖F ω‖ ≤ t)
    _ = _ := by
      have h := μ.prob_not (fun ω => t < ‖F ω‖)
      simpa only [not_lt] using congrArg (fun z : ℝ => z ^ m) h

end FiniteLaw
end MarkovSuperreflexivity

end

end OAI

import OAI.MeasureTheory.Falconer.Estimates.FiniteHolder
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace OAI

/-! # Finite coordinate splitting for the Loomis–Whitney induction -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

abbrev eraseFinCoordinate {X : Type*} {n : ℕ} (i : Fin (n+1))
    (z : Fin (n+1) → X) : Fin n → X := fun j => z (i.succAbove j)

theorem sum_tuple_cons {n : ℕ} (f : (Fin (n+1) → X) → ℝ) :
    (∑ z, f z) = ∑ x, ∑ y : Fin n → X, f (Fin.cons x y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => X)).sum_comp f]
  exact Fintype.sum_prod_type _

omit [Fintype X] in
@[simp] theorem remove_coordinate_cons_zero {n : ℕ} (x : X) (y : Fin n → X) :
    eraseFinCoordinate (0 : Fin (n+1)) (Fin.cons x y) = y := by
  ext j
  simp [eraseFinCoordinate]

omit [Fintype X] in
@[simp] theorem remove_coordinate_cons_succ {n : ℕ}
    (i : Fin (n+1)) (x : X) (y : Fin (n+1) → X) :
    eraseFinCoordinate i.succ (Fin.cons x y) = Fin.cons x (eraseFinCoordinate i y) :=
  Fin.cons_comp_succ_succAbove x y i

omit [Fintype X] in
theorem finite_holder_two_successor {n : ℕ} (B : Finset X) (f g : X → ℝ)
    (hf : ∀ x ∈ B, 0 ≤ f x) (hg : ∀ x ∈ B, 0 ≤ g x) :
    (∑ x ∈ B, (f x)^(1/((n+1:ℕ):ℝ))*(g x)^((n:ℝ)/(n+1:ℕ))) ≤
      (∑ x ∈ B, f x)^(1/((n+1:ℕ):ℝ))*(∑ x ∈ B, g x)^((n:ℝ)/(n+1:ℕ)) := by
  classical
  let h : Fin (n+1) → X → ℝ := Fin.cases f (fun _ => g)
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin (n+1))), ∀ x ∈ B, 0 ≤ h i x := by
    intro i _ x hx
    refine Fin.cases (hf x hx) (fun _ => hg x hx) i
  have hc := finite_holder_equal Finset.univ B (by simp) h hh
  have hp (u v : ℝ) (hv : 0 ≤ v) :
      (∏ i : Fin (n+1), (Fin.cases u (fun _ => v) i)^(1/((n+1:ℕ):ℝ))) =
        u^(1/((n+1:ℕ):ℝ))*v^((n:ℝ)/(n+1:ℕ)) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cases_zero,Fin.cases_succ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [← Real.rpow_mul_natCast hv]
    congr 2
    push_cast
    ring
  have hleft : (∑ x ∈ B, ∏ i : Fin (n+1), h i x^(1/((n+1:ℕ):ℝ))) =
      ∑ x ∈ B, f x^(1/((n+1:ℕ):ℝ))*g x^((n:ℝ)/(n+1:ℕ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← hp (f x) (g x) (hg x hx)]
    apply Finset.prod_congr rfl
    intro i _
    refine Fin.cases rfl (fun _ => rfl) i
  have hright : (∏ i : Fin (n+1), (∑ x ∈ B, h i x)^(1/((n+1:ℕ):ℝ))) =
      (∑ x ∈ B, f x)^(1/((n+1:ℕ):ℝ))*(∑ x ∈ B, g x)^((n:ℝ)/(n+1:ℕ)) := by
    have he : (fun i : Fin (n+1) => ∑ x ∈ B, h i x) =
        Fin.cases (∑ x ∈ B, f x) (fun _ => ∑ x ∈ B, g x) := by
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
    change (∏ i : Fin (n+1), ((fun i => ∑ x ∈ B, h i x) i)^(1/((n+1:ℕ):ℝ))) = _
    rw [he]
    exact hp _ _ (Finset.sum_nonneg hg)
  simpa only [Finset.card_univ,Fintype.card_fin,hleft,hright] using hc

end Falconer

end OAI

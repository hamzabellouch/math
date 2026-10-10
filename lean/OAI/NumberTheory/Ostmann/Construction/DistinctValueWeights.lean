import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

def tupleImage (b : ℕ) (x : Fin b → κ) : Finset κ := Finset.univ.image x

def imageFiber (b : ℕ) (S : Finset κ) : Finset (Fin b → κ) :=
  Finset.univ.filter (fun x => tupleImage b x=S)

theorem imageFiber_card_le (b : ℕ) (S : Finset κ) : (imageFiber b S).card≤b^b := by
  classical
  by_cases h : (imageFiber b S).Nonempty
  · obtain ⟨x,hx⟩ := h
    have hxeq : tupleImage b x=S := (Finset.mem_filter.mp hx).2
    have hS : S.card≤b := by
      rw [← hxeq]
      exact (Finset.card_image_le).trans (by simp)
    have hsub : imageFiber b S⊆Fintype.piFinset (fun _ : Fin b => S) := by
      intro y hy
      have hyeq := (Finset.mem_filter.mp hy).2
      apply Fintype.mem_piFinset.mpr
      intro i
      rw [← hyeq]
      exact Finset.mem_image_of_mem y (Finset.mem_univ i)
    calc
      _ ≤ (Fintype.piFinset (fun _ : Fin b => S)).card := Finset.card_le_card hsub
      _ = S.card^b := Fintype.card_piFinset_const S b
      _ ≤ b^b := Nat.pow_le_pow_left hS b
  · simp only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.card_empty]
    exact Nat.zero_le _

theorem tuple_distinct_weight_sum (b : ℕ) (w : κ → ℝ) :
    (∑ x : Fin b → κ, ∏ a∈tupleImage b x, w a) =
      ∑ S∈(Finset.univ : Finset κ).powerset, (imageFiber b S).card*(∏ a∈S, w a) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin b → κ)))
    (t := (Finset.univ : Finset κ).powerset) (g := tupleImage b)
    (fun x _ => Finset.mem_powerset.mpr (Finset.subset_univ _))]
  apply Finset.sum_congr rfl
  intro S hS
  have heq : (∑ x∈Finset.univ.filter (fun x => tupleImage b x=S),
      ∏ a∈tupleImage b x, w a) =
      ∑ _x∈imageFiber b S, ∏ a∈S, w a := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [heq]
  simp only [Finset.sum_const, nsmul_eq_mul]

theorem powerset_weight_sum_le_exp (w : κ → ℝ) (hw : ∀ a, 0≤w a) :
    (∑ S∈(Finset.univ : Finset κ).powerset, ∏ a∈S, w a) ≤ Real.exp (∑ a, w a) := by
  have heq : (∑ S∈(Finset.univ : Finset κ).powerset, ∏ a∈S, w a) =
      ∏ a, (w a+1) := by
    simpa only [Finset.prod_const_one, mul_one] using
      (Finset.prod_add w (fun _ => (1:ℝ)) Finset.univ).symm
  rw [heq, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro a ha
    exact add_nonneg (hw a) zero_le_one
  · intro a ha
    exact Real.add_one_le_exp _

theorem tuple_distinct_weight_sum_le (b : ℕ) (w : κ → ℝ) (hw : ∀ a, 0≤w a) :
    (∑ x : Fin b → κ, ∏ a∈tupleImage b x, w a) ≤
      (b:ℝ)^b*Real.exp (∑ a, w a) := by
  rw [tuple_distinct_weight_sum]
  calc
    _ ≤ ∑ S∈(Finset.univ : Finset κ).powerset, (b:ℝ)^b*(∏ a∈S, w a) := by
      apply Finset.sum_le_sum
      intro S hS
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast imageFiber_card_le b S
      · exact Finset.prod_nonneg (fun a _ => hw a)
    _ = (b:ℝ)^b*(∑ S∈(Finset.univ : Finset κ).powerset, ∏ a∈S, w a) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (powerset_weight_sum_le_exp w hw) (by positivity)

end Ostmann.Construction

end

end OAI

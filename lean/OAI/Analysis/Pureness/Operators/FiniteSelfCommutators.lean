import OAI.Analysis.Pureness.Operators.SelfCommutatorSeparation
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A]

lemma selfCommutator_star (a : A) : selfCommutator (star a) = -selfCommutator a := by
  apply Subtype.ext
  simp [selfCommutator, sub_eq_add_neg]

lemma selfCommutator_sqrt_smul (r : ℝ) (hr : 0 ≤ r) (a : A) :
    selfCommutator (Real.sqrt r • a) = r • selfCommutator a := by
  apply Subtype.ext
  simp only [selfCommutator, selfAdjoint.val_smul, star_smul, star_trivial,
    smul_mul_assoc, mul_smul_comm, smul_smul, Real.mul_self_sqrt hr, smul_sub]

lemma exists_selfCommutator_smul (r : ℝ) (a : A) :
    ∃ b : A, selfCommutator b = r • selfCommutator a := by
  by_cases hr : 0 ≤ r
  · exact ⟨Real.sqrt r • a, selfCommutator_sqrt_smul r hr a⟩
  · refine ⟨Real.sqrt (-r) • star a, ?_⟩
    rw [selfCommutator_sqrt_smul (-r) (by linarith), selfCommutator_star]
    simp

theorem selfCommutatorSpace_exists_list (x : selfAdjoint A)
    (hx : x ∈ selfCommutatorSpace) :
    ∃ l : List A, (l.map selfCommutator).sum = x := by
  classical
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact ⟨[a], by simp⟩
  | zero => exact ⟨[], by simp⟩
  | add y z _ _ hy hz =>
      obtain ⟨l, rfl⟩ := hy
      obtain ⟨k, rfl⟩ := hz
      exact ⟨l ++ k, by simp⟩
  | smul r y _ hy =>
      obtain ⟨l, rfl⟩ := hy
      choose b hb using exists_selfCommutator_smul (A := A) r
      refine ⟨l.map b, ?_⟩
      simp only [List.map_map, Function.comp_def, hb, List.smul_sum]

variable [PartialOrder A] [StarOrderedRing A]

theorem exists_list_selfCommutator_ge_half (h : ¬ Nonempty (TracialState A)) :
    ∃ l : List A, algebraMap ℝ A (1 / 2) ≤
      (l.map (fun a => star a * a - a * star a)).sum := by
  obtain ⟨m, hm, hbound⟩ := exists_selfCommutatorSpace_ge_half h
  obtain ⟨l, hl⟩ := selfCommutatorSpace_exists_list m hm
  refine ⟨l, ?_⟩
  have heq : ((l.map selfCommutator).sum : A) =
      (l.map (fun a => star a * a - a * star a)).sum := by
    clear hl
    induction l with
    | nil => rfl
    | cons a l ih => simpa [selfCommutator] using congrArg (fun x : A =>
        star a * a - a * star a + x) ih
  rw [← heq, hl]
  exact hbound

theorem exists_finite_selfCommutator_ge_half (h : ¬ Nonempty (TracialState A)) :
    ∃ (n : ℕ) (a : Fin n → A), algebraMap ℝ A (1 / 2) ≤
      ∑ i, (star (a i) * a i - a i * star (a i)) := by
  obtain ⟨l, hl⟩ := exists_list_selfCommutator_ge_half h
  refine ⟨l.length, l.get, ?_⟩
  rw [← Fin.sum_ofFn]
  change algebraMap ℝ A (1 / 2) ≤
    (List.ofFn ((fun a : A => star a * a - a * star a) ∘ l.get)).sum
  rw [← List.map_ofFn, List.ofFn_get]
  exact hl
end CuntzPureness

end

end OAI

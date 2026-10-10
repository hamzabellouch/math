import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Algebra.BigOperators.Ring.List

namespace OAI
namespace CuntzPureness
variable {A : Type*} [Ring A]

def finiteIdealSum (h : A) (l : List (A × A)) : A :=
  (l.map fun p => p.1 * h * p.2).sum

theorem exists_finiteIdealSum {h x : A} (hx : x ∈ TwoSidedIdeal.span {h}) :
    ∃ l : List (A × A), finiteIdealSum h l = x := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    have : x = h := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨[(1, 1)], by simp [finiteIdealSum]⟩
  | zero => exact ⟨[], rfl⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨l, rfl⟩ := ihx
    obtain ⟨m, rfl⟩ := ihy
    exact ⟨l ++ m, by simp [finiteIdealSum]⟩
  | neg x hx ih =>
    obtain ⟨l, rfl⟩ := ih
    refine ⟨l.map (fun p => (-p.1, p.2)), ?_⟩
    clear hx
    induction l with
    | nil => simp [finiteIdealSum]
    | cons p l ih =>
      simp_all [finiteIdealSum, List.map_map, Function.comp_def, neg_add_rev, add_comm]
  | left_absorb a x hx ih =>
    obtain ⟨l, rfl⟩ := ih
    refine ⟨l.map (fun p => (a * p.1, p.2)), ?_⟩
    simp [finiteIdealSum, List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]
  | right_absorb b x hx ih =>
    obtain ⟨l, rfl⟩ := ih
    refine ⟨l.map (fun p => (p.1, p.2 * b)), ?_⟩
    simp only [finiteIdealSum, List.map_map, Function.comp_def]
    simpa only [mul_assoc] using
      (List.sum_map_mul_right (l := l) (f := fun p => p.1 * h * p.2) (r := b))
end CuntzPureness

end OAI

import Mathlib
import OAI.Probability.CriticalPercolation.Modular.PushMass

namespace OAI

section
section
namespace CriticalPercolation.FiniteEntropy
open scoped Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
lemma supported_event_entropy (P R : X → ℝ) (hP : ∀ x, 0 ≤ P x)
    (hP1 : ∑ x, P x = 1) (hR : ∀ x, 0 < R x) (A : Set X)
    (hs : ∀ x, P x ≠ 0 → x ∈ A) :
    0 < (∑ x, if x ∈ A then R x else 0) ∧
      Real.log (1/(∑ x, if x ∈ A then R x else 0)) ≤ divergence P R := by
  let R' : X → ℝ := fun x => if x ∈ A then R x else 0
  have hn : ∀ x, 0 ≤ R' x := by
    intro x
    unfold R'
    split_ifs
    · exact (hR x).le
    · exact le_rfl
  have hp : ∀ x, 0 < P x → 0 < R' x := by
    intro x hx
    simp only [R',ite_eq_left (hs x hx.ne')]
    exact hR x
  have ho : 0 < ∑ x, R' x := by
    have hh := normalizer_pos P R' hP hn hP1 hp (fun _ => 0)
    simpa only [Real.exp_zero,mul_one] using hh
  refine ⟨ho,?_⟩
  have hh := log_sum_inequality P R' hP hn hp
  rw [hP1,one_mul] at hh
  refine hh.trans_eq ?_
  unfold divergence
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P x=0
  · simp only [hx,zero_mul]
  · simp only [R',ite_eq_left (hs x hx)]

omit [Fintype Y] in
lemma pushMass_supported (P : X → ℝ) (f : X → Y) (A : Set Y)
    (hs : ∀ x, P x ≠ 0 → f x ∈ A) (y : Y) (hy : pushMass f P y ≠ 0) : y ∈ A := by
  by_contra hn
  apply hy
  unfold pushMass
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : f x=y
  · rw [ite_eq_left hx]
    by_contra hp
    exact hn (hx ▸ hs x hp)
  · exact ite_eq_right hx

end CriticalPercolation.FiniteEntropy
end
end

end OAI

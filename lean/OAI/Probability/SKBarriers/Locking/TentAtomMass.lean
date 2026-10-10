import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarLocalTentMoments

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic

theorem scalarTentAtomMass_nonneg (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i,m i∈Icc (0:ℝ) 1) (hs : Monotone m) (l s : Fin (n+1)) :
    0 ≤ scalarTentAtomMass n m l s := by
  exact Finset.sum_nonneg (fun j _ => hierarchyAtom_nonneg n m zero_le_one (fun i => (hm i).1)
    (fun i => (hm i).2) hs j)

theorem scalarTentAtomMass_eq (n : ℕ) (m : Fin n → ℝ) (l s : Fin (n+1)) (hls : l<s) :
    scalarTentAtomMass n m l s=m ⟨s.val-1,by have := s.isLt; omega⟩-
      m ⟨l.val,by have := s.isLt; change l.val<s.val at hls; omega⟩ := by
  let i : Fin n := ⟨l.val,by have := s.isLt; change l.val<s.val at hls; omega⟩
  let k : Fin n := ⟨s.val-1,by have := s.isLt; omega⟩
  have H := congrArg₂ (fun a b : ℝ => a-b) (hierarchyAtom_tail_sum n m 1 i) (hierarchyAtom_tail_sum n m 1 k)
  rw [← Finset.sum_sub_distrib] at H
  have he : (∑ j : Fin (n+1), ((if i.val<j.val then hierarchyAtom n m 1 j else 0)-
      (if k.val<j.val then hierarchyAtom n m 1 j else 0)))=scalarTentAtomMass n m l s := by
    unfold scalarTentAtomMass
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    have hls' : l.val<s.val := hls
    dsimp only [i,k]
    by_cases hlj : l.val<j.val
    · by_cases hjs : j.val<s.val
      · simp only [hlj,show ¬s.val-1<j.val by omega,ite_true,ite_false,sub_zero]
        rw [ite_eq_left ⟨hlj,hjs⟩]
      · simp only [hlj,show s.val-1<j.val by omega,ite_true,sub_self]
        rw [ite_eq_right (by intro h; exact hjs h.2)]
    · simp only [hlj,show ¬s.val-1<j.val by omega,ite_false,sub_self]
      rw [ite_eq_right (by intro h; exact hlj h.1)]
  rw [he] at H
  dsimp only [i,k] at H
  linarith

end SK.Analytic

end
end

end OAI

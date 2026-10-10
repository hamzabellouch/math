import OAI.NumberTheory.JointDickman.Amplification.SingularFactor

namespace OAI

/-! # Exact forward-row parametrization by the positive lag -/
namespace JointDickman
open Finset Classical

theorem sum_fin_forward_lags {M : ℕ} (i : Fin M) (H T : ℕ) (f : ℕ → ℂ) :
    (∑ k : Fin M, if i < k ∧ H < k.val-i.val ∧ k.val-i.val < T then f (k.val-i.val) else 0) =
      ∑ j ∈ range (T+1), if H < j ∧ j < min T (M-i.val) then f j else 0 := by
  rw [← sum_filter,← sum_filter]
  apply sum_bij (fun k _ => k.val-i.val)
  · intro k hk
    have hh := (mem_filter.mp hk).2
    have hik : i.val < k.val := hh.1
    simp only [mem_filter,mem_range,lt_min_iff]
    exact ⟨by omega,hh.2.1,hh.2.2,by omega⟩
  · intro k hk l hl hkl
    have hk' : i.val < k.val := (mem_filter.mp hk).2.1
    have hl' : i.val < l.val := (mem_filter.mp hl).2.1
    apply Fin.ext
    omega
  · intro j hj
    have hh := mem_filter.mp hj
    have hb := lt_min_iff.mp hh.2.2
    have hij : i.val+j < M := by omega
    refine ⟨⟨i.val+j,hij⟩,?_,?_⟩
    · simp only [mem_filter,mem_univ,true_and,Fin.lt_def]
      exact ⟨by omega,by simpa using hh.2.1,by simpa using hb.1⟩
    · simp
  · intro k _
    rfl

end JointDickman

end OAI

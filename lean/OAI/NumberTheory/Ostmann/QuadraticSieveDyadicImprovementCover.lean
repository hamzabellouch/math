import OAI.NumberTheory.Ostmann.QuadraticSieveRowInflationDyadic
import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeDyadic

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

def dyadicPrefixCover (j : ℕ) : Finset ℕ :=
  if j=0 then {1} else dyadicSquarefreeRows (2^(j-1))

theorem oddSquarefree_mem_dyadicPrefixCover {M v : ℕ}
    (hv : v ∈ oddSquarefreeUpTo M) :
    ∃ j ∈ Finset.range (Nat.log 2 M+2), v ∈ dyadicPrefixCover j := by
  classical
  have hv' := mem_oddSquarefreeUpTo.mp hv
  by_cases hv1 : v=1
  · refine ⟨0,by simp,?_⟩
    simp [dyadicPrefixCover,hv1]
  have hv2 : 2 ≤ v := by omega
  let j := Nat.log 2 (v-1)
  have hj : j ≤ Nat.log 2 M := Nat.log_mono_right (by omega)
  have hlo : 2^j ≤ v-1 := Nat.pow_log_le_self 2 (by omega)
  have hhi : v-1 < 2^(j+1) := Nat.lt_pow_succ_log_self (by decide) (v-1)
  refine ⟨j+1,Finset.mem_range.mpr (by omega),?_⟩
  simp only [dyadicPrefixCover,Nat.add_eq_zero_iff,one_ne_zero,and_false,ite_false,Nat.add_sub_cancel]
  apply mem_dyadicSquarefreeRows.mpr
  rw [pow_succ] at hhi
  exact ⟨by omega,by omega,hv'.2.2.1,hv'.2.2.2⟩

theorem dyadicPrefixCover_base_le {M j : ℕ} (hM : 0 < M)
    (hj : j ∈ Finset.range (Nat.log 2 M+2)) (hj0 : j ≠ 0) : 2^(j-1) ≤ M := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hj' := Finset.mem_range.mp hj
  exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:ℕ))
    (show previous+1-1 ≤ Nat.log 2 M by omega)).trans
    (Nat.pow_log_le_self 2 hM.ne')

theorem quadraticNorm_prefix_le_dyadic_cover (M N : ℕ) :
    quadraticNorm (oddSquarefreeUpTo M) (oddSquarefreeUpTo N) ≤
      ∑ j ∈ Finset.range (Nat.log 2 M+2), quadraticNorm (dyadicPrefixCover j) (oddSquarefreeUpTo N) :=
  quadraticNorm_le_sum_cover _ _ _ _ (fun v hv => oddSquarefree_mem_dyadicPrefixCover (v := v) hv)

theorem quadraticNorm_row_one_le (N : ℕ) : quadraticNorm {1} (oddSquarefreeUpTo N) ≤ N := by
  have hcard : (oddSquarefreeUpTo N).card ≤ N := by
    calc
      _ ≤ (Finset.Icc 1 N).card := Finset.card_filter_le _ _
      _ = N := by simp
  have hh := quadraticNorm_le_card_mul {1} (oddSquarefreeUpTo N)
  simp only [Finset.card_singleton,Nat.cast_one,one_mul] at hh
  exact hh.trans (by exact_mod_cast hcard)

end Ostmann.QuadraticSieve

end

end OAI

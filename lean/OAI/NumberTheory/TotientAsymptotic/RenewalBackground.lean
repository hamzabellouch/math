import OAI.NumberTheory.TotientAsymptotic.RenewalDifference
import OAI.NumberTheory.TotientAsymptotic.PrefixCoordinates

namespace OAI

/-! A positive ordered translate of the prefix simplex. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def renewalBackground (N : ℕ) (t : ℝ) (i : Fin N) : ℝ := t*g (N-i.val)

lemma renewal_reverse_sum {N i : ℕ} (hi : i < N) :
    (∑ j ∈ Finset.range N,if i < j then a (j-i)*g (N-j) else 0)=
      g (N-i)-a (N-i) := by
  have hrec := g_convolution (by omega : 0 < N-i)
  have hs : (∑ k ∈ Finset.range (N-i),g k*a (N-i-k))=
      a (N-i)+(∑ j ∈ Finset.range N,if i < j then a (j-i)*g (N-j) else 0) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_range.mpr (by omega : 0 < N-i))]
    simp only [g,Nat.sub_zero,one_mul]
    rw [add_comm]
    congr 1
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun k _ => N-k)
    · intro k hk
      obtain ⟨hk0,hk⟩ := Finset.mem_erase.mp hk
      have hkN := Finset.mem_range.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by omega⟩
    · intro k hk l hl he
      have hkN := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
      have hlN := Finset.mem_range.mp (Finset.mem_erase.mp hl).2
      omega
    · intro j hj
      obtain ⟨hj,hiJ⟩ := Finset.mem_filter.mp hj
      have hjN := Finset.mem_range.mp hj
      exact ⟨N-j,Finset.mem_erase.mpr ⟨by omega,Finset.mem_range.mpr (by omega)⟩,
        by omega⟩
    · intro k hk
      have hkN := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
      have he : N-i-k=N-k-i := by omega
      have he' : N-(N-k)=k := by omega
      rw [he,he',mul_comm]
  linarith only [hs,hrec]

lemma renewalBackground_slack (N : ℕ) (t : ℝ) (i : Fin N) :
    prefixLinear N (renewalBackground N t) i=t*a (N-i.val) := by
  rw [prefixLinear_apply]
  have hs : (∑ j : Fin N,if i < j then a (j.val-i.val)*renewalBackground N t j else 0)=
      t*(g (N-i.val)-a (N-i.val)) := by
    rw [←renewal_reverse_sum i.isLt,Finset.mul_sum]
    simp only [renewalBackground,Fin.lt_def]
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      if i.val < j then a (j-i.val)*(t*g (N-j)) else 0)]
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> ring
  rw [hs]
  unfold renewalBackground
  ring

lemma renewalBackground_top (N : ℕ) (t : ℝ) :
    (∑ i : Fin N,a (i.val+1)*renewalBackground N t i)=
      t*(g (N+1)-a (N+1)) := by
  have hs := renewal_reverse_sum (i:=0) (N:=N+1) (by omega)
  rw [Finset.sum_range_succ'] at hs
  simp only [not_lt_zero,ite_false,add_zero,Nat.zero_lt_succ,ite_true,Nat.sub_zero] at hs
  rw [←hs,Finset.mul_sum]
  simp only [renewalBackground]
  rw [Fin.sum_univ_eq_sum_range (fun i => a (i+1)*(t*g (N-i)))]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [show N+1-(i+1)=N-i by omega]
  ring

lemma renewalBackground_gap {N : ℕ} (t : ℝ) (ht : 0 ≤ t) (i : Fin (N+1)) :
    t*a 1*g (N+1-i.val) ≤
      renewalBackground (N+2) t i.castSucc-renewalBackground (N+2) t i.succ := by
  have h := mul_le_mul_of_nonneg_left
    (renewal_difference_lower (n:=N+1-i.val) (by have := i.isLt; omega)) ht
  have he : N+2-i.val=(N+1-i.val)+1 := by have := i.isLt; omega
  simpa only [renewalBackground,Fin.val_castSucc,Fin.val_succ,
    show N+2-(i.val+1)=N+1-i.val by omega,he,mul_sub,mul_assoc] using h

theorem renewalBackground_uniform_gap : ∃ c : ℝ,0 < c ∧
    ∀ (N : ℕ) (t : ℝ),0 ≤ t → ∀ i : Fin (N+1),
      c*t*(rho^(N+2))⁻¹ ≤
        (renewalBackground (N+2) t i.castSucc-
          renewalBackground (N+2) t i.succ)/rho^(i.val+1) := by
  obtain ⟨c,hc,hgap⟩ := renewal_difference_uniform_lower
  refine ⟨c,hc,?_⟩
  intro N t ht i
  have hi : 1 ≤ N+1-i.val := by have := i.isLt; omega
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hgap _ hi) ht) (pow_pos rho_pos (i.val+1)).le
  have he : N+2-i.val=(N+1-i.val)+1 := by have := i.isLt; omega
  have hp : rho^(N+1-i.val)*rho^(i.val+1)=rho^(N+2) := by
    rw [←pow_add,show N+1-i.val+(i.val+1)=N+2 by have := i.isLt; omega]
  convert hh using 1
  · rw [←hp]
    field_simp [rho_pos.ne']
  · simp only [renewalBackground,Fin.val_castSucc,Fin.val_succ,
      show N+2-(i.val+1)=N+1-i.val by omega,he,mul_sub]

end TotientAsymptotic

end

end OAI

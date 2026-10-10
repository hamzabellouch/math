import OAI.Analysis.LipschitzHilbert.Estimates.FiniteRestrictedStrong

namespace OAI

/-! Null support-measure levels contribute zero and can be removed
before the positive-measure class argument. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

theorem finite_restricted_strong_nonneg (I J : Finset ℤ) (m n : ℤ → ℝ)
    (B : ℤ → ℤ → ℂ) (C : ℝ) (hC : 0≤C)
    (hm : ∀ i∈I, 0≤m i) (hn : ∀ j∈J, 0≤n j)
    (hB : ∀ i∈I, ∀ j∈J, ‖B i j‖≤
      C*((1+|Real.log (m i/n j)|)^3)⁻¹*Real.sqrt (m i)*Real.sqrt (n j)) :
    ‖∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j‖≤
      C*restrictedStrongConstant*
        Real.sqrt (∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2)*
        Real.sqrt (∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2) := by
  classical
  let Ip := I.filter (fun i => 0<m i)
  let Jp := J.filter (fun j => 0<n j)
  have hIp : Ip⊆I := Finset.filter_subset _ _
  have hJp : Jp⊆J := Finset.filter_subset _ _
  have hz (i : ℤ) (hi : i∈I) (j : ℤ) (hj : j∈J) (hzero : m i=0 ∨ n j=0) : B i j=0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    rcases hzero with he | he
    · simpa only [he,Real.sqrt_zero,mul_zero,zero_mul] using hB i hi j hj
    · simpa only [he,Real.sqrt_zero,mul_zero] using hB i hi j hj
  have heq : (∑ i∈Ip, ∑ j∈Jp, ((2:ℝ)^i*(2:ℝ)^j) • B i j)=
      ∑ i∈I, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j := by
    calc
      _ = ∑ i∈Ip, ∑ j∈J, ((2:ℝ)^i*(2:ℝ)^j) • B i j := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_subset hJp
        intro j hj hjp
        have hn0 : n j=0 := le_antisymm (le_of_not_gt (by simpa only [Jp,Finset.mem_filter,hj,true_and] using hjp)) (hn j hj)
        rw [hz i (hIp hi) j hj (Or.inr hn0),smul_zero]
      _ = _ := by
        apply Finset.sum_subset hIp
        intro i hi hip
        have hm0 : m i=0 := le_antisymm (le_of_not_gt (by simpa only [Ip,Finset.mem_filter,hi,true_and] using hip)) (hm i hi)
        exact Finset.sum_eq_zero (fun j hj => by rw [hz i hi j hj (Or.inl hm0),smul_zero])
  rw [←heq]
  have h := finite_restricted_strong Ip Jp m n B C hC
    (fun i hi => (Finset.mem_filter.mp hi).2) (fun j hj => (Finset.mem_filter.mp hj).2)
    (fun i hi j hj => hB i (hIp hi) j (hJp hj))
  apply h.trans
  have hE : (∑ i∈Ip, ((2:ℝ)^i*Real.sqrt (m i))^2)≤∑ i∈I, ((2:ℝ)^i*Real.sqrt (m i))^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hIp (fun _ _ _ => sq_nonneg _)
  have hF : (∑ j∈Jp, ((2:ℝ)^j*Real.sqrt (n j))^2)≤∑ j∈J, ((2:ℝ)^j*Real.sqrt (n j))^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hJp (fun _ _ _ => sq_nonneg _)
  have hconstant := restrictedStrongConstant_pos.le
  gcongr

end LipschitzHilbert

end

end OAI

import Mathlib

namespace OAI

section

section

noncomputable section
open Set Module

namespace WeakMTWTransport
section CenterRank
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma unit_positive_direction_of_rank_one_semibound (S : Submodule ℝ E)
    {p : E} {a b : ℝ} (ha : 0 < a) (hS : S≠⊥)
    (hbound : ∀ z ∈ S, a*‖z‖^2 ≤ b*(inner ℝ p z)^2) :
    ∃ e ∈ S, ‖e‖=1 ∧ 0 < inner ℝ p e ∧
      S=Submodule.span ℝ {e} ∧ a ≤ b*(inner ℝ p e)^2 := by
  have hk : ∀ z ∈ S, inner ℝ p z=0 → z=0 := by
    intro z hz hpz
    have H := hbound z hz
    rw [hpz,zero_pow (by norm_num : 2≠0),mul_zero] at H
    have Hsq : ‖z‖^2 ≤ 0 := (mul_le_mul_iff_of_pos_left ha).mp (by simpa only [mul_zero] using H)
    exact norm_eq_zero.mp (by nlinarith only [Hsq,norm_nonneg z,sq_nonneg ‖z‖])
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hpv : inner ℝ p v≠0 := fun H => hv0 (hk v hv H)
  obtain ⟨w,hw,hw0,hpw⟩ : ∃ w:E,w∈S ∧ w≠0 ∧ 0 < inner ℝ p w := by
    rcases lt_or_gt_of_ne hpv with h | h
    · exact ⟨-v,S.neg_mem hv,neg_ne_zero.mpr hv0,by simpa using neg_pos.mpr h⟩
    · exact ⟨v,hv,hv0,h⟩
  let e : E := ‖w‖⁻¹ • w
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have heS : e∈S := S.smul_mem _ hw
  have hen : ‖e‖=1 := by dsimp [e]; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hwn.le),inv_mul_cancel₀ hwn.ne']
  have hpe : 0 < inner ℝ p e := by
    change 0 < inner ℝ p (‖w‖⁻¹ • w)
    rw [inner_smul_right]
    exact mul_pos (inv_pos.mpr hwn) hpw
  have hspan : S=Submodule.span ℝ {e} := by
    apply le_antisymm
    · intro z hz
      have heq : z=((inner ℝ p z)/(inner ℝ p e)) • e := by
        apply sub_eq_zero.mp
        apply hk _ (S.sub_mem hz (S.smul_mem _ heS))
        rw [inner_sub_right,inner_smul_right,div_mul_cancel₀ _ hpe.ne',sub_self]
      rw [heq]
      exact (Submodule.span ℝ {e}).smul_mem _ (Submodule.subset_span (mem_singleton e))
    · exact Submodule.span_le.mpr (singleton_subset_iff.mpr heS)
  refine ⟨e,heS,hen,hpe,hspan,?_⟩
  simpa only [hen,one_pow,mul_one] using hbound e heS
end CenterRank
end WeakMTWTransport

end

end

end

end OAI

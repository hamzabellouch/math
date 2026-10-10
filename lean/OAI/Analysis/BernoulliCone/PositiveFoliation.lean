import OAI.Analysis.BernoulliCone.UpperFamily

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology
namespace Bernoulli.Foliation

lemma strict_increase_above_zero {f:ℝ→ℝ} {a b:ℝ} (hab:a<b)
    (hc:ContinuousOn f (Icc a b)) (ha:0<f a)
    (hd:∀t∈Ico a b, 0<f t → ∃v:ℝ, 0<v ∧ HasDerivWithinAt f v (Ici t) t) : f a<f b := by
  by_contra hn
  have hba:f b≤f a:=not_lt.mp hn
  obtain ⟨c,hcI,hmax⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le) hc
  have hfa:f a≤f c:=hmax ⟨le_rfl,hab.le⟩
  have hbad (t:ℝ) (ht:t∈Ico a b) (htp:0<f t) (hm:IsMaxOn f (Icc a b) t) : False := by
    obtain ⟨v,hv,hdv⟩:=hd t ht htp
    have hm':IsMaxOn f (Icc t b) t := by
      intro y hy
      exact hm (Icc_subset_Icc_left ht.1 hy)
    have hs:segment ℝ t b⊆Icc t b:=by rw [segment_eq_Icc ht.2.le]
    have hcT:=sub_mem_posTangentConeAt_of_segment_subset hs
    have hh:=hm'.isLocalMaxOn.hasFDerivWithinAt_nonpos
      (hdv.mono Icc_subset_Ici_self).hasFDerivWithinAt hcT
    have he:v*(b-t)≤0:=by simpa only [ContinuousLinearMap.toSpanSingleton_apply,smul_eq_mul,mul_comm] using hh
    exact (not_le.mpr (mul_pos hv (sub_pos.mpr ht.2))) he
  rcases hfa.eq_or_lt with he|he
  · apply hbad a ⟨le_rfl,hab⟩ ha
    intro t ht
    exact (hmax ht).trans_eq he.symm
  · have hcb:c<b:=by
      rcases hcI.2.eq_or_lt with hh|hh
      · rw [hh] at he
        exact False.elim ((not_lt.mpr hba) he)
      · exact hh
    exact hbad c ⟨hcI.1,hcb⟩ (ha.trans he) hmax

lemma monotone_positive_part {f:ℝ→ℝ} {a b:ℝ} (hab:a≤b)
    (hc:ContinuousOn f (Icc a b))
    (hd:∀t∈Ico a b, 0<f t → ∃v:ℝ, 0<v ∧ HasDerivWithinAt f v (Ici t) t) :
    max (f a) 0 ≤ max (f b) 0 := by
  rcases hab.eq_or_lt with h|h
  · simp [h]
  · rcases lt_or_ge 0 (f a) with hp|hp
    · exact max_le_max ((strict_increase_above_zero h hc hp hd).le) le_rfl
    · rw [max_eq_right hp]
      exact le_max_right _ _

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
lemma hasDerivAt_dilate {f:E→ℝ} (x:E) {l:ℝ} (hl:l≠0) (hf:DifferentiableAt ℝ f (l⁻¹ • x)) :
    HasDerivAt (fun t:ℝ=>t*f (t⁻¹ • x))
      (f (l⁻¹ • x)-inner ℝ (l⁻¹ • x) (gradient f (l⁻¹ • x))) l := by
  have hd:=hf.hasFDerivAt.comp_hasDerivAt l (((hasDerivAt_id l).inv hl).smul_const x)
  convert! (hasDerivAt_id l).mul hd using 1
  simp only [Function.comp_apply, Pi.inv_apply, id_eq,one_mul,ContinuousLinearMap.map_smul,smul_eq_mul]
  rw [←inner_gradient_left,real_inner_smul_left,real_inner_comm x (gradient f (l⁻¹ • x))]
  field_simp
  ring
end Bernoulli.Foliation

end
end

end OAI

import Mathlib
import OAI.Analysis.Commutator.KaplanskyRational
import OAI.Analysis.Commutator.KaplanskySelfAdjoint

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

namespace Kadison.Kaplansky

open OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma contraction_apply {a : H →L[ℂ] H} (ha : ‖a‖≤1) (x : H) : ‖a x‖≤‖x‖ := by
  calc
    ‖a x‖≤‖a‖*‖x‖ := a.le_opNorm x
    _≤1*‖x‖ := mul_le_mul_of_nonneg_right ha (norm_nonneg x)
    _=‖x‖ := one_mul _

lemma clip_difference_apply {a b : H →L[ℂ] H} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (x : H) :
    ‖clip a x-clip b x‖≤2*‖(a-b) (kernel b x)‖+‖(a-b) (b (kernel b x))‖ := by
  rw [←sub_apply,clip_difference ha hb]
  simp only [sub_apply,smul_apply,mul_apply_eq_comp]
  calc
    ‖(2:ℝ) • (kernel a ((a-b) (kernel b x)))-clip a ((a-b) (b (kernel b x)))‖
      ≤‖(2:ℝ) • (kernel a ((a-b) (kernel b x)))‖+
        ‖clip a ((a-b) (b (kernel b x)))‖ := norm_sub_le _ _
    _≤2*‖(a-b) (kernel b x)‖+‖(a-b) (b (kernel b x))‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (contraction_apply (kernel_norm_le a) _) (by norm_num))
        (contraction_apply (clip_norm_le a) _)

lemma cfc_bicommutant (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (f : ℝ → ℝ) : cfc f T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
  intro c hc
  exact ((show Commute c T from hT c hc).symm.cfc_real f).symm.eq

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem selfAdjoint_contraction_finite_approx
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsClosed (S : Set (H →L[ℂ] H)))
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) (x : ι → H) (ε : ℝ) (hε : 0<ε) :
    ∃ a : H →L[ℂ] H, a∈S ∧ IsSelfAdjoint a ∧ ‖a‖≤1 ∧ ∀ i, ‖a (x i)-T (x i)‖<ε := by
  let : IsClosed (S : Set (H →L[ℂ] H)) := hS
  let b := lift T
  have hb : b∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) :=
    cfc_bicommutant S hT rationalLift
  have hsb : IsSelfAdjoint b := lift_selfAdjoint T
  have hcb : clip b=T := clip_lift hsT hnT
  let v : SumSpace (H:=H) (ι⊕ι) := WithLp.toLp 2
    (Sum.elim (fun i => kernel b (x i)) (fun i => b (kernel b (x i))))
  obtain ⟨a,ha,hsa,he⟩ := selfAdjoint_finite_approx (ι⊕ι) S hb hsb v (ε/3) (by positivity)
  refine ⟨clip a,?_,clip_selfAdjoint a,clip_norm_le a,?_⟩
  · exact cfc_mem (𝕜:=ℝ) (𝕜':=ℂ) (s:=S) rationalClip ha
  · intro i
    have h₁ : ‖(a-b) (kernel b (x i))‖<ε/3 := by
      have h := (PiLp.norm_apply_le (p:=2)
        (diagonal (H:=H) (ι⊕ι) a v-diagonal (H:=H) (ι⊕ι) b v) (Sum.inl i)).trans_lt he
      simpa only [PiLp.sub_apply,diagonal_apply,v,WithLp.ofLp_toLp,
        Sum.elim_inl,sub_apply] using h
    have h₂ : ‖(a-b) (b (kernel b (x i)))‖<ε/3 := by
      have h := (PiLp.norm_apply_le (p:=2)
        (diagonal (H:=H) (ι⊕ι) a v-diagonal (H:=H) (ι⊕ι) b v) (Sum.inr i)).trans_lt he
      simpa only [PiLp.sub_apply,diagonal_apply,v,WithLp.ofLp_toLp,
        Sum.elim_inr,sub_apply] using h
    rw [←hcb]
    exact (clip_difference_apply hsa hsb (x i)).trans_lt (by linarith)

end Kadison.Kaplansky

end

end
end

end OAI

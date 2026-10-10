import Mathlib
import OAI.Analysis.Commutator.CStarRangeLifts
import OAI.Analysis.Commutator.KaplanskyDensity

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace CStarAlgebra ComplexStarModule

namespace Kadison.Kaplansky

open OperatorAmplification ComplexStarModule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem selfAdjoint_contraction_finite_approx_of_clip
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hclip : ∀ a∈S, IsSelfAdjoint a → clip a∈S)
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) (x : ι → H) (ε : ℝ) (hε : 0<ε) :
    ∃ a : H →L[ℂ] H, a∈S ∧ IsSelfAdjoint a ∧ ‖a‖≤1 ∧ ∀ i, ‖a (x i)-T (x i)‖<ε := by
  let b := lift T
  have hb : b∈Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) :=
    cfc_bicommutant S hT rationalLift
  have hsb : IsSelfAdjoint b := lift_selfAdjoint T
  have hcb : clip b=T := clip_lift hsT hnT
  let v : SumSpace (H:=H) (ι⊕ι) := WithLp.toLp 2
    (Sum.elim (fun i => kernel b (x i)) (fun i => b (kernel b (x i))))
  obtain ⟨a,ha,hsa,he⟩ := selfAdjoint_finite_approx (ι⊕ι) S hb hsb v (ε/3) (by positivity)
  refine ⟨clip a,?_,clip_selfAdjoint a,clip_norm_le a,?_⟩
  · exact hclip a ha hsa
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

variable {A : Type*} [CStarAlgebra A]

variable (φ : A →⋆ₐ[ℂ] (H →L[ℂ] H))

lemma clip_mem_range {b : H →L[ℂ] H} (hb : IsSelfAdjoint b)
    (hr : b∈φ.range) : clip b∈φ.range := by
  obtain ⟨a,ha⟩ := hr
  change φ a=b at ha
  let a₀ : A := ℜ a
  have ha₀ : IsSelfAdjoint a₀ := (ℜ a).property
  have he : φ a₀=b := by rw [show a₀=(ℜ a:A) from rfl,map_realPart,ha,hb.coe_realPart]
  refine ⟨clip a₀,?_⟩
  change φ (clip a₀)=clip b
  rw [clip,φ.map_cfc rationalClip a₀ continuous_rationalClip.continuousOn
    (by fun_prop) ha₀ (ha₀.map φ),he]
  rfl

theorem range_selfAdjoint_contraction_finite_approx
    {T : H →L[ℂ] H} (hT : T∈Set.centralizer (Set.centralizer (φ.range : Set (H →L[ℂ] H))))
    (hsT : IsSelfAdjoint T) (hnT : ‖T‖≤1) (x : ι → H) (ε : ℝ) (hε : 0<ε) :
    ∃ a : A, IsSelfAdjoint a ∧ ‖a‖≤1 ∧ ∀ i, ‖φ a (x i)-T (x i)‖<ε := by
  obtain ⟨b,hb,hsb,hnb,he⟩ := selfAdjoint_contraction_finite_approx_of_clip ι φ.range
    (fun _ hr hs => clip_mem_range φ hs hr) hT hsT hnT x ε hε
  obtain ⟨a,hsa,hna,ha⟩ := CStarRangeLifts.selfAdjoint_contraction φ hsb hnb hb
  exact ⟨a,hsa,hna,by simpa only [ha] using he⟩

end Kadison.Kaplansky

end

end
end

end OAI

import OAI.Analysis.KadisonKastler.VectorBicentralizerLocal
import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra

namespace OAI

/-! # Vectors continuous for projection centrality -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def projectionVectorDefect (J : H ≃ₗᵢ⋆[ℂ] H) (p : AlgebraProjection M) : H →L[ℂ] H :=
  p.val.val-conjugationOperator J p.val.val

theorem projectionVectorDefect_eq (J : H ≃ₗᵢ⋆[ℂ] H) (p : AlgebraProjection M) (x : H) :
    projectionVectorDefect J p x=centralVectorDefect J x p.val.val := by
  rw [centralVectorDefect_apply]
  have hs : star p.val.val=p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  rw [hs]
  rfl

def ProjectionCentralVector (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p : AlgebraProjection M,
    ‖projectionVectorDefect J p ξ‖ < δ → ‖projectionVectorDefect J p η‖ < ε

def projectionCentralSpace (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) : Submodule ℂ H where
  carrier := ProjectionCentralVector (M := M) J ξ
  zero_mem' := by
    intro ε hε
    exact ⟨1,by norm_num,fun p _ => by simpa only [map_zero,norm_zero] using hε⟩
  add_mem' := by
    intro x y hx hy ε hε
    obtain ⟨δ,hδ,hd⟩ := hx (ε/2) (half_pos hε)
    obtain ⟨γ,hγ,hg⟩ := hy (ε/2) (half_pos hε)
    refine ⟨min δ γ,lt_min hδ hγ,?_⟩
    intro p hp
    rw [map_add]
    have h1 := hd p (hp.trans_le (min_le_left _ _))
    have h2 := hg p (hp.trans_le (min_le_right _ _))
    exact (norm_add_le _ _).trans_lt (by linarith only [h1,h2])
  smul_mem' := by
    intro c x hx ε hε
    have hden : 0 < ‖c‖+1 := by positivity
    obtain ⟨δ,hδ,hd⟩ := hx (ε/(‖c‖+1)) (div_pos hε hden)
    refine ⟨δ,hδ,?_⟩
    intro p hp
    rw [map_smul,norm_smul]
    have hh := (lt_div_iff₀ hden).mp (hd p hp)
    nlinarith [norm_nonneg (projectionVectorDefect J p x)]

theorem reference_mem_projectionCentralSpace (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    ξ ∈ projectionCentralSpace (M := M) J ξ :=
  fun ε hε => ⟨ε,hε,fun _ h => h⟩

theorem projectionVectorDefect_conjugate (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (p : AlgebraProjection M) (x : H) :
    projectionVectorDefect J p (J x) = -J (projectionVectorDefect J p x) := by
  change p.val.val (J x)-J (p.val.val (J (J x))) =
    -J (p.val.val x-J (p.val.val (J x)))
  rw [hJ,map_sub,hJ]
  abel

theorem conjugate_mem_projectionCentralSpace (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (ξ : H) {η : H}
    (hη : η ∈ projectionCentralSpace (M := M) J ξ) :
    J η ∈ projectionCentralSpace (M := M) J ξ := by
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := hη ε hε
  refine ⟨δ,hδ,fun p hp => ?_⟩
  rw [projectionVectorDefect_conjugate J hJ,norm_neg,J.norm_map]
  exact hd p hp

variable [Nontrivial H]

theorem bicentralizer_vector_mem_projectionCentralSpace
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ) (a : Algebra M) (ha : vectorBicentralizerMember J ξ a) :
    a.val ξ ∈ projectionCentralSpace (M := M) J ξ := by
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := (vectorBicentralizerMember_iff_local J hJ hright ξ hξ a).mp ha
    ξ (ε/2) (half_pos hε)
  refine ⟨min δ (ε/(2*(‖a‖+1))),lt_min hδ (by positivity),?_⟩
  intro p hp
  have href : ‖centralVectorDefect J ξ p.val.val‖<δ := by
    rw [← projectionVectorDefect_eq]
    exact hp.trans_le (min_le_left _ _)
  have hc := hd p.val (p.property.norm_le _) href
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) a.val a.property
  have he : projectionVectorDefect J p (a.val ξ)=
      a.val (projectionVectorDefect J p ξ)-(a*p.val-p.val*a).val ξ := by
    change p.val.val (a.val ξ)-conjugationOperator J p.val.val (a.val ξ)=
      a.val (p.val.val ξ-conjugationOperator J p.val.val ξ)-
        (a.val (p.val.val ξ)-p.val.val (a.val ξ))
    have hh := congrArg (fun T : H →L[ℂ] H => T ξ) hcomm
    change a.val (conjugationOperator J p.val.val ξ)=conjugationOperator J p.val.val (a.val ξ) at hh
    rw [map_sub,hh]
    abel
  rw [he]
  apply (norm_sub_le _ _).trans_lt
  have hs : ‖a.val (projectionVectorDefect J p ξ)‖<ε/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(‖a‖+1))).mp
      (hp.trans_le (min_le_right _ _))
    have hb := a.val.le_opNorm (projectionVectorDefect J p ξ)
    change ‖a.val (projectionVectorDefect J p ξ)‖≤‖a‖*‖projectionVectorDefect J p ξ‖ at hb
    nlinarith [norm_nonneg (projectionVectorDefect J p ξ)]
  linarith

end

end KadisonKastler

end OAI

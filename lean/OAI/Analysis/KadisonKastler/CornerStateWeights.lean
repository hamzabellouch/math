import OAI.Analysis.KadisonKastler.TwoCornerStateNorm

namespace OAI

/-! # Normalized corner states of faithful vector states

The weights of a proper nonzero projection lie strictly between zero and
one. The two normalized compressions have norm at most one and reconstruct
a state centralizing the projection with exactly those scalar weights.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def projectionVectorWeight (p : AlgebraProjection M) (ξ : H) : ℝ := ‖p.val.val ξ‖^2

def vectorCornerState (p : AlgebraProjection M) (ξ : H) : Algebra M →L[ℂ] ℂ :=
  (projectionVectorWeight p ξ)⁻¹ • vectorFunctional (p.val.val ξ)

theorem cornerFunctional_vectorFunctional (p : AlgebraProjection M) (ξ : H) :
    cornerFunctional (vectorFunctional ξ) p.val = vectorFunctional (p.val.val ξ) := by
  ext a
  change inner ℂ ξ (p.val.val (a.val (p.val.val ξ))) =
    inner ℂ (p.val.val ξ) (a.val (p.val.val ξ))
  have hs : p.val.val.adjoint = p.val.val :=
    (p.property.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
  rw [← p.val.val.adjoint_inner_right,hs]

theorem vectorFunctional_projection (p : AlgebraProjection M) (ξ : H) :
    vectorFunctional ξ p.val = (projectionVectorWeight p ξ : ℂ) := by
  have hp := congrArg (fun a : Algebra M => a.val ξ) p.property.isIdempotentElem.eq
  change p.val.val (p.val.val ξ) = p.val.val ξ at hp
  have hs : p.val.val.adjoint = p.val.val :=
    (p.property.map M.toStarSubalgebra.subtype).isSelfAdjoint.star_eq
  change inner ℂ ξ (p.val.val ξ) = (‖p.val.val ξ‖^2 : ℝ)
  calc
    _ = inner ℂ ξ (p.val.val (p.val.val ξ)) := by rw [hp]
    _ = inner ℂ (p.val.val ξ) (p.val.val ξ) := by
      simpa only [hs] using p.val.val.adjoint_inner_right ξ (p.val.val ξ)
    _ = _ := by
      rw [inner_self_eq_norm_sq_to_K,← RCLike.ofReal_pow]
      rfl

theorem projectionVectorWeight_add_complement (p : AlgebraProjection M) (ξ : H) :
    projectionVectorWeight p ξ +
      projectionVectorWeight ⟨1-p.val,p.property.one_sub⟩ ξ = ‖ξ‖^2 := by
  exact projection_norm_sq_decomposition
    (p.property.map M.toStarSubalgebra.subtype) ξ

theorem projectionVectorWeight_pos (p : AlgebraProjection M) (ξ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ)) (hp : p.val ≠ 0) :
    0 < projectionVectorWeight p ξ := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  apply hp
  apply hξ
  change p.val.val ξ = (0 : H →L[ℂ] H) ξ
  simpa only [zero_apply] using hz

theorem projectionVectorWeight_mem_Ioo (p : AlgebraProjection M) (ξ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ)) (hunit : ‖ξ‖ = 1)
    (hp0 : p.val ≠ 0) (hp1 : p.val ≠ 1) :
    0 < projectionVectorWeight p ξ ∧ projectionVectorWeight p ξ < 1 := by
  have hp := projectionVectorWeight_pos p ξ hξ hp0
  have hq := projectionVectorWeight_pos ⟨1-p.val,p.property.one_sub⟩ ξ hξ
    (sub_ne_zero.mpr hp1.symm)
  have he := projectionVectorWeight_add_complement p ξ
  rw [hunit] at he
  exact ⟨hp,by linarith⟩

theorem vectorCornerState_norm_le (p : AlgebraProjection M) (ξ : H)
    (hp : 0 < projectionVectorWeight p ξ) : ‖vectorCornerState p ξ‖ ≤ 1 := by
  rw [vectorCornerState,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (projectionVectorWeight p ξ)⁻¹ * ‖p.val.val ξ‖^2 :=
      mul_le_mul_of_nonneg_left (vectorFunctional_norm_le _) (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

theorem weight_smul_vectorCornerState (p : AlgebraProjection M) (ξ : H)
    (hp : 0 < projectionVectorWeight p ξ) :
    projectionVectorWeight p ξ • vectorCornerState p ξ = vectorFunctional (p.val.val ξ) := by
  rw [vectorCornerState,smul_smul,mul_inv_cancel₀ hp.ne',one_smul]

theorem vectorFunctional_eq_weighted_corners (p : AlgebraProjection M) (ξ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ)) (hunit : ‖ξ‖ = 1)
    (hp0 : p.val ≠ 0) (hp1 : p.val ≠ 1)
    (hcentral : ∀ a : Algebra M,
      vectorFunctional ξ (p.val*a) = vectorFunctional ξ (a*p.val)) :
    vectorFunctional ξ = projectionVectorWeight p ξ • vectorCornerState p ξ +
      (1-projectionVectorWeight p ξ) •
        vectorCornerState ⟨1-p.val,p.property.one_sub⟩ ξ := by
  have hp := projectionVectorWeight_pos p ξ hξ hp0
  have hq := projectionVectorWeight_pos ⟨1-p.val,p.property.one_sub⟩ ξ hξ
    (sub_ne_zero.mpr hp1.symm)
  have he : 1-projectionVectorWeight p ξ =
      projectionVectorWeight ⟨1-p.val,p.property.one_sub⟩ ξ := by
    have he := projectionVectorWeight_add_complement p ξ
    rw [hunit] at he
    linarith
  rw [he,weight_smul_vectorCornerState p ξ hp,weight_smul_vectorCornerState _ ξ hq]
  rw [functional_eq_two_corners (vectorFunctional ξ) p.val p.property hcentral,
    cornerFunctional_vectorFunctional p ξ,
    cornerFunctional_vectorFunctional ⟨1-p.val,p.property.one_sub⟩ ξ]

end

end KadisonKastler

end OAI

import OAI.Analysis.KadisonKastler.PositiveConeOrthogonality
import OAI.Analysis.KadisonKastler.ProjectionPinchedState

namespace OAI

/-! # The state norm estimate from an orthogonal positive decomposition

This is the last step of Araki's Theorem 4(8), Pacific J. Math. 50 (1974),
309–354. A reflection in the support of the positive part witnesses the
state norm. The existence of the orthogonal decomposition is left explicit.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveStateEstimateRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem norm_sq_le_vectorState_norm_of_projection
    (η ζ α β : H) (hdiff : η-ζ=α-β)
    (p : AlgebraProjection M) (hpa : p.val.val α=α) (hpb : p.val.val β=0)
    (haζ : 0 ≤ inner ℝ α ζ) (hbη : 0 ≤ inner ℝ β η) :
    ‖η-ζ‖^2 ≤ ‖vectorFunctional (M := M) η-vectorFunctional ζ‖ := by
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  let s : Algebra M := (2:ℂ) • p.val-1
  have hsstar : star s.val=s.val := by
    change star ((2:ℂ) • p.val.val-1)=(2:ℂ) • p.val.val-1
    simp only [star_sub,star_smul,hp.isSelfAdjoint.star_eq,star_ofNat,star_one]
  have hsnorm : ‖s‖ ≤ 1 :=
    norm_unitary_le_one ⟨s.val,projectionReflection_unitary hp⟩
  have hsdiff : s.val (η-ζ)=α+β := by
    rw [hdiff]
    change ((2:ℂ) • p.val.val-1) (α-β)=α+β
    simp only [sub_apply,smul_apply,one_apply_eq_self,map_sub,hpa,hpb]
    module
  have heval : (((vectorFunctional (M := M) η-vectorFunctional ζ) : Algebra M →L[ℂ] ℂ) s).re =
      inner ℝ (α+β) (η+ζ) := by
    change (inner ℂ η (s.val η)-inner ℂ ζ (s.val ζ)).re=_
    have he : inner ℂ η (s.val η)-inner ℂ ζ (s.val ζ)=
        (inner ℂ (s.val (η-ζ)) (η+ζ)+inner ℂ (η+ζ) (s.val (η-ζ)))/2 := by
      rw [map_sub]
      simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right]
      have hswap (a b : H) : inner ℂ (s.val a) b=inner ℂ a (s.val b) := by
        rw [← ContinuousLinearMap.adjoint_inner_right,
          ← ContinuousLinearMap.star_eq_adjoint,hsstar]
      simp only [hswap]
      ring
    rw [he,hsdiff]
    have hhalf (z : ℂ) : (z/2).re=z.re/2 := by
      norm_num [Complex.div_re,Complex.normSq]
    rw [hhalf,Complex.add_re]
    change (inner ℝ (α+β) (η+ζ)+inner ℝ (η+ζ) (α+β))/2=_
    rw [real_inner_comm (η+ζ) (α+β)]
    ring
  have hinner : ‖η-ζ‖^2 ≤ inner ℝ (α+β) (η+ζ) := by
    have he : ‖η-ζ‖^2=inner ℝ (α-β) (η-ζ) := by
      rw [← hdiff,real_inner_self_eq_norm_sq]
    rw [he]
    simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right]
    linarith
  calc
    _ ≤ (((vectorFunctional (M := M) η-vectorFunctional ζ) : Algebra M →L[ℂ] ℂ) s).re := by rwa [heval]
    _ ≤ ‖((vectorFunctional (M := M) η-vectorFunctional ζ : Algebra M →L[ℂ] ℂ) s)‖ := Complex.re_le_norm _
    _ ≤ ‖vectorFunctional (M := M) η-vectorFunctional ζ‖*‖s‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) hsnorm

theorem positiveCone_norm_sq_le_state_norm_of_decomposition
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ α β : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (hα : α ∈ modularPositiveCone (M := M) J ξ)
    (hβ : β ∈ modularPositiveCone (M := M) J ξ)
    (horth : inner ℝ α β=0) (hdiff : η-ζ=α-β) :
    ‖η-ζ‖^2 ≤ ‖vectorFunctional (M := M) η-vectorFunctional ζ‖ := by
  exact norm_sq_le_vectorState_norm_of_projection η ζ α β hdiff
    (vectorSupportProjection M α) (vectorSupportProjection_apply M α)
    (positiveCone_support_kills_of_orthogonal J hJ hright hleft ξ hξ hpos hα hβ horth)
    (modularPositiveCone_acute J hJ hright ξ hpos hα hζ)
    (modularPositiveCone_acute J hJ hright ξ hpos hβ hη)

end

end KadisonKastler

end OAI

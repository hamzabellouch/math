import OAI.Analysis.KadisonKastler.PositiveConeProjectionSupport
import Mathlib.Algebra.QuadraticDiscriminant

namespace OAI

/-! # Orthogonal positive vectors have orthogonal algebra supports

The quadratic positivity of the generated modular cone suffices for this
step of Araki's Theorem 4(7), Pacific J. Math. 50 (1974), 309–354.
No self-duality or positive decomposition is assumed.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveOrthogonalityRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

private theorem linear_coefficient_eq_zero {A B : ℝ}
    (h : ∀ t : ℝ, 0 ≤ A*(t*t)+B*t) : B=0 := by
  have hd := discrim_le_zero (a := A) (b := B) (c := 0) (by simpa using h)
  simp only [discrim,mul_zero,sub_zero] at hd
  nlinarith [sq_nonneg B]

theorem positiveCone_inner_left_eq_zero_of_dual_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ)
    {η ζ : H} (hηJ : J η=η)
    (hdual : ∀ v ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ η v)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (horth : inner ℝ η ζ=0) (a : Algebra M) :
    inner ℂ η (a.val ζ)=0 := by
  have hζJ := modularPositiveCone_fixed J hright ξ hξ hζ
  have hreal (b : Algebra M) : (inner ℂ η (b.val ζ)).re=0 := by
    have hp (t : ℝ) : 0 ≤
        inner ℝ η (modularQuadratic J b ζ)*(t*t)+
          (2*inner ℝ η (b.val ζ))*t := by
      let c : Algebra M := 1+(t : ℂ) • b
      have hc := hdual _
        (modularQuadratic_preserves_positiveCone J hJ hright ξ c hζ)
      have he : conjugationOperator J c.val =
          1+(t : ℂ) • conjugationOperator J b.val := by
        change conjugationOperator J (1+(t : ℂ) • b.val)=_
        rw [conjugationOperator_add,conjugationOperator_one J hJ,conjugationOperator_smul]
        simp
      have hv : modularQuadratic J c ζ =
          ζ+(t : ℂ) • conjugationOperator J b.val ζ+
            (t : ℂ) • b.val ζ+((t*t : ℝ) : ℂ) • modularQuadratic J b ζ := by
        change (1+(t : ℂ) • b.val) (conjugationOperator J c.val ζ)=_
        rw [he]
        simp only [add_apply,one_apply_eq_self,smul_apply,map_add,map_smul,smul_add,
          smul_smul,modularQuadratic,mul_apply_eq_comp,Complex.ofReal_mul]
        abel
      have hs (v : H) : (t : ℂ) • v=t • v := by
        simpa only [Complex.coe_algebraMap] using (IsScalarTower.algebraMap_smul ℂ t v)
      have hs2 (v : H) : ((t*t : ℝ) : ℂ) • v=(t*t) • v := by
        simpa only [Complex.coe_algebraMap] using (IsScalarTower.algebraMap_smul ℂ (t*t) v)
      have heq : inner ℝ η (conjugationOperator J b.val ζ)=inner ℝ η (b.val ζ) := by
        simp only [real_inner_eq_re_inner]
        change (inner ℂ η (J (b.val (J ζ)))).re=_
        rw [hζJ,← hηJ,conjugateIsometry_inner]
        simp only [hηJ,RCLike.re_eq_complex_re,Complex.star_def,Complex.conj_re]
      rw [hv,inner_add_right,inner_add_right,inner_add_right,hs,hs,hs2,
        real_inner_smul_right,real_inner_smul_right,real_inner_smul_right,horth,heq] at hc
      nlinarith only [hc]
    have he := linear_coefficient_eq_zero hp
    change (inner ℂ η (b.val ζ)).re=0
    change 2*(inner ℂ η (b.val ζ)).re=0 at he
    linarith
  apply Complex.ext
  · exact hreal a
  · have hi := hreal (Complex.I • a)
    change (inner ℂ η (Complex.I • a.val ζ)).re=0 at hi
    rw [inner_smul_right] at hi
    simpa using hi

theorem positiveCone_inner_left_eq_zero_of_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (horth : inner ℝ η ζ=0) (a : Algebra M) :
    inner ℂ η (a.val ζ)=0 :=
  positiveCone_inner_left_eq_zero_of_dual_orthogonal J hJ hright ξ hξ
    (modularPositiveCone_fixed J hright ξ hξ hη)
    (fun _ hv => modularPositiveCone_acute J hJ hright ξ hpos hη hv) hζ horth a

/-- A positive support also kills orthogonal fixed vectors in the dual cone. -/
theorem positiveCone_support_kills_dual_of_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    {η ζ : H} (hηJ : J η=η)
    (hdual : ∀ v ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ η v)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (horth : inner ℝ η ζ=0) :
    (vectorSupportProjection M ζ).val.val η=0 := by
  have hζJ := modularPositiveCone_fixed J hright ξ hξ hζ
  have horbit (b : Algebra M.commutant) : inner ℂ (b.val ζ) η=0 := by
    have hb := positiveCone_inner_left_eq_zero_of_dual_orthogonal J hJ hright ξ hξ
      hηJ hdual hζ horth ⟨conjugationOperator J b.val,hleft b⟩
    change inner ℂ η (J (b.val (J ζ)))=0 at hb
    rw [hζJ,← hηJ,conjugateIsometry_inner] at hb
    have hh : inner ℂ η (b.val ζ)=0 := star_eq_zero.mp hb
    rwa [inner_eq_zero_symm]
  have hz : η ∈ (vectorOrbitClosure M.commutant.toStarSubalgebra ζ)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro v hv
    have hc : IsClosed {v : H | inner ℂ v η=0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    apply closure_minimal ?_ hc hv
    rintro v ⟨b,rfl⟩
    exact horbit b
  change (vectorOrbitClosure M.commutant.toStarSubalgebra ζ).starProjection η=0
  simpa only [Submodule.starProjection_apply,ZeroMemClass.coe_zero] using congrArg Subtype.val
    ((vectorOrbitClosure M.commutant.toStarSubalgebra ζ).orthogonalProjectionOnto_apply_of_mem_orthogonal hz)

/-- The support of one positive vector kills every orthogonal positive vector. -/
theorem positiveCone_support_kills_of_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (horth : inner ℝ η ζ=0) :
    (vectorSupportProjection M η).val.val ζ=0 := by
  have hηJ := modularPositiveCone_fixed J hright ξ hξ hη
  have hζJ := modularPositiveCone_fixed J hright ξ hξ hζ
  have horbit (b : Algebra M.commutant) : inner ℂ (b.val η) ζ=0 := by
    have hb := positiveCone_inner_left_eq_zero_of_orthogonal J hJ hright ξ hξ hpos
      hη hζ horth ⟨conjugationOperator J (star b).val,hleft (star b)⟩
    change inner ℂ η (J ((star b).val (J ζ)))=0 at hb
    rw [hζJ,← hηJ,conjugateIsometry_inner] at hb
    have hh : inner ℂ η ((star b).val ζ)=0 := star_eq_zero.mp hb
    simpa only [StarMemClass.coe_star,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right] using hh
  have hz : ζ ∈ (vectorOrbitClosure M.commutant.toStarSubalgebra η)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro v hv
    have hc : IsClosed {v : H | inner ℂ v ζ=0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    apply closure_minimal ?_ hc hv
    rintro v ⟨b,rfl⟩
    exact horbit b
  change (vectorOrbitClosure M.commutant.toStarSubalgebra η).starProjection ζ=0
  simpa only [Submodule.starProjection_apply,ZeroMemClass.coe_zero] using congrArg Subtype.val
    ((vectorOrbitClosure M.commutant.toStarSubalgebra η).orthogonalProjectionOnto_apply_of_mem_orthogonal hz)

/-- Both support projections are orthogonal in the ambient algebra. -/
theorem positiveCone_support_mul_eq_zero_of_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (horth : inner ℝ η ζ=0) :
    (vectorSupportProjection M η).val.val * (vectorSupportProjection M ζ).val.val=0 :=
  mul_vectorSupport_eq_zero M ζ (vectorSupportProjection M η).val
    (positiveCone_support_kills_of_orthogonal J hJ hright hleft ξ hξ hpos hη hζ horth)

end

end KadisonKastler

end OAI

import OAI.Analysis.KadisonKastler.PositiveConeDualProjection

namespace OAI

/-! # Self-duality on the conjugation-fixed real Hilbert space

A dual residual orthogonal to a positive vector is killed by its support.
Compressing the reference vector to the complementary corner then forces
that residual to vanish. Cyclicity of the reference is the only density
hypothesis. This proves the local self-duality needed for state estimates.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveSelfDualRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem positiveCone_dual_eq_zero_of_reference_orthogonal
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    {r : H} (hrJ : J r=r)
    (hdual : ∀ w ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ r w)
    (horth : inner ℝ r ξ=0) : r=0 := by
  have hcoeff (a : Algebra M) : inner ℂ r (a.val ξ)=0 :=
    positiveCone_inner_left_eq_zero_of_dual_orthogonal J hJ hright ξ hξ hrJ hdual
      (reference_mem_modularPositiveCone J hJ ξ) horth a
  apply ext_inner_right ℂ
  intro y
  simp only [inner_zero_left]
  apply hcyc.induction_on (p := fun y => inner ℂ r y=0) y
  · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  · exact hcoeff

theorem modularPositiveCone_mem_of_dual
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    {x : H} (hxJ : J x=x)
    (hxdual : ∀ w ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ x w) :
    x ∈ modularPositiveCone (M := M) J ξ := by
  obtain ⟨v,r,hv,hrJ,hrdual,hrv,hx⟩ :=
    exists_positiveCone_dual_decomposition J hright ξ hξ x hxJ
  let p := vectorSupportProjection M v
  let q : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  have hpv : p.val.val v=v := vectorSupportProjection_apply M v
  have hpr : p.val.val r=0 :=
    positiveCone_support_kills_dual_of_orthogonal J hJ hright hleft ξ hξ hrJ hrdual hv hrv
  have hqv : q.val.val v=0 := by
    change v-p.val.val v=0
    rw [hpv,sub_self]
  have hqr : q.val.val r=r := by
    change r-p.val.val r=r
    rw [hpr,sub_zero]
  have hvJ := modularPositiveCone_fixed J hright ξ hξ hv
  have hQv : modularQuadratic J q.val v=0 := by
    change q.val.val (J (q.val.val (J v)))=0
    rw [hvJ,hqv,map_zero,map_zero]
  have hQr : modularQuadratic J q.val r=r := by
    change q.val.val (J (q.val.val (J r)))=r
    rw [hrJ,hqr,hrJ,hqr]
  have hQstar : star (modularQuadratic J q.val)=modularQuadratic J q.val := by
    rw [modularQuadratic_star J hJ hright,q.property.isSelfAdjoint.star_eq]
  have hpair (z : H) : inner ℝ z (modularQuadratic J q.val ξ)=
      inner ℝ (modularQuadratic J q.val z) ξ := by
    simp only [real_inner_eq_re_inner]
    rw [← ContinuousLinearMap.adjoint_inner_left,← ContinuousLinearMap.star_eq_adjoint,hQstar]
  have hrξ : inner ℝ r ξ=0 := by
    have hnonneg := hrdual ξ (reference_mem_modularPositiveCone J hJ ξ)
    have hcut := hxdual (modularQuadratic J q.val ξ)
      (modularQuadratic_mem_positiveCone J ξ q.val)
    rw [hx,inner_sub_left,hpair v,hpair r,hQv,hQr,inner_zero_left] at hcut
    linarith
  have hr := positiveCone_dual_eq_zero_of_reference_orthogonal J hJ hright ξ hξ hcyc
    hrJ hrdual hrξ
  rw [hx,hr,sub_zero]
  exact hv

/-- Self-duality is stated on the real fixed space, without introducing a
new type or any claim that the complex Hilbert space is ordered. -/
theorem modularPositiveCone_mem_iff_dual
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ)) (x : H) :
    x ∈ modularPositiveCone (M := M) J ξ ↔
      J x=x ∧ ∀ w ∈ modularPositiveCone (M := M) J ξ, 0 ≤ inner ℝ x w := by
  constructor
  · intro hx
    exact ⟨modularPositiveCone_fixed J hright ξ hξ hx,
      fun _ hw => modularPositiveCone_acute J hJ hright ξ hpos hx hw⟩
  · rintro ⟨hxJ,hxdual⟩
    exact modularPositiveCone_mem_of_dual J hJ hright hleft ξ hξ hcyc hxJ hxdual

end

end KadisonKastler

end OAI

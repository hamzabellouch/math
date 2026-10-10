import OAI.Analysis.KadisonKastler.PositiveConeProjectionSupport

namespace OAI

/-! # The left support of a modular quadratic vector

For a positive vector, the kernel of `a J a J` on that vector is already
the kernel of the left action of `a`. This is the support calculation
needed for faithful finite matrix averaging.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveQuadraticRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

theorem positiveCone_operator_kills_of_quadratic_kills
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (a : Algebra M) (haη : modularQuadratic J a η = 0) : a.val η = 0 := by
  let b := star a * a
  have hηJ := modularPositiveCone_fixed J hright ξ hξ hη
  have hbη : modularQuadratic J b η = 0 := by
    rw [← modularQuadratic_mul J hJ hright]
    change modularQuadratic J (star a) (modularQuadratic J a η) = 0
    rw [haη,map_zero]
  have hpair : inner ℝ η (b.val η) = ‖a.val η‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [real_inner_eq_re_inner]
    change (inner ℂ η (a.val.adjoint (a.val η))).re = _
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [RCLike.re_eq_complex_re]
  have hpair' : inner ℝ η (conjugationOperator J b.val η) = ‖a.val η‖ ^ 2 := by
    rw [← hpair]
    simp only [real_inner_eq_re_inner]
    change (inner ℂ η (J (b.val (J η)))).re = _
    rw [hηJ]
    calc
      _ = (inner ℂ (J η) (J (b.val η))).re := by rw [hηJ]
      _ = _ := by
        rw [conjugateIsometry_inner]
        exact Complex.conj_re _
  have hlin (t : ℝ) : 0 ≤ ‖η‖ ^ 2 + 2 * t * ‖a.val η‖ ^ 2 := by
    let c : Algebra M := 1 + (t : ℂ) • b
    have hc := modularPositiveCone_acute J hJ hright ξ hpos hη
      (modularQuadratic_preserves_positiveCone J hJ hright ξ c hη)
    have he : conjugationOperator J c.val =
        1 + (t : ℂ) • conjugationOperator J b.val := by
      change conjugationOperator J (1 + (t : ℂ) • b.val) = _
      rw [conjugationOperator_add,conjugationOperator_one J hJ,conjugationOperator_smul]
      simp
    have hv : modularQuadratic J c η = η + (t : ℂ) •
        conjugationOperator J b.val η + (t : ℂ) • b.val η := by
      change (1 + (t : ℂ) • b.val) (conjugationOperator J c.val η) = _
      rw [he]
      change (η + (t : ℂ) • conjugationOperator J b.val η) +
        (t : ℂ) • b.val (η + (t : ℂ) • conjugationOperator J b.val η) = _
      have hz : b.val (conjugationOperator J b.val η) = 0 := hbη
      rw [map_add,map_smul,hz,smul_zero,add_zero]
    rw [hv,inner_add_right,inner_add_right] at hc
    have hs (v : H) : (t : ℂ) • v = t • v := by
      simpa only [Complex.coe_algebraMap] using (IsScalarTower.algebraMap_smul ℂ t v)
    simp only [hs,real_inner_smul_right,real_inner_self_eq_norm_sq,hpair,hpair'] at hc
    nlinarith only [hc]
  by_contra hn
  have hb : 0 < ‖a.val η‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have he := hlin (-(‖η‖ ^ 2 + 1) / (2 * ‖a.val η‖ ^ 2))
  have hcancel : 2 * (-(‖η‖ ^ 2 + 1) / (2 * ‖a.val η‖ ^ 2)) *
      ‖a.val η‖ ^ 2 = -(‖η‖ ^ 2 + 1) := by
    field_simp
  rw [hcancel] at he
  linarith

end

end KadisonKastler

end OAI

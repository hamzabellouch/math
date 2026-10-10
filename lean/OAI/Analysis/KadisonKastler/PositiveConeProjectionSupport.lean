import OAI.Analysis.KadisonKastler.ModularPositiveReal
import OAI.Analysis.KadisonKastler.ConjugateVectorSupport

namespace OAI

/-! # Projection supports of positive vectors

A projection kills a positive vector precisely when its matching left-right
corner does. This proves that positive summands cannot cancel on a left
support. No self-duality or state-representation theorem is assumed.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveProjectionRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

private theorem projection_pairing (p : H →L[ℂ] H) (hp : IsStarProjection p) (η : H) :
    inner ℝ η (p η) = ‖p η‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [real_inner_eq_re_inner]
  rw [← ContinuousLinearMap.adjoint_inner_right,← ContinuousLinearMap.star_eq_adjoint,
    hp.isSelfAdjoint.star_eq]
  exact congrArg (fun v => (inner ℂ η v).re)
    (congrArg (fun T : H →L[ℂ] H => T η) hp.isIdempotentElem.eq).symm

private theorem conjugation_projection (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (p : AlgebraProjection M) :
    IsStarProjection (conjugationOperator J p.val.val) := by
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  constructor
  · change conjugationOperator J p.val.val * conjugationOperator J p.val.val = _
    rw [← conjugationOperator_mul J hJ,hp.isIdempotentElem.eq]
  · change star (conjugationOperator J p.val.val) = _
    rw [← conjugationOperator_star J hJ,hp.isSelfAdjoint.star_eq]

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ = ξ)
  (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))

include hJ hright hξ hpos in
theorem positiveCone_projection_kills_of_corner_kills
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (p : AlgebraProjection M) (hpη : modularQuadratic J p.val η = 0) :
    p.val.val η = 0 := by
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  have hηJ := modularPositiveCone_fixed J hright ξ hξ hη
  have hnorm : ‖conjugationOperator J p.val.val η‖ = ‖p.val.val η‖ := by
    change ‖J (p.val.val (J η))‖ = _
    rw [hηJ,J.norm_map]
  have hpair := projection_pairing p.val.val hp η
  have hpair' := projection_pairing (conjugationOperator J p.val.val)
    (conjugation_projection J hJ p) η
  rw [hnorm] at hpair'
  have hlin (t : ℝ) : 0 ≤ ‖η‖ ^ 2 + 2 * t * ‖p.val.val η‖ ^ 2 := by
    let a : Algebra M := 1 + (t : ℂ) • p.val
    have ha := modularPositiveCone_acute J hJ hright ξ hpos hη
      (modularQuadratic_preserves_positiveCone J hJ hright ξ a hη)
    have he : conjugationOperator J a.val =
        1 + (t : ℂ) • conjugationOperator J p.val.val := by
      change conjugationOperator J (1 + (t : ℂ) • p.val.val) = _
      rw [conjugationOperator_add,conjugationOperator_one J hJ,
        conjugationOperator_smul]
      simp
    have hv : modularQuadratic J a η = η + (t : ℂ) •
        conjugationOperator J p.val.val η + (t : ℂ) • p.val.val η := by
      change (1 + (t : ℂ) • p.val.val) (conjugationOperator J a.val η) = _
      rw [he]
      change (η + (t : ℂ) • conjugationOperator J p.val.val η) +
        (t : ℂ) • p.val.val (η + (t : ℂ) • conjugationOperator J p.val.val η) = _
      have hz : p.val.val (conjugationOperator J p.val.val η) = 0 := hpη
      rw [map_add,map_smul,hz,smul_zero,add_zero]
    rw [hv,inner_add_right,inner_add_right] at ha
    have hs (v : H) : (t : ℂ) • v = t • v := by
      simpa only [Complex.coe_algebraMap] using (IsScalarTower.algebraMap_smul ℂ t v)
    simp only [hs,real_inner_smul_right,real_inner_self_eq_norm_sq,hpair,hpair'] at ha
    nlinarith only [ha]
  by_contra hn
  have hb : 0 < ‖p.val.val η‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have he := hlin (-(‖η‖ ^ 2 + 1) / (2 * ‖p.val.val η‖ ^ 2))
  have hcancel : 2 * (-(‖η‖ ^ 2 + 1) / (2 * ‖p.val.val η‖ ^ 2)) *
      ‖p.val.val η‖ ^ 2 = -(‖η‖ ^ 2 + 1) := by
    field_simp
  rw [hcancel] at he
  linarith

include hJ hright hξ hpos in
theorem positiveCone_projection_kills_summands
    {η ζ : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hζ : ζ ∈ modularPositiveCone (M := M) J ξ)
    (p : AlgebraProjection M) (hp : p.val.val (η+ζ) = 0) :
    p.val.val η = 0 ∧ p.val.val ζ = 0 := by
  have hproj : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val)
    p.val.val p.val.property
  have hQ : IsStarProjection (modularQuadratic J p.val) :=
    hproj.mul (conjugation_projection J hJ p) hcomm
  have hz : modularQuadratic J p.val (η+ζ) = 0 := by
    change (p.val.val * conjugationOperator J p.val.val) (η+ζ) = 0
    rw [hcomm]
    change conjugationOperator J p.val.val (p.val.val (η+ζ)) = 0
    rw [hp,map_zero]
  have hnonneg := modularPositiveCone_acute J hJ hright ξ hpos hη
    (modularQuadratic_preserves_positiveCone J hJ hright ξ p.val hζ)
  have hpair := congrArg (inner ℝ η) hz
  rw [map_add,inner_add_right,inner_zero_right,
    projection_pairing _ hQ] at hpair
  have hη0 : modularQuadratic J p.val η = 0 := by
    apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖modularQuadratic J p.val η‖]
  have hζ0 : modularQuadratic J p.val ζ = 0 := by
    rw [map_add,hη0,zero_add] at hz
    exact hz
  exact ⟨positiveCone_projection_kills_of_corner_kills J hJ hright ξ hξ hpos hη p hη0,
    positiveCone_projection_kills_of_corner_kills J hJ hright ξ hξ hpos hζ p hζ0⟩

end

end KadisonKastler

end OAI

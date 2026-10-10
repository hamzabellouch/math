import OAI.Analysis.KadisonKastler.PositiveConeFaithfulUniqueness
import OAI.Analysis.KadisonKastler.ProjectionPinchedState

namespace OAI

/-! # State centralizers on the constructed positive cone

A unitary centralizing a faithful positive vector state has zero central
vector defect for the same conjugation. This uses positive-state
uniqueness, not a new modular-conjugation identification assumption.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveCentralizerRealInner : InnerProductSpace ℝ H :=
  InnerProductSpace.complexToReal

theorem positiveCone_centralizer_unitary
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hs : Function.Injective (algebraVectorMap M η))
    (u : unitary (Algebra M))
    (hcentral : ∀ a : Algebra M,
      inner ℂ η ((u.val*a).val η) = inner ℂ η ((a*u.val).val η)) :
    centralVectorDefect J η u.val.val = 0 := by
  let U := ambientAlgebraUnitary u
  let V := conjugationUnitary J hJ U
  let ζ := modularQuadratic J u.val η
  have hV : (V : H →L[ℂ] H) ∈ M.commutant := hright u.val
  have hcomm : (U : H →L[ℂ] H) * V = (V : H →L[ℂ] H) * U :=
    VonNeumannAlgebra.mem_commutant_iff.mp hV U u.val.property
  have hζV : ζ = (V : H →L[ℂ] H) ((U : H →L[ℂ] H) η) :=
    congrArg (fun T : H →L[ℂ] H => T η) hcomm
  have hζ := modularQuadratic_preserves_positiveCone J hJ hright ξ u.val hη
  have hstate (a : Algebra M) : inner ℂ η (a.val η) = inner ℂ ζ (a.val ζ) := by
    have hc := hcentral (star u.val * a)
    rw [← mul_assoc,Unitary.mul_star_self_of_mem u.property,one_mul] at hc
    have hv := congrArg (fun φ : Algebra M →L[ℂ] ℂ => φ a)
      (vectorFunctional_commuting_unitary (M := M) ((U : H →L[ℂ] H) η) V hV)
    change inner ℂ ((V : H →L[ℂ] H) ((U : H →L[ℂ] H) η))
        (a.val ((V : H →L[ℂ] H) ((U : H →L[ℂ] H) η))) =
      inner ℂ ((U : H →L[ℂ] H) η) (a.val ((U : H →L[ℂ] H) η)) at hv
    calc
      _ = inner ℂ η (star (U : H →L[ℂ] H) (a.val ((U : H →L[ℂ] H) η))) := hc
      _ = inner ℂ ((U : H →L[ℂ] H) η) (a.val ((U : H →L[ℂ] H) η)) := by
        rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
      _ = _ := by rw [hζV]; exact hv.symm
  have hz := positiveCone_faithful_state_unique J hJ hright hleft ξ hξ hpos hη hζ hs hstate
  change (U : H →L[ℂ] H) ((V : H →L[ℂ] H) η) = η at hz
  have hVη : (V : H →L[ℂ] H) η = star (U : H →L[ℂ] H) η := by
    calc
      _ = star (U : H →L[ℂ] H) ((U : H →L[ℂ] H) ((V : H →L[ℂ] H) η)) := by
        change _ = (star (U : H →L[ℂ] H) * U) ((V : H →L[ℂ] H) η)
        rw [Unitary.star_mul_self_of_mem U.property,one_apply_eq_self]
      _ = _ := by rw [hz]
  have hηJ := modularPositiveCone_fixed J hright ξ hξ hη
  have hj := congrArg J hVη
  change J (J ((U : H →L[ℂ] H) (J η))) = J (star (U : H →L[ℂ] H) η) at hj
  rw [hJ,hηJ] at hj
  change (U : H →L[ℂ] H) η - J (star (U : H →L[ℂ] H) (J η)) = 0
  rw [hηJ]
  exact sub_eq_zero.mpr hj

theorem positiveCone_mem_centralVectorSpace
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ)
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hs : Function.Injective (algebraVectorMap M η))
    (N : VonNeumannAlgebra H) (hNM : N ≤ M)
    (hcentral : ∀ (a : Algebra N) (b : Algebra M),
      inner ℂ η ((a.val*b.val) η) = inner ℂ η ((b.val*a.val) η)) :
    η ∈ centralVectorSpace N J := by
  let inc := StarSubalgebra.inclusion hNM
  let D : Algebra N →ₗ[ℂ] H :=
    (centralVectorDefect J η).comp N.toStarSubalgebra.subtype.toLinearMap
  have hunit (u : unitary (Algebra N)) : D u.val = 0 := by
    let v := Unitary.map (StarMonoidHom.ofClass inc) u
    exact positiveCone_centralizer_unitary J hJ hright hleft ξ hξ hpos hη hs v
      (fun b => hcentral u.val b)
  intro a
  obtain ⟨u,c,ha,_⟩ := CStarAlgebra.exists_sum_four_unitary a
  have hz : D a = 0 := by
    rw [ha,map_sum]
    simp only [map_smul,hunit,smul_zero,Finset.sum_const_zero]
  exact sub_eq_zero.mp hz

end

end KadisonKastler

end OAI

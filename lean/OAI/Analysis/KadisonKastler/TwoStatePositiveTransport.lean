import OAI.Analysis.KadisonKastler.TwoStateCornerSupports

namespace OAI

/-! # Spatial transport determined by the positive two-state matrix vector -/

namespace KadisonKastler
open Generator
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H) (Ω ξ : H)
  (hc : DenseRange (algebraVectorMap (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ)))
  (d : ModularConjugationData (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ))

abbrev twoStateQuadraticBridge : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H :=
  modularQuadratic d.conjugation (twoStateEntry M 1 0 1)

include hc in
def twoStatePositiveTransport : H ≃ₗᵢ[ℂ] H :=
  partialIsometryCornerEquiv (twoStateCornerEmbedding 0) (twoStateCornerEmbedding 1)
    (twoStateQuadraticBridge M Ω ξ d)
    (twoStateEntry_quadratic_initial M Ω ξ hc d)
    (twoStateEntry_quadratic_final M Ω ξ hc d)

theorem twoStateQuadraticBridge_triple :
    twoStateQuadraticBridge M Ω ξ d * star (twoStateQuadraticBridge M Ω ξ d) *
      twoStateQuadraticBridge M Ω ξ d = twoStateQuadraticBridge M Ω ξ d := by
  dsimp only [twoStateQuadraticBridge]
  rw [modularQuadratic_star d.conjugation d.involutive (d.right_mem le_rfl),
    modularQuadratic_mul d.conjugation d.involutive (d.right_mem le_rfl),
    modularQuadratic_mul d.conjugation d.involutive (d.right_mem le_rfl),
    twoStateEntry_star, star_one, twoStateEntry_mul, one_mul, twoStateEntry_mul, one_mul]

theorem twoStatePositiveTransport_embedding (x : H) :
    twoStateCornerEmbedding 1 (twoStatePositiveTransport M Ω ξ hc d x) =
      twoStateQuadraticBridge M Ω ξ d (twoStateCornerEmbedding 0 x) := by
  rw [twoStatePositiveTransport, partialIsometryCornerEquiv_apply]
  change ((twoStateCornerEmbedding 1).toContinuousLinearMap.comp
    (twoStateCornerEmbedding 1).toContinuousLinearMap.adjoint)
      (twoStateQuadraticBridge M Ω ξ d (twoStateCornerEmbedding 0 x)) = _
  rw [← twoStateEntry_quadratic_final M Ω ξ hc d]
  have he := congrArg (fun T : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H =>
    T (twoStateCornerEmbedding 0 x)) (twoStateQuadraticBridge_triple M Ω ξ d)
  exact he

theorem twoStatePositiveTransport_inverse_embedding (x : H) :
    twoStateCornerEmbedding 0 ((twoStatePositiveTransport M Ω ξ hc d).symm x) =
      (twoStateQuadraticBridge M Ω ξ d).adjoint (twoStateCornerEmbedding 1 x) := by
  have he := congrArg (twoStateQuadraticBridge M Ω ξ d).adjoint
    (twoStatePositiveTransport_embedding M Ω ξ hc d
      ((twoStatePositiveTransport M Ω ξ hc d).symm x))
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  change _ = ((twoStateQuadraticBridge M Ω ξ d).adjoint.comp
    (twoStateQuadraticBridge M Ω ξ d)) _ at he
  rw [twoStateEntry_quadratic_initial M Ω ξ hc d] at he
  have hi := (twoStateCornerEmbedding (H := H) 0).adjoint_comp_self
  have hv (y : H) : (twoStateCornerEmbedding 0).toContinuousLinearMap.adjoint
      (twoStateCornerEmbedding 0 y)=y := congrArg (fun T : H →L[ℂ] H => T y) hi
  simp only [ContinuousLinearMap.comp_apply, hv] at he
  change (twoStateQuadraticBridge M Ω ξ d).adjoint (twoStateCornerEmbedding 1 x) =
    twoStateCornerEmbedding 0 ((twoStatePositiveTransport M Ω ξ hc d).symm x) at he
  exact he.symm

include hc in
theorem twoStateQuadratic_projection_reference (i : Fin 2) :
    modularQuadratic d.conjugation (twoStateEntry M i i 1) (twoStateMatrixVector Ω ξ) =
      twoStateCornerEmbedding i (twoStateVectorAt Ω ξ i) := by
  have he : modularQuadratic d.conjugation (twoStateEntry M i i 1) =
      (twoStateCornerEmbedding i).toContinuousLinearMap.comp
        (twoStateCornerEmbedding i).toContinuousLinearMap.adjoint := by
    rw [twoStateCorner_rangeProjection]
    change (twoStateEntry M i i 1).val *
      conjugationOperator d.conjugation (twoStateEntry M i i 1).val = _
    rw [twoStateEntry_projection_conjugation M Ω ξ hc d]
  rw [he, ContinuousLinearMap.comp_apply, twoStateCornerEmbedding_adjoint]
  fin_cases i <;> rfl

theorem twoStatePositiveTransport_inverse_reference :
    twoStateCornerEmbedding 0 ((twoStatePositiveTransport M Ω ξ hc d).symm ξ) =
      modularQuadratic d.conjugation (twoStateEntry M 0 1 1) (twoStateMatrixVector Ω ξ) := by
  rw [twoStatePositiveTransport_inverse_embedding]
  have he := twoStateQuadratic_projection_reference M Ω ξ hc d 1
  change modularQuadratic d.conjugation (twoStateEntry M 1 1 1)
    (twoStateMatrixVector Ω ξ)=twoStateCornerEmbedding 1 ξ at he
  rw [← he]
  change (star (twoStateQuadraticBridge M Ω ξ d) *
    modularQuadratic d.conjugation (twoStateEntry M 1 1 1)) (twoStateMatrixVector Ω ξ) = _
  dsimp only [twoStateQuadraticBridge]
  rw [modularQuadratic_star d.conjugation d.involutive (d.right_mem le_rfl),
    modularQuadratic_mul d.conjugation d.involutive (d.right_mem le_rfl),
    twoStateEntry_star, star_one, twoStateEntry_mul, one_mul]


def twoStateDiagonalEntry (a : Algebra M) : Algebra (twoStateMatrixAlgebra M) :=
  twoStateEntry M 0 0 a+twoStateEntry M 1 1 a

omit hc d Ω ξ in
private theorem diagonal_fst (a : Algebra M) (x : TwoStateMatrixHilbert H H) (r : Fin 2) :
    ((twoStateDiagonalEntry M a).val x).fst r=a.val (x.fst r) := by
  change ((twoStateEntry M 0 0 a).val x).fst r+((twoStateEntry M 1 1 a).val x).fst r=_
  rw [twoStateEntry_fst,twoStateEntry_fst]
  fin_cases r <;> simp

omit hc d Ω ξ in
private theorem diagonal_snd (a : Algebra M) (x : TwoStateMatrixHilbert H H) (r : Fin 2) :
    ((twoStateDiagonalEntry M a).val x).snd r=a.val (x.snd r) := by
  change ((twoStateEntry M 0 0 a).val x).snd r+((twoStateEntry M 1 1 a).val x).snd r=_
  rw [twoStateEntry_snd,twoStateEntry_snd]
  fin_cases r <;> simp

omit hc d Ω ξ in
theorem twoStateDiagonalEntry_corner (a : Algebra M) (i : Fin 2) (x : H) :
    (twoStateDiagonalEntry M a).val (twoStateCornerEmbedding i x) =
      twoStateCornerEmbedding i (a.val x) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> apply PiLp.ext <;> intro r
  · change ((twoStateDiagonalEntry M a).val (twoStateCornerEmbedding i x)).fst r =
      (twoStateCornerEmbedding i (a.val x)).fst r
    rw [diagonal_fst]
    fin_cases i <;> fin_cases r <;> simp [twoStateCornerEmbedding,tupleSingle_apply]
  · change ((twoStateDiagonalEntry M a).val (twoStateCornerEmbedding i x)).snd r =
      (twoStateCornerEmbedding i (a.val x)).snd r
    rw [diagonal_snd]
    fin_cases i <;> fin_cases r <;> simp [twoStateCornerEmbedding,tupleSingle_apply]

omit hc d Ω ξ in
private theorem diagonal_commutes_entry (a : Algebra M) :
    (twoStateDiagonalEntry M a).val*(twoStateEntry M 1 0 1).val =
      (twoStateEntry M 1 0 1).val*(twoStateDiagonalEntry M a).val := by
  ext x
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> apply PiLp.ext <;> intro r
  · change ((twoStateDiagonalEntry M a).val ((twoStateEntry M 1 0 1).val x)).fst r =
      ((twoStateEntry M 1 0 1).val ((twoStateDiagonalEntry M a).val x)).fst r
    rw [diagonal_fst,twoStateEntry_fst,twoStateEntry_fst,diagonal_fst]
    fin_cases r <;> simp
  · change ((twoStateDiagonalEntry M a).val ((twoStateEntry M 1 0 1).val x)).snd r =
      ((twoStateEntry M 1 0 1).val ((twoStateDiagonalEntry M a).val x)).snd r
    rw [diagonal_snd,twoStateEntry_snd,twoStateEntry_snd,diagonal_snd]
    fin_cases r <;> simp

omit hc in
theorem twoStateQuadraticBridge_commutes (a : Algebra M) :
    twoStateQuadraticBridge M Ω ξ d*(twoStateDiagonalEntry M a).val =
      (twoStateDiagonalEntry M a).val*twoStateQuadraticBridge M Ω ξ d := by
  have he := VonNeumannAlgebra.mem_commutant_iff.mp
    (d.right_mem le_rfl (twoStateEntry M 1 0 1))
    (twoStateDiagonalEntry M a).val (twoStateDiagonalEntry M a).property
  dsimp only [twoStateQuadraticBridge,modularQuadratic]
  rw [mul_assoc,← he,← mul_assoc,← diagonal_commutes_entry,mul_assoc]

theorem twoStatePositiveTransport_intertwines (a : Algebra M) (x : H) :
    twoStatePositiveTransport M Ω ξ hc d (a.val x)=
      a.val (twoStatePositiveTransport M Ω ξ hc d x) := by
  apply (twoStateCornerEmbedding 1).injective
  rw [twoStatePositiveTransport_embedding,← twoStateDiagonalEntry_corner,
    ← twoStateDiagonalEntry_corner]
  have he := congrArg (fun T : TwoStateMatrixHilbert H H →L[ℂ] TwoStateMatrixHilbert H H =>
    T (twoStateCornerEmbedding 0 x)) (twoStateQuadraticBridge_commutes M Ω ξ d a)
  change twoStateQuadraticBridge M Ω ξ d
      ((twoStateDiagonalEntry M a).val (twoStateCornerEmbedding 0 x)) =
    (twoStateDiagonalEntry M a).val
      (twoStateCornerEmbedding 1 (twoStatePositiveTransport M Ω ξ hc d x))
  rw [twoStatePositiveTransport_embedding]
  exact he

end
end KadisonKastler

end OAI

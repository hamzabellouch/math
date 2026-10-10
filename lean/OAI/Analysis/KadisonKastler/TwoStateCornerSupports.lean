import OAI.Analysis.KadisonKastler.TwoStateMatrixState
import OAI.Analysis.KadisonKastler.TwoStateCornerCompression
import OAI.Analysis.KadisonKastler.NormalTwoStateSupports
import OAI.Analysis.KadisonKastler.PartialIsometryCorner
import OAI.Analysis.KadisonKastler.ModularPositiveCone

namespace OAI

/-! # The quadratic off-diagonal isometry between the two state corners -/

namespace KadisonKastler
open Generator
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

def twoStateEntry (i j : Fin 2) (a : Algebra M) : Algebra (twoStateMatrixAlgebra M) :=
  twoStateMatrixEquiv M (matrixSlot i j a)

theorem twoStateEntry_mul (i j k : Fin 2) (a b : Algebra M) :
    twoStateEntry M i j a * twoStateEntry M j k b = twoStateEntry M i k (a*b) := by
  simp only [twoStateEntry, ← map_mul, matrixSlot_mul]

theorem twoStateEntry_star (i j : Fin 2) (a : Algebra M) :
    star (twoStateEntry M i j a)=twoStateEntry M j i (star a) := by
  change star (twoStateMatrixEquiv M (matrixSlot i j a)) =
    twoStateMatrixEquiv M (matrixSlot j i (star a))
  exact ((twoStateMatrixEquiv M).toStarAlgHom.map_star'
    (matrixSlot i j a)).symm.trans (congrArg (twoStateMatrixEquiv M) (matrixSlot_star i j a))

theorem twoStateEntry_fst (i j r : Fin 2) (a : Algebra M)
    (x : TwoStateMatrixHilbert H H) :
    ((twoStateEntry M i j a).val x).fst r = if r=i then a.val (x.fst j) else 0 := by
  rw [twoStateEntry, twoStateMatrixEquiv_coe]
  change matrixOperatorHom M (matrixSlot i j a) x.fst r = _
  fin_cases i <;> fin_cases j <;> fin_cases r <;>
    simp [matrixOperatorHom_apply, hilbertMatrix_apply, matrixSlot,
      Fin.sum_univ_two, CStarMatrix.map_apply]

theorem twoStateEntry_snd (i j r : Fin 2) (a : Algebra M)
    (x : TwoStateMatrixHilbert H H) :
    ((twoStateEntry M i j a).val x).snd r = if r=i then a.val (x.snd j) else 0 := by
  rw [twoStateEntry, twoStateMatrixEquiv_coe]
  change matrixOperatorHom M
    (coefficientMatrixMap (StarAlgEquiv.refl ℂ (Algebra M)).toStarAlgHom
      (matrixSlot i j a)) x.snd r = _
  fin_cases i <;> fin_cases j <;> fin_cases r <;>
    simp [matrixOperatorHom_apply, hilbertMatrix_apply, matrixSlot,
      Fin.sum_univ_two, CStarMatrix.map_apply, coefficientMatrixMap_apply]

theorem twoStateCorner_rangeProjection (i : Fin 2) :
    (twoStateCornerEmbedding (H := H) i).toContinuousLinearMap.comp
      (twoStateCornerEmbedding (H := H) i).toContinuousLinearMap.adjoint =
      (twoStateEntry M i i 1).val * twoStateSummandProjection (H := H) (K := H) i := by
  ext x
  change twoStateCornerEmbedding i
    ((twoStateCornerEmbedding (H := H) i).toContinuousLinearMap.adjoint x) = _
  rw [twoStateCornerEmbedding_adjoint]
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> apply PiLp.ext <;> intro r
  · change (twoStateCornerEmbedding i (if i=0 then x.fst 0 else x.snd 1)).fst r =
      ((twoStateEntry M i i 1).val (twoStateSummandProjection i x)).fst r
    rw [twoStateEntry_fst]
    fin_cases i <;> fin_cases r <;>
      simp [twoStateCornerEmbedding, twoStateSummandProjection, tupleSingle_apply]
  · change (twoStateCornerEmbedding i (if i=0 then x.fst 0 else x.snd 1)).snd r =
      ((twoStateEntry M i i 1).val (twoStateSummandProjection i x)).snd r
    rw [twoStateEntry_snd]
    fin_cases i <;> fin_cases r <;>
      simp [twoStateCornerEmbedding, twoStateSummandProjection, tupleSingle_apply]

variable (Ω ξ : H)
  (hc : DenseRange (algebraVectorMap (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ)))
  (d : ModularConjugationData (twoStateMatrixAlgebra M) (twoStateMatrixVector Ω ξ))

theorem twoStateSummand_mem_commutant (i : Fin 2) :
    twoStateSummandProjection (H := H) (K := H) i ∈ (twoStateMatrixAlgebra M).commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  obtain ⟨b,hb⟩ := (twoStateMatrixEquiv M).surjective ⟨a,ha⟩
  have he : (twoStateMatrixEquiv M b).val=a := congrArg Subtype.val hb
  rw [← he, twoStateMatrixEquiv_coe]
  ext x
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> fin_cases i <;>
    simp [twoStateSummandProjection, twoStateMatrixRepresentation,
      hilbertPairRepresentation, mul_apply_eq_comp, hilbertPairOperator]

theorem twoStateSummand_reference (i : Fin 2) :
    twoStateSummandProjection i (twoStateMatrixVector Ω ξ)=
      (twoStateEntry M i i 1).val (twoStateMatrixVector Ω ξ) := by
  rw [twoStateEntry, twoStateMatrixEquiv_coe]
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> apply PiLp.ext <;> intro r
  · change ((if i=0 then (1 : FiniteHilbert (Fin 2) H →L[ℂ] FiniteHilbert (Fin 2) H)
      else 0) (tupleSingle 0 Ω)) r =
      (twoStateMatrixRepresentation (StarAlgEquiv.refl ℂ (Algebra M))
        (matrixSlot i i 1) (twoStateMatrixVector Ω ξ)).fst r
    rw [twoStateMatrixRepresentation_vector_fst]
    fin_cases i <;> fin_cases r <;> simp [matrixSlot, tupleSingle_apply]
  · change ((if i=0 then (0 : FiniteHilbert (Fin 2) H →L[ℂ] FiniteHilbert (Fin 2) H)
      else 1) (tupleSingle 1 ξ)) r =
      (twoStateMatrixRepresentation (StarAlgEquiv.refl ℂ (Algebra M))
        (matrixSlot i i 1) (twoStateMatrixVector Ω ξ)).snd r
    rw [twoStateMatrixRepresentation_vector_snd]
    fin_cases i <;> fin_cases r <;> simp [matrixSlot, tupleSingle_apply]

include hc in
theorem twoStateEntry_projection_conjugation (i : Fin 2) :
    conjugationOperator d.conjugation (twoStateEntry M i i 1).val =
      twoStateSummandProjection i := by
  apply commutant_operator_eq_of_vector (twoStateMatrixAlgebra M)
    (twoStateMatrixVector Ω ξ) hc (d.right_mem le_rfl _)
    (twoStateSummand_mem_commutant M i)
  rw [twoStateSummand_reference M Ω ξ]
  have hv := d.centralizer_vector (twoStateEntry M i i 1)
    (fun a => twoStateMatrixProjection_centralizes M Ω ξ i a.val a.property)
  have hs : star (twoStateEntry M i i 1).val=(twoStateEntry M i i 1).val := by
    rw [← StarMemClass.coe_star, twoStateEntry_star, star_one]
  rwa [hs] at hv

include hc in
theorem twoStateEntry_quadratic_initial :
    (modularQuadratic d.conjugation (twoStateEntry M 1 0 1)).adjoint.comp
      (modularQuadratic d.conjugation (twoStateEntry M 1 0 1)) =
      (twoStateCornerEmbedding 0).toContinuousLinearMap.comp
        (twoStateCornerEmbedding 0).toContinuousLinearMap.adjoint := by
  change star (modularQuadratic d.conjugation (twoStateEntry M 1 0 1)) *
    modularQuadratic d.conjugation (twoStateEntry M 1 0 1) = _
  rw [modularQuadratic_star d.conjugation d.involutive (d.right_mem le_rfl),
    modularQuadratic_mul d.conjugation d.involutive (d.right_mem le_rfl),
    twoStateEntry_star, star_one, twoStateEntry_mul, one_mul,
    twoStateCorner_rangeProjection]
  change (twoStateEntry M 0 0 1).val *
    conjugationOperator d.conjugation (twoStateEntry M 0 0 1).val = _
  rw [twoStateEntry_projection_conjugation M Ω ξ hc d]

include hc in
theorem twoStateEntry_quadratic_final :
    (modularQuadratic d.conjugation (twoStateEntry M 1 0 1)).comp
      (modularQuadratic d.conjugation (twoStateEntry M 1 0 1)).adjoint =
      (twoStateCornerEmbedding 1).toContinuousLinearMap.comp
        (twoStateCornerEmbedding 1).toContinuousLinearMap.adjoint := by
  change modularQuadratic d.conjugation (twoStateEntry M 1 0 1) *
    star (modularQuadratic d.conjugation (twoStateEntry M 1 0 1)) = _
  rw [modularQuadratic_star d.conjugation d.involutive (d.right_mem le_rfl),
    modularQuadratic_mul d.conjugation d.involutive (d.right_mem le_rfl),
    twoStateEntry_star, star_one, twoStateEntry_mul, one_mul,
    twoStateCorner_rangeProjection]
  change (twoStateEntry M 1 1 1).val *
    conjugationOperator d.conjugation (twoStateEntry M 1 1 1).val = _
  rw [twoStateEntry_projection_conjugation M Ω ξ hc d]

end
end KadisonKastler

end OAI

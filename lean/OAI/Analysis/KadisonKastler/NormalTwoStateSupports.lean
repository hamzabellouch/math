import OAI.Analysis.KadisonKastler.NormalTwoStateState
import OAI.Analysis.KadisonKastler.ModularConjugationData
import OAI.Analysis.KadisonKastler.RightBoundedVector

namespace OAI

/-! # The right supports of the two summands in the two-state representation -/

namespace KadisonKastler

open Generator

noncomputable section

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}
  (θ : Algebra M ≃⋆ₐ[ℂ] Algebra N)
  (hθ : BoundedWeakNormal M (N.toStarSubalgebra.subtype.comp θ.toStarAlgHom))

/-- The projection onto one of the two original representation summands. -/
def twoStateSummandProjection (i : Fin 2) :
    TwoStateMatrixHilbert H K →L[ℂ] TwoStateMatrixHilbert H K :=
  hilbertPairOperator (if i = 0 then 1 else 0) (if i = 0 then 0 else 1)

include hθ in
theorem twoStateSummandProjection_mem_commutant (i : Fin 2) :
    twoStateSummandProjection (H := H) (K := K) i ∈ (normalTwoStateAlgebra θ).commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro a ha
  obtain ⟨b, hb⟩ := (normalTwoStateEquiv θ hθ).surjective ⟨a, ha⟩
  have he : (normalTwoStateEquiv θ hθ b).val = a := congrArg Subtype.val hb
  rw [← he, normalTwoStateEquiv_coe]
  ext x
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> fin_cases i <;>
    simp [twoStateSummandProjection, twoStateMatrixRepresentation,
      hilbertPairRepresentation, mul_apply_eq_comp, hilbertPairOperator]

theorem twoStateSummandProjection_vector (Ω : H) (ξ : K) (i : Fin 2) :
    twoStateSummandProjection i (twoStateMatrixVector Ω ξ) =
      (normalTwoStateProjection θ hθ i).val (twoStateMatrixVector Ω ξ) := by
  change twoStateSummandProjection i (twoStateMatrixVector Ω ξ) =
    (normalTwoStateEquiv θ hθ (matrixSlot i i 1)).val (twoStateMatrixVector Ω ξ)
  rw [normalTwoStateEquiv_coe]
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext <;> apply PiLp.ext <;> intro j
  · change ((if i = 0 then (1 : FiniteHilbert (Fin 2) H →L[ℂ] FiniteHilbert (Fin 2) H) else 0)
      (tupleSingle 0 Ω)) j =
      (twoStateMatrixRepresentation θ (matrixSlot i i 1) (twoStateMatrixVector Ω ξ)).fst j
    rw [twoStateMatrixRepresentation_vector_fst]
    fin_cases i <;> fin_cases j <;> simp [matrixSlot, tupleSingle_apply]
  · change ((if i = 0 then (0 : FiniteHilbert (Fin 2) K →L[ℂ] FiniteHilbert (Fin 2) K) else 1)
      (tupleSingle 1 ξ)) j =
      (twoStateMatrixRepresentation θ (matrixSlot i i 1) (twoStateMatrixVector Ω ξ)).snd j
    rw [twoStateMatrixRepresentation_vector_snd]
    fin_cases i <;> fin_cases j <;> simp [matrixSlot, tupleSingle_apply]

theorem normalTwoStateProjection_star (i : Fin 2) :
    star (normalTwoStateProjection θ hθ i).val = (normalTwoStateProjection θ hθ i).val := by
  have hs : star (matrixSlot i i (1 : Algebra M)) = matrixSlot i i 1 := by
    rw [matrixSlot_star, star_one]
  have h := (normalTwoStateEquiv θ hθ).toStarAlgHom.map_star' (matrixSlot i i (1 : Algebra M))
  exact (congrArg Subtype.val h).symm.trans (congrArg
    (fun a => (normalTwoStateEquiv θ hθ a).val) hs)

theorem normalTwoStateProjection_conjugation (Ω : H) (ξ : K)
    (hcyc : DenseRange (algebraVectorMap (normalTwoStateAlgebra θ) (twoStateMatrixVector Ω ξ)))
    (d : ModularConjugationData (normalTwoStateAlgebra θ) (twoStateMatrixVector Ω ξ))
    (i : Fin 2) :
    conjugationOperator d.conjugation (normalTwoStateProjection θ hθ i).val =
      twoStateSummandProjection i := by
  apply commutant_operator_eq_of_vector (normalTwoStateAlgebra θ)
    (twoStateMatrixVector Ω ξ) hcyc (d.right_mem le_rfl _)
    (twoStateSummandProjection_mem_commutant θ hθ i)
  rw [twoStateSummandProjection_vector θ hθ]
  have hc := normalTwoStateProjection_centralizes θ hθ Ω ξ i
  have hv := d.centralizer_vector (normalTwoStateProjection θ hθ i)
    (fun a => hc a.val a.property)
  rwa [normalTwoStateProjection_star] at hv

end

end KadisonKastler

end OAI

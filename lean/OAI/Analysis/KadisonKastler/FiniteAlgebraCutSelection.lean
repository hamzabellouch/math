import OAI.Analysis.KadisonKastler.FiniteCutSelection
import OAI.Analysis.KadisonKastler.ConjugateFiniteThreshold

namespace OAI

/-! # A genuine algebra projection from the finite spectral cut estimates -/

namespace KadisonKastler

open Generator Generator.Tracial Finset
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] {M : VonNeumannAlgebra H}

theorem exists_finite_algebra_projection_cut
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (P : ι → AlgebraProjection M)
    (ho : ∀ i j, i ≠ j → (P i).val * (P j).val = 0)
    (ht : ∑ i, (P i).val = 1) (c : ι → ℝ)
    (hcr : ∀ i, c i ∈ Set.Icc (-1 : ℝ) 1)
    (ξ η : H) (hη : ‖η‖ = 1) (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b)
    (hsmall : ‖((∑ i, (c i : ℂ) • (P i).val.val) -
        conjugationOperator J (∑ i, (c i : ℂ) • (P i).val.val)) ξ‖ * ‖ξ‖ <
      δ * (‖((∑ i, (c i : ℂ) • (P i).val.val) -
        conjugationOperator J (∑ i, (c i : ℂ) • (P i).val.val)) η‖ ^ 2 / 2 - 2 * b)) :
    ∃ p : AlgebraProjection M,
      ‖(p.val.val - conjugationOperator J p.val.val) ξ‖ ^ 2 ≤ δ ∧
      b ≤ ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by
  let A : ι → H →L[ℂ] H := fun i => (P i).val.val
  let B : ι → H →L[ℂ] H := fun i => conjugationOperator J (A i)
  have hA (i : ι) : IsStarProjection (A i) :=
    (P i).property.map M.toStarSubalgebra.subtype
  have hB (i : ι) : IsStarProjection (B i) :=
    (conjugateAlgebraProjection M M.commutant J hJ hright (P i)).property.map
      M.commutant.toStarSubalgebra.subtype
  have hAo (i j : ι) (hij : i ≠ j) : A i * A j = 0 := congrArg Subtype.val (ho i j hij)
  have hBo (i j : ι) (hij : i ≠ j) : B i * B j = 0 := by
    change conjugationOperator J (A i) * conjugationOperator J (A j) = 0
    rw [← conjugationOperator_mul J hJ,hAo i j hij]
    ext ζ
    simp only [conjugationOperator_apply,zero_apply,map_zero]
  have hAt : (∑ i, A i) = 1 := by
    have he := congrArg M.toStarSubalgebra.subtype ht
    simp only [map_sum,map_one] at he
    change (∑ i, A i) = 1 at he
    exact he
  have hBt : (∑ i, B i) = 1 := by
    have he := congrArg (conjugationOperator J) hAt
    rw [conjugationOperator_finsetSum,conjugationOperator_one J hJ] at he
    exact he
  have hcomm (i j : ι) : Commute (A i) (B j) :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright (P j).val) (A i) (P i).val.property
  have hsmall' : ‖((∑ i, (c i : ℂ) • A i) - (∑ i, (c i : ℂ) • B i)) ξ‖ * ‖ξ‖ <
      δ * (‖((∑ i, (c i : ℂ) • A i) - (∑ i, (c i : ℂ) • B i)) η‖ ^ 2 / 2 - 2 * b) := by
    simpa only [conjugationOperator_real_sum] using hsmall
  obtain ⟨t,_,hξ,hη'⟩ := exists_finite_spectral_cut A B hA hB hAo hBo hAt hBt hcomm
    c c hcr hcr ξ η hη δ b hδ hb hsmall'
  let T := finiteThresholdProjection A c t
  have hTM : T ∈ M := by
    apply M.toStarSubalgebra.sum_mem
    intro i _
    exact M.toStarSubalgebra.smul_mem (P i).val.property _
  have hT : IsStarProjection T := finiteThresholdProjection_isProjection A hA hAo c t
  let p : AlgebraProjection M := ⟨⟨T,hTM⟩,
    ⟨Subtype.ext hT.isIdempotentElem.eq,Subtype.ext hT.isSelfAdjoint.star_eq⟩⟩
  refine ⟨p,?_,?_⟩
  · change ‖(T - conjugationOperator J T) ξ‖ ^ 2 ≤ δ
    simpa only [T,conjugationOperator_finiteThreshold] using hξ
  · change b ≤ ‖(T - conjugationOperator J T) η‖ ^ 2
    simpa only [T,conjugationOperator_finiteThreshold] using hη'

end

end KadisonKastler

end OAI

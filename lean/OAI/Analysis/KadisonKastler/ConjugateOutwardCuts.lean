import OAI.Analysis.KadisonKastler.OutwardCutEnergy
import OAI.Analysis.KadisonKastler.ConjugateFiniteThreshold
import OAI.Analysis.KadisonKastler.TwoVectorCutSelection

namespace OAI

/-! # Two-vector projection cuts in the original algebra -/

namespace KadisonKastler

open MeasureTheory Finset Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] {M : VonNeumannAlgebra H}

def finiteAlgebraOutwardProjection (P : ι → AlgebraProjection M)
    (ho : ∀ i j, i ≠ j → (P i).val*(P j).val=0)
    (c : ι → ℝ) (t : ℝ) : AlgebraProjection M := by
  let A : ι → H →L[ℂ] H := fun i => (P i).val.val
  have hT : finiteThresholdProjection A (signedSquare ∘ c) t ∈ M := by
    apply M.toStarSubalgebra.sum_mem
    intro i _
    exact M.toStarSubalgebra.smul_mem (P i).val.property _
  have hm : finiteOutwardProjection A c t ∈ M := by
    unfold finiteOutwardProjection
    split
    · exact M.sub_mem M.one_mem hT
    · exact hT
  have hp := finiteOutwardProjection_isProjection A
    (fun i => (P i).property.map M.toStarSubalgebra.subtype)
    (fun i j hij => congrArg Subtype.val (ho i j hij)) c t
  exact ⟨⟨finiteOutwardProjection A c t,hm⟩,
    ⟨Subtype.ext hp.isIdempotentElem.eq,Subtype.ext hp.isSelfAdjoint.star_eq⟩⟩

omit [CompleteSpace H] in
theorem conjugationOperator_finiteOutward (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (P : ι → H →L[ℂ] H) (c : ι → ℝ) (t : ℝ) :
    conjugationOperator J (finiteOutwardProjection P c t)=
      finiteOutwardProjection (fun i => conjugationOperator J (P i)) c t := by
  unfold finiteOutwardProjection
  split
  · rw [conjugationOperator_sub,conjugationOperator_one J hJ,conjugationOperator_finiteThreshold]
  · exact conjugationOperator_finiteThreshold J P _ t

theorem centralVectorDefect_projection (J : H ≃ₗᵢ⋆[ℂ] H)
    (ξ : H) (p : AlgebraProjection M) :
    centralVectorDefect J ξ p.val.val=(p.val.val-conjugationOperator J p.val.val) ξ := by
  rw [centralVectorDefect_apply,
    show star p.val.val=p.val.val from congrArg Subtype.val p.property.isSelfAdjoint.star_eq]
  rfl

theorem exists_finite_two_vector_projection
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (P : ι → AlgebraProjection M)
    (ho : ∀ i j, i ≠ j → (P i).val*(P j).val=0)
    (ht : ∑ i, (P i).val=1) (c : ι → ℝ)
    (ξ η : H) (hξ : J ξ=ξ) {α K : ℝ} (hα : 0 < α) (hK : 0 < K)
    (hsmall : α*(‖(∑ i, (c i : ℂ) • (P i).val.val) ξ‖^2+
      ‖(∑ i, (c i : ℂ) • (P i).val.val) η‖^2)+
      2*K*‖(∑ i, (c i : ℂ) • (P i).val.val) ξ‖*
        ‖((∑ i, (c i : ℂ) • (P i).val.val)-
          conjugationOperator J (∑ i, (c i : ℂ) • (P i).val.val)) ξ‖ <
      α*K/2*‖((∑ i, (c i : ℂ) • (P i).val.val)-
        conjugationOperator J (∑ i, (c i : ℂ) • (P i).val.val)) η‖^2) :
    ∃ p : AlgebraProjection M,
      ‖p.val.val ξ‖^2+‖p.val.val η‖^2 < K*‖centralVectorDefect J η p.val.val‖^2 ∧
      ‖centralVectorDefect J ξ p.val.val‖^2 < α*‖centralVectorDefect J η p.val.val‖^2 := by
  let A : ι → H →L[ℂ] H := fun i => (P i).val.val
  let B : ι → H →L[ℂ] H := fun i => conjugationOperator J (A i)
  let S : H →L[ℂ] H := ∑ i, (c i : ℂ) • A i
  let p := finiteAlgebraOutwardProjection P ho c
  have hA (i : ι) : IsStarProjection (A i) :=
    (P i).property.map M.toStarSubalgebra.subtype
  have hB (i : ι) : IsStarProjection (B i) :=
    (conjugateAlgebraProjection M M.commutant J hJ hright (P i)).property.map
      M.commutant.toStarSubalgebra.subtype
  have hAo (i j : ι) (hij : i ≠ j) : A i*A j=0 := congrArg Subtype.val (ho i j hij)
  have hBo (i j : ι) (hij : i ≠ j) : B i*B j=0 := by
    change conjugationOperator J (A i)*conjugationOperator J (A j)=0
    rw [← conjugationOperator_mul J hJ,hAo i j hij]
    ext ζ
    simp only [conjugationOperator_apply,zero_apply,map_zero]
  have hAt : ∑ i, A i=1 := by
    have he := congrArg M.toStarSubalgebra.subtype ht
    simp only [map_sum,map_one] at he
    change (∑ i, A i)=1 at he
    exact he
  have hBt : ∑ i, B i=1 := by
    have he := congrArg (conjugationOperator J) hAt
    rw [conjugationOperator_finsetSum,conjugationOperator_one J hJ] at he
    exact he
  have hc (i j : ι) : Commute (A i) (B j) :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright (P j).val) (A i) (P i).val.property
  have hsum : (∑ i, (c i : ℂ) • B i)=conjugationOperator J S :=
    (conjugationOperator_real_sum J A c).symm
  have hgap (ζ : H) (t : ℝ) :
      ‖centralVectorDefect J ζ (p t).val.val‖^2=
        ‖(finiteOutwardProjection A c t-finiteOutwardProjection B c t) ζ‖^2 := by
    rw [centralVectorDefect_projection]
    change ‖(finiteOutwardProjection A c t-
      conjugationOperator J (finiteOutwardProjection A c t)) ζ‖^2=_
    rw [conjugationOperator_finiteOutward J hJ]
  have hi (ζ : H) : Integrable (fun t => ‖centralVectorDefect J ζ (p t).val.val‖^2) := by
    simp_rw [hgap]
    exact finiteOutwardProjection_gap_integrable A B hA hB hAo hBo hAt hBt hc c c ζ
  have hm (ζ : H) : Integrable (fun t => ‖(p t).val.val ζ‖^2) :=
    finiteOutwardProjection_mass_integrable A hA hAo hAt c ζ
  have hmval (ζ : H) : (∫ t, ‖(p t).val.val ζ‖^2)=‖S ζ‖^2 :=
    finiteOutwardProjection_integral_mass A hA hAo hAt c ζ
  have hlo : ‖(S-conjugationOperator J S) η‖^2 ≤
      2*(∫ t, ‖centralVectorDefect J η (p t).val.val‖^2) := by
    simp_rw [hgap]
    have he := finiteOutwardProjection_integral_lower A B hA hB hAo hBo hAt hBt hc c c η
    rwa [hsum] at he
  have hup : (∫ t, ‖centralVectorDefect J ξ (p t).val.val‖^2) ≤
      2*‖S ξ‖*‖(S-conjugationOperator J S) ξ‖ := by
    have he := finiteOutwardProjection_integral_upper_sq A B hA hB hAo hBo hAt hBt hc c c ξ
    rw [hsum] at he
    have hnorm : ‖conjugationOperator J S ξ‖=‖S ξ‖ := by
      simp only [conjugationOperator_apply,hξ,J.norm_map]
    rw [hnorm] at he
    apply (sq_le_sq₀ (integral_nonneg (fun _ => sq_nonneg _)) (by positivity)).mp
    simp_rw [hgap]
    calc
      _ ≤ _ := he
      _ = (2*‖S ξ‖*‖(S-conjugationOperator J S) ξ‖)^2 := by ring
  apply exists_projection_two_relative_bounds J ξ η p ((hm ξ).add (hm η)) (hi ξ) (hi η) hα hK
  rw [integral_add (hm ξ) (hm η),hmval ξ,hmval η]
  change α*(‖S ξ‖^2+‖S η‖^2)+2*K*‖S ξ‖*‖(S-conjugationOperator J S) ξ‖ <
    α*K/2*‖(S-conjugationOperator J S) η‖^2 at hsmall
  calc
    _ ≤ α*(‖S ξ‖^2+‖S η‖^2)+K*(2*‖S ξ‖*‖(S-conjugationOperator J S) ξ‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hup hK.le)
    _ < α*K/2*‖(S-conjugationOperator J S) η‖^2 := by nlinarith [hsmall]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hlo (mul_nonneg hα.le hK.le)]

end

end KadisonKastler

end OAI

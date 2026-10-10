import OAI.Analysis.KadisonKastler.FiniteThresholdEstimate
import OAI.Analysis.KadisonKastler.ConjugateVectorSupport

namespace OAI

/-! # Finite spectral cuts and the conjugate right action -/

namespace KadisonKastler

open Generator Generator.Tracial Finset
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

omit [CompleteSpace H] [Fintype ι] in
theorem conjugationOperator_finsetSum (J : H ≃ₗᵢ⋆[ℂ] H)
    (s : Finset ι) (P : ι → H →L[ℂ] H) :
    conjugationOperator J (∑ i ∈ s, P i) = ∑ i ∈ s, conjugationOperator J (P i) := by
  ext ξ
  simp only [conjugationOperator_apply,_root_.sum_apply,map_sum]

omit [CompleteSpace H] in
theorem conjugationOperator_real_sum (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → H →L[ℂ] H) (c : ι → ℝ) :
    conjugationOperator J (∑ i, (c i : ℂ) • P i) =
      ∑ i, (c i : ℂ) • conjugationOperator J (P i) := by
  rw [conjugationOperator_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [conjugationOperator_smul]
  simp only [Complex.star_def,Complex.conj_ofReal]

omit [CompleteSpace H] in
theorem conjugationOperator_finiteThreshold (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → H →L[ℂ] H) (c : ι → ℝ) (t : ℝ) :
    conjugationOperator J (finiteThresholdProjection P c t) =
      finiteThresholdProjection (fun i => conjugationOperator J (P i)) c t :=
  conjugationOperator_real_sum J P _

theorem finiteSpectralCut_integral_le {M : VonNeumannAlgebra H}
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (P : ι → AlgebraProjection M)
    (ho : ∀ i j, i ≠ j → (P i).val * (P j).val = 0)
    (ht : ∑ i, (P i).val = 1) (c : ι → ℝ) (ξ : H) :
    (∫ t, ‖(finiteThresholdProjection (fun i => (P i).val.val) c t -
      conjugationOperator J (finiteThresholdProjection (fun i => (P i).val.val) c t)) ξ‖ ^ 2) ≤
    ‖((∑ i, (c i : ℂ) • (P i).val.val) -
      conjugationOperator J (∑ i, (c i : ℂ) • (P i).val.val)) ξ‖ * ‖ξ‖ := by
  let Q : ι → H →L[ℂ] H := fun i => conjugationOperator J (P i).val.val
  have hP (i : ι) : IsStarProjection (P i).val.val :=
    (P i).property.map M.toStarSubalgebra.subtype
  have hQ (i : ι) : IsStarProjection (Q i) :=
    (conjugateAlgebraProjection M M.commutant J hJ hright (P i)).property.map
      M.commutant.toStarSubalgebra.subtype
  have hPo (i j : ι) (hij : i ≠ j) : (P i).val.val * (P j).val.val = 0 :=
    congrArg Subtype.val (ho i j hij)
  have hQo (i j : ι) (hij : i ≠ j) : Q i * Q j = 0 := by
    change conjugationOperator J (P i).val.val * conjugationOperator J (P j).val.val = 0
    rw [← conjugationOperator_mul J hJ,hPo i j hij]
    ext η
    simp only [conjugationOperator_apply,zero_apply,map_zero]
  have hPt : (∑ i, (P i).val.val) = 1 := by
    have he := congrArg M.toStarSubalgebra.subtype ht
    simp only [map_sum,map_one] at he
    change (∑ i, (P i).val.val) = 1 at he
    exact he
  have hQt : (∑ i, Q i) = 1 := by
    have he := congrArg (conjugationOperator J) hPt
    rw [conjugationOperator_finsetSum,conjugationOperator_one J hJ] at he
    exact he
  have hcomm (i j : ι) : Commute (P i).val.val (Q j) :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright (P j).val) (P i).val.val (P i).val.property
  have he := finiteThresholdProjection_integral_le (fun i => (P i).val.val) Q
    hP hQ hPo hQo hPt hQt hcomm c c ξ
  simpa only [conjugationOperator_finiteThreshold,conjugationOperator_real_sum] using he

end

end KadisonKastler

end OAI

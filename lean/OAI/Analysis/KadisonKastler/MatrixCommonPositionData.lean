import OAI.Analysis.KadisonKastler.MatrixRightAlignment
import OAI.Analysis.KadisonKastler.MatrixCommonStandardPosition
import OAI.Analysis.KadisonKastler.ConjugatedRepresentationComparison
import OAI.Analysis.KadisonKastler.CommonPositionConstants
import OAI.Analysis.KadisonKastler.PublishedCommonPosition

namespace OAI

/-! # Common tracial position from the constructed matrix correction -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

universe u

variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M N R : VonNeumannAlgebra H} {L P C : VonNeumannAlgebra K}

theorem exists_commonPositionData_of_matrix_cyclic_neighbor
    (hRM : R ≤ M) (hRN : R ≤ N) (hCL : C ≤ L) (hCP : C ≤ P)
    (eM : Algebra M ≃⋆ₐ[ℂ] Algebra L) (eN : Algebra N ≃⋆ₐ[ℂ] Algebra P)
    (eR : Algebra R ≃⋆ₐ[ℂ] Algebra C)
    (heM : ∀ r, eM (coordinateInclusion hRM r) = coordinateInclusion hCL (eR r))
    (heN : ∀ r, eN (coordinateInclusion hRN r) = coordinateInclusion hCP (eR r))
    (p : StandardTracialPosition L) (hP : IsII1Factor P.toStarSubalgebra)
    (d : ℕ → ℕ) (E : ∀ n, MatrixUnitSystem (Fin (d n)) (K →L[ℂ] K))
    (hmono : Monotone (fun n => (E n).algebra))
    (hC : C = generatedVonNeumannAlgebra (⨆ n, (E n).algebra))
    (hirr : ∀ T ∈ L, (∀ r ∈ C, r * T = T * r) →
      ∃ z : ℂ, T = z • (1 : K →L[ℂ] K))
    {γ : ℝ} (hγ : 0 < γ) (hsmall : γ < 174 / 1000000000000000)
    (hMN : NearInclusion M N γ) (hNM : NearInclusion N M γ)
    (hcomp : ∀ (a : Algebra M) (b : Algebra N), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖(eM a).val - (eN b).val‖ ≤ 400000000 * γ + ‖a.val - b.val‖)
    (hcommNear : NearInclusion L.commutant P.commutant (405000000 * γ))
    (hcommGap : kkDistance L.commutant P.commutant ≤ 810000000 * γ) :
    Nonempty (CommonTracialPositionData M N R hRM hRN γ K) := by
  let : Nontrivial K := nontrivial_of_ne p.vector 0 (by
    intro h
    have hn := p.vector_norm
    rw [h, norm_zero] at hn
    exact zero_ne_one hn)
  have hLP := nearInclusion_of_representation_comparison eM eN hγ hcomp hMN
  have hPL := reverse_nearInclusion_of_representation_comparison eM eN hγ hcomp hNM
  have hdist : kkDistance L P ≤ 2 * (400000000 * γ + 2 * γ) :=
    kkDistance_le_two_mul_of_nearInclusions (by positivity) hLP hPL
  obtain ⟨w, hwC, hCQ, hright, hwn⟩ := exists_matrix_right_alignment p hCL hCP d E
    hmono hC (by positivity : 0 ≤ 405000000 * γ) (by linarith) hcommNear
  let Q := unitaryConjugateAlgebra (star w) P
  have hw : ‖(w : K →L[ℂ] K) - 1‖ ≤ 34020000000 * γ := by linarith
  have hLQ : kkDistance L Q < 1 / 2 := by
    have h := preparedPair_second_correction_gap L P w
    change kkDistance L Q ≤ _ at h
    linarith
  have hLQ' : kkDistance L.commutant Q.commutant < 1 / 2 := by
    have h := preparedPair_second_correction_commutant_gap L P w
    change kkDistance L.commutant Q.commutant ≤ _ at h
    linarith
  have hQ : IsII1Factor Q.toStarSubalgebra := unitaryConjugateAlgebra_isII1 (star w) hP
  obtain ⟨q, hq, hbasic⟩ := exists_matrix_common_standardPosition p hCL hCQ hQ
    d E hmono hC hirr hright hLQ hLQ'
  let f := eN.trans (unitaryConjugateEquiv (star w) P)
  have hf : ∀ (a : Algebra M) (b : Algebra N), ‖a‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖(eM a).val - (f b).val‖ ≤ 68440000000 * γ + ‖a.val - b.val‖ := by
    intro a b ha hb
    have h := conjugated_representation_comparison eM eN hcomp w hw a b ha hb
    change ‖(eM a).val - (f b).val‖ ≤ _ at h
    linarith
  have hnL : NearInclusion L Q (69000000000 * γ) := by
    obtain ⟨δ, hδ, happ⟩ := nearInclusion_of_representation_comparison eM f hγ hf hMN
    exact ⟨δ, by linarith, happ⟩
  have hnQ : NearInclusion Q L (69000000000 * γ) := by
    obtain ⟨δ, hδ, happ⟩ := reverse_nearInclusion_of_representation_comparison eM f hγ hf hNM
    exact ⟨δ, by linarith, happ⟩
  refine ⟨{
    left := L
    right := Q
    common := C
    common_le_left := hCL
    common_le_right := hCQ
    leftEquiv := eM
    rightEquiv := f
    commonEquiv := eR
    left_restrict := heM
    right_restrict := ?_
    leftPosition := p
    rightPosition := q
    same_vector := hq.symm
    tolerance := 69000000000 * γ
    tolerance_nonneg := by positivity
    tolerance_lt := commonPosition_tolerance_lt hγ hsmall
    near_left := hnL
    near_right := hnQ
    comparison := ?_
    same_basicConstruction := hbasic }⟩
  · intro r
    apply Subtype.ext
    change unitaryConj (star w) (eN (coordinateInclusion hRN r)).val = (eR r).val
    rw [heN]
    exact unitaryConj_eq_self_of_mem_commutant (star_mem hwC) (eR r).property
  · intro a b ha hb
    have h := hf a b ha hb
    linarith

end

end KadisonKastler

end OAI

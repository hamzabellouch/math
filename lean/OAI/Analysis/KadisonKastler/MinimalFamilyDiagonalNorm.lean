import OAI.Analysis.KadisonKastler.CentralLocalizationMinimum
import OAI.Analysis.KadisonKastler.FactorOffDiagonal

namespace OAI

/-! Diagonal norm preservation on a minimal row family. Central support
localization handles arbitrary centers and represented multiplicities. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {c : ℝ}

theorem minimal_row_family_diagonal_norm
    (hc : 0 ≤ c) (C : Set (BoundedWeakAlgebraMap M c)) (hclosed : IsClosed C)
    (hinv : RowInvariant hc C)
    (hmin : ∀ D : Set (BoundedWeakAlgebraMap M c), D ⊆ C → D.Nonempty → IsClosed D →
      RowInvariant hc D → D = C)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (R : C → H →L[ℂ] K)
    (hR : Continuous (fun F => ContinuousLinearMapWOT.ofCLM (R F)))
    (hrow : ∀ (n : ℕ) (r : Fin n → Algebra M) (hr : ∑ i, r i * star (r i) = 1) (F : C),
      R ⟨boundedWeakRowAverage hc r hr F.val, hinv n r hr F.property⟩ =
        representationRowAverage π r (R F))
    (F : C) (e : AlgebraProjection M) :
    ‖(π e.val).comp ((R F).comp (e.val : H →L[ℂ] H))‖ =
      ‖(R F).comp (e.val : H →L[ℂ] H)‖ := by
  let : CompactSpace (BoundedWeakAlgebraMap M c) :=
    isCompact_univ_iff.mp (isCompact_boundedWeakAlgebraMap M hc)
  let : CompactSpace C := isCompact_iff_compactSpace.mp hclosed.isCompact
  obtain ⟨G, hG⟩ := exists_central_localized_norm_le π R hR
    (fun A n r hr => ⟨⟨boundedWeakRowAverage hc r hr A.val, hinv n r hr A.property⟩,
      hrow n r hr A⟩) e F
  have heq := minimal_row_family_localized_factor_norm hc C hclosed hinv hmin π R hR hrow
    ((centralSupport e).val : H →L[ℂ] H)
    (fun a => congrArg Subtype.val (centralSupport_commutes e a)) F G
  have hcore : ‖(R F).comp ((centralSupport e).val : H →L[ℂ] H)‖ ≤
      ‖(π e.val).comp ((R F).comp (e.val : H →L[ℂ] H))‖ := heq.trans_le hG
  have hep : ((centralSupport e).val : H →L[ℂ] H).comp (e.val : H →L[ℂ] H) =
      (e.val : H →L[ℂ] H) := congrArg Subtype.val (le_centralSupport e)
  have hsub : ‖(R F).comp (e.val : H →L[ℂ] H)‖ ≤
      ‖(R F).comp ((centralSupport e).val : H →L[ℂ] H)‖ := by
    calc
      _ = ‖((R F).comp ((centralSupport e).val : H →L[ℂ] H)).comp
          (e.val : H →L[ℂ] H)‖ := by rw [ContinuousLinearMap.comp_assoc, hep]
      _ ≤ _ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul_of_nonneg_left (e.property.map M.toStarSubalgebra.subtype).norm_le
          (norm_nonneg _)).trans_eq (mul_one _))
  apply le_antisymm
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right (e.property.map π).norm_le (norm_nonneg _)).trans_eq
        (one_mul _))
  · exact hsub.trans hcore

end

end KadisonKastler

end OAI

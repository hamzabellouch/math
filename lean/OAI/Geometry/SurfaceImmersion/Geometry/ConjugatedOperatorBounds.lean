import OAI.Geometry.SurfaceImmersion.Correction.ConjugatedPolynomialOperator

namespace OAI

/-! The fixed-loss conjugated estimate for the actual supported linear map. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma supportedField_eq_zero_of_seminorm_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {K : Compacts Base} (s : ℝ≥0) (m : ℕ)
    {f : SupportedField (F := F) K} (hf : supportedWeightedSeminorm K s m f = 0) : f = 0 := by
  apply DFunLike.ext
  intro p
  have h := (weightedBound_of_supportedSeminorm s m f).norm_le (Set.mem_univ p)
  rw [hf] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

namespace Expression

theorem conjugatedVariationLM_bound {U : Set Base} {O Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQcompact : IsCompact Q) (hQO : Q ⊆ O)
    (e : Expression) (he : e.SmoothCoeffs O) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (m : ℕ) (B P : ℝ) (hB : 1 ≤ B) (hP : 0 ≤ P) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0) (τ : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      WeightedBound U s (m + e.order) B (lowJet G) →
      (∀ v, WeightedBound U s (m + e.order) P
        (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ H : SupportedField (F := Fin 4 → ℂ) K,
        supportedWeightedSeminorm K s m
          (conjugatedVariationLM hO hU he hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ t H) ≤
        D / τ ^ (e.loss + 6) * supportedWeightedSeminorm K s (m + e.order) H := by
  obtain ⟨D, hD, hd⟩ := compact_conjugated_multilinear_bound hU hO hQcompact hQO e he m B P hB hP
  refine ⟨D, hD, ?_⟩
  intro G φ hG hφ hGQ s τ hτ hs hτs hs1 hGb hφb t ht H
  let C := supportedWeightedSeminorm K s (m + e.order) H
  have hC : 0 ≤ C := apply_nonneg _ _
  by_cases hC0 : C = 0
  · have hH0 : H = 0 := supportedField_eq_zero_of_seminorm_eq_zero s (m + e.order) hC0
    simp only [hH0, map_zero, mul_zero, le_refl]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hCs : ∀ j : Fin 3, 0 < (![C, 1, 1] j) := by
      intro j
      fin_cases j <;> simp [hCpos]
    have hHb : ∀ j, WeightedBound U s (m + e.order) (![C, 1, 1] j) (singleDirection H j) := by
      intro j
      fin_cases j
      · exact (weightedBound_of_supportedSeminorm s (m + e.order) H).restrict_open hU
      · exact (weightedBound_zero U s (m + e.order)).mono_const zero_le_one
      · exact (weightedBound_zero U s (m + e.order)).mono_const zero_le_one
    have hΦb : ∀ j v, WeightedBound U s (m + e.order) P
        (fun p => fderiv ℝ (singlePhase φ j) p (coordinateVector v)) := by
      intro j v
      fin_cases j
      · exact hφb v
      · change WeightedBound U s (m + e.order) P
          (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
        simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
          (weightedBound_zero U s (m + e.order) (F := ℝ)).mono_const hP
      · change WeightedBound U s (m + e.order) P
          (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
        simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
          (weightedBound_zero U s (m + e.order) (F := ℝ)).mono_const hP
    have hv := hd G (singlePhase φ) (singleDirection H) s τ ![C, 1, 1]
      hτ hs hτs hs1 hCs hG (singlePhase_smooth hφ) (singleDirection_smooth H.contDiff)
      hGQ hGb hHb hΦb t ht 0
    have hl : WeightedBound U s m (D * C / τ ^ (e.loss + 6))
        (conjugatedVariationLM hO hU he hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ t H) := by
      apply (show WeightedBound U s m (D * C / τ ^ (e.loss + 6))
        (fun p => conjugatedVariation e G (singlePhase φ) (singleDirection H) τ 0 (p, t)) by
          simpa using hv).congr
      intro p _
      exact conjugatedVariationLM_apply hO hU he hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ t H p
    have hg := hl.extend_support hU
      ((conjugatedVariationLM hO hU he hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ t H).tsupport_subset.trans hKU)
      (by positivity)
    have hn := supportedSeminorm_le_of_weightedBound hs (show 0 ≤ D * C / τ ^ (e.loss + 6) by positivity)
      (conjugatedVariationLM hO hU he hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ t H) hg
    convert hn using 1
    dsimp only [C]
    ring

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI

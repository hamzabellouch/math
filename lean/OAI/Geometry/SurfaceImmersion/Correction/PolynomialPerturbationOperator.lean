import OAI.Geometry.SurfaceImmersion.Geometry.ConjugatedOperatorBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPerturbationBounds
import OAI.Geometry.SurfaceImmersion.Geometry.SupportedTupleOperators

namespace OAI

/-! The conjugated derivative of the actual finite polynomial perturbation,
with its fixed scale loss and linear dependence on epsilon. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates ModulatedJets

variable {n : ℕ} {U : Set Base} {O : Set LowJet} {G : Base → Space}

def conjugatedLM (hO : IsOpen O) (hU : IsOpen U) (P : Fin n → Expression)
    (hP : ∀ l, (P l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε t : ℝ) :
    SupportedField (F := Fin 4 → ℂ) K →ₗ[ℝ] SupportedField (F := ℂ) K :=
  ∑ l, ε ^ (l.val + 1) •
    (P l).conjugatedVariationLM hO hU (hP l) hG hQ K hKU hφ τ t

lemma conjugatedLM_apply (hO : IsOpen O) (hU : IsOpen U) (P : Fin n → Expression)
    (hP : ∀ l, (P l).SmoothCoeffs O) (hG : ContDiff ℝ ∞ G)
    (hQ : Set.MapsTo (lowJet G) U O) (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ) (τ ε t : ℝ)
    (H : SupportedField (F := Fin 4 → ℂ) K) (p : Base) :
    conjugatedLM hO hU P hP hG hQ K hKU hφ τ ε t H p =
      conjugated P ε G (singlePhase φ) (singleDirection H) τ 0 (p, t) := by
  simp only [conjugatedLM, LinearMap.sum_apply, LinearMap.smul_apply]
  have hsum := congrArg (fun f : Base → ℂ => f p)
    (map_sum (FunLike.coeAddMonoidHom (SupportedField (F := ℂ) K) Base ℂ)
      (fun l : Fin n => ε ^ (l.val + 1) •
        (P l).conjugatedVariationLM hO hU (hP l) hG hQ K hKU hφ τ t H) Finset.univ)
  simp only [FunLike.coeAddMonoidHom_apply, Finset.sum_apply] at hsum
  rw [hsum]
  simp only [smul_apply, Expression.conjugatedVariationLM_apply, conjugated]

theorem conjugatedLM_bound {Q : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hQcompact : IsCompact Q) (hQO : Q ⊆ O)
    (P : Fin n → Expression) (hP : ∀ l, (P l).SmoothCoeffs O) (K : Compacts Base)
    (hKU : (K : Set Base) ⊆ U) (m : ℕ) (B R : ℝ) (hB : 1 ≤ B) (hR : 0 ≤ R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (G : Base → Space) (φ : Base → ℝ)
      (hG : ContDiff ℝ ∞ G) (hφ : ContDiff ℝ ∞ φ)
      (hGQ : Set.MapsTo (lowJet G) U Q) (s : ℝ≥0) (τ ε : ℝ),
      0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 → 0 ≤ ε → ε ≤ 1 →
      WeightedBound U s (m + order P) B (lowJet G) →
      (∀ v, WeightedBound U s (m + order P) R
        (fun p => fderiv ℝ φ p (coordinateVector v))) →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ H : SupportedField (F := Fin 4 → ℂ) K,
        supportedWeightedSeminorm K s m
          (conjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H) ≤
        D * ε / τ ^ loss P * supportedWeightedSeminorm K s (m + order P) H := by
  obtain ⟨D, hD, hd⟩ := compact_conjugated_bound hU hO hQcompact hQO P hP m B R hB hR
  refine ⟨D, hD, ?_⟩
  intro G φ hG hφ hGQ s τ ε hτ hs hτs hs1 hε hε1 hGb hφb t ht H
  let C := supportedWeightedSeminorm K s (m + order P) H
  have hC : 0 ≤ C := apply_nonneg _ _
  by_cases hC0 : C = 0
  · have hH0 : H = 0 := supportedField_eq_zero_of_seminorm_eq_zero s (m + order P) hC0
    simp only [hH0, map_zero, mul_zero, le_refl]
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hCs : ∀ j : Fin 3, 0 < (![C, 1, 1] j) := by
      intro j
      fin_cases j <;> simp [hCpos]
    have hHb : ∀ j, WeightedBound U s (m + order P) (![C, 1, 1] j) (singleDirection H j) := by
      intro j
      fin_cases j
      · exact (weightedBound_of_supportedSeminorm s (m + order P) H).restrict_open hU
      · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
      · exact (weightedBound_zero U s (m + order P)).mono_const zero_le_one
    have hΦb : ∀ j v, WeightedBound U s (m + order P) R
        (fun p => fderiv ℝ (singlePhase φ j) p (coordinateVector v)) := by
      intro j v
      fin_cases j
      · exact hφb v
      · change WeightedBound U s (m + order P) R
          (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
        simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
          (weightedBound_zero U s (m + order P) (F := ℝ)).mono_const hR
      · change WeightedBound U s (m + order P) R
          (fun p => fderiv ℝ (fun _ : Base => (0 : ℝ)) p (coordinateVector v))
        simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply] using
          (weightedBound_zero U s (m + order P) (F := ℝ)).mono_const hR
    have hv := hd G (singlePhase φ) (singleDirection H) s τ ε ![C, 1, 1]
      hτ hs hτs hs1 hε hε1 hCs hG (singlePhase_smooth hφ) (singleDirection_smooth H.contDiff)
      hGQ hGb hHb hΦb t ht 0
    have hl : WeightedBound U s m (D * ε * C / τ ^ loss P)
        (conjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H) := by
      apply (show WeightedBound U s m (D * ε * C / τ ^ loss P)
        (fun p => conjugated P ε G (singlePhase φ) (singleDirection H) τ 0 (p, t)) by
          simpa using hv).congr
      intro p _
      exact conjugatedLM_apply hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H p
    have hg := hl.extend_support hU
      ((conjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H).tsupport_subset.trans hKU)
      (by positivity)
    have hn := supportedSeminorm_le_of_weightedBound hs
      (show 0 ≤ D * ε * C / τ ^ loss P by positivity)
      (conjugatedLM hO hU P hP hG (fun _ hp => hQO (hGQ hp)) K hKU hφ τ ε t H) hg
    convert hn using 1
    dsimp only [C]
    ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI

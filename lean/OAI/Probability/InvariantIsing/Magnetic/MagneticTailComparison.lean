import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationClosedPDE
import OAI.Probability.InvariantIsing.Magnetic.MagneticScaledBounds
import OAI.Probability.InvariantIsing.Magnetic.MagneticBoundedInverseComparison
import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationComparison

namespace OAI

/-! Finite-tail comparison with initial inverse-curvature order. The
analytic comparison hypotheses are derived from the actual Gaussian
recursions, leaving only the initial orders for use in a finite induction. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticClosedCurvature_compare_initial (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (hL1 : ∀ av ∈ L, av.1 ≤ 1) (hM1 : ∀ av ∈ M, av.1 ≤ 1)
    {ζ η : ℝ} (hζ : 0 ≤ ζ) (hζη : ζ ≤ η) (hη1 : η ≤ 1)
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      closedMagneticScalarCurvature L hL ζ (0, u) ≤
        closedMagneticScalarCurvature M hM η (0, u))
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticScalarCurvature L hL ζ (v, s) ≤
      closedMagneticScalarCurvature M hM η (v, s) := by
  have hζ1 := hζη.trans hη1
  have hη := hζ.trans hζη
  have hall := inverse_curvature_parabolic_comparison_bound (A := 1) hv hη hζη
    (closedMagneticScalarCurvature L hL ζ) (closedMagneticScalarTime L hL ζ)
    (closedMagneticScalarSlope L hL ζ) (closedMagneticScalarSecond L hL ζ)
    (closedMagneticScalarCurvature M hM η) (closedMagneticScalarTime M hM η)
    (closedMagneticScalarSlope M hM η) (closedMagneticScalarSecond M hM η)
    ((continuousOn_closedMagneticScalarCurvature L hL hL1 hζ hζ1).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩))
    ((continuousOn_closedMagneticScalarCurvature M hM hM1 hη hη1).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩)) hinit
    (fun t ht u _ => (closedMagneticScalarCurvature_hasDerivAt_time L hL hζ ht.1 u).hasDerivWithinAt)
    (fun t ht u _ => (closedMagneticScalarCurvature_hasDerivAt_time M hM hη ht.1 u).hasDerivWithinAt)
    (fun t _ u hu => closedMagneticScalarCurvature_hasDerivAt_spin L hL hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticScalarCurvature_hasDerivAt_spin M hM hη (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticScalarSlope_hasDerivAt_spin L hL hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticScalarSlope_hasDerivAt_spin M hM hη (abs_lt.mpr hu) t)
    (fun p _ => closedMagneticScalarCurvature_nonneg L hL hζ p)
    (fun p _ => closedMagneticScalarCurvature_nonneg M hM hη p)
    (fun p hp => closedMagneticScalarCurvature_le_one L hL hL1 hζ hζ1 p hp.2)
    (fun p _ => closedMagneticScalarCurvature_weighted_second_bound_nonneg L hL hL1 hζ hζ1 p)
    (fun t _ => by
      obtain ⟨ha, hb⟩ := closedMagneticScalarCurvature_endpoints L hL ζ t
      obtain ⟨hc, hd⟩ := closedMagneticScalarCurvature_endpoints M hM η t
      exact ⟨ha, hc, hb, hd⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact hall (v, s) ⟨⟨hv, le_rfl⟩, hs⟩

theorem magneticClosedSquare_compare_initial (L M : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hM : ∀ av ∈ M, 0 < av.1)
    (hL1 : ∀ av ∈ L, av.1 ≤ 1) (hM1 : ∀ av ∈ M, av.1 ≤ 1)
    (i : Fin (L.length + 1)) (j : Fin (M.length + 1))
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hcurv : ∀ u ∈ Icc (-1 : ℝ) 1,
      closedMagneticScalarCurvature L hL ζ (0, u) ≤
        closedMagneticScalarCurvature M hM ζ (0, u))
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      closedMagneticContinuation L (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ (0, u) ≤
        closedMagneticContinuation M (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet ζ (0, u))
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    closedMagneticContinuation L (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet ζ (v, s) ≤
      closedMagneticContinuation M (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet ζ (v, s) := by
  let A := (magneticScalarSquareFourJet L hL i).toMagneticContinuationJet
  let B := (magneticScalarSquareFourJet M hM j).toMagneticContinuationJet
  have hall := magnetic_continuation_coefficient_comparison hv
    (closedMagneticContinuation L A ζ) (closedMagneticContinuationTime L hL A ζ)
    (closedMagneticContinuationSlope L hL A ζ) (closedMagneticContinuationSecond L hL A ζ)
    (closedMagneticContinuation M B ζ) (closedMagneticContinuationTime M hM B ζ)
    (closedMagneticContinuationSlope M hM B ζ) (closedMagneticContinuationSecond M hM B ζ)
    (closedMagneticScalarCurvature L hL ζ) (closedMagneticScalarCurvature M hM ζ)
    ((continuousOn_closedMagneticContinuation L hL A
      (magneticScalarSquareFourJet_sandwich L hL i) hζ).mono (fun p hp => ⟨mem_univ _, hp.2⟩))
    ((continuousOn_closedMagneticContinuation M hM B
      (magneticScalarSquareFourJet_sandwich M hM j) hζ).mono (fun p hp => ⟨mem_univ _, hp.2⟩)) hinit
    (fun t ht u _ => (closedMagneticContinuation_hasDerivAt_time L hL A hζ ht.1 u).hasDerivWithinAt)
    (fun t ht u _ => (closedMagneticContinuation_hasDerivAt_time M hM B hζ ht.1 u).hasDerivWithinAt)
    (fun t _ u hu => closedMagneticContinuation_hasDerivAt_spin L hL A hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticContinuation_hasDerivAt_spin M hM B hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticContinuationSlope_hasDerivAt_spin L hL A hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticContinuationSlope_hasDerivAt_spin M hM B hζ (abs_lt.mpr hu) t)
    (fun p _ => closedMagneticScalarCurvature_nonneg L hL hζ p)
    (fun p hp => magneticClosedCurvature_compare_initial L M hL hM hL1 hM1 hζ
      (le_refl ζ) hζ1 hcurv hp.1.1 hp.2)
    (fun p hp => closedMagneticSquareContinuationSecond_nonneg L hL hL1 i hζ hζ1 hp.1.1.le p.2)
    (fun t _ => closedMagneticScalarCurvature_endpoints M hM ζ t)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact hall (v, s) ⟨⟨hv, le_rfl⟩, hs⟩

end InvariantIsing

end

end OAI

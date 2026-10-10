import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabClosedDerivatives
import OAI.Probability.InvariantIsing.Magnetic.MagneticInverseComparison

namespace OAI

/-! The actual finite-slab inverse curvature increases with its exponent.
All comparison hypotheses, including the degenerate endpoints and
uniform zeroth-order coefficient bound, are discharged here. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem magneticScalarInverseCurvature_exponent_mono (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {ζ η : ℝ} (hζ : 0 < ζ) (hζη : ζ ≤ η) (hη1 : η ≤ 1)
    {v s : ℝ} (hv : 0 ≤ v) (hs : |s| < 1) :
    magneticScalarInverseCurvature L hL ζ v s ≤ magneticScalarInverseCurvature L hL η v s := by
  have hζ1 := hζη.trans hη1
  have hη : 0 ≤ η := hζ.le.trans hζη
  have ht := inverse_curvature_parabolic_comparison hv hη hζη
    (closedMagneticScalarCurvature L hL ζ) (closedMagneticScalarTime L hL ζ)
    (closedMagneticScalarSlope L hL ζ) (closedMagneticScalarSecond L hL ζ)
    (closedMagneticScalarCurvature L hL η) (closedMagneticScalarTime L hL η)
    (closedMagneticScalarSlope L hL η) (closedMagneticScalarSecond L hL η)
    ((continuousOn_closedMagneticScalarCurvature L hL hL1 hζ.le hζ1).mono
      (by intro p hp; exact ⟨mem_univ _, hp.2⟩))
    ((continuousOn_closedMagneticScalarCurvature L hL hL1 hη hη1).mono
      (by intro p hp; exact ⟨mem_univ _, hp.2⟩))
    (fun u _ => (closedMagneticScalarCurvature_initial L hL ζ η u).le)
    (fun t ht u _ => (closedMagneticScalarCurvature_hasDerivAt_time L hL hζ.le ht.1 u).hasDerivWithinAt)
    (fun t ht u _ => (closedMagneticScalarCurvature_hasDerivAt_time L hL hη ht.1 u).hasDerivWithinAt)
    (fun t _ u hu => closedMagneticScalarCurvature_hasDerivAt_spin L hL hζ.le (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticScalarCurvature_hasDerivAt_spin L hL hη (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticScalarSlope_hasDerivAt_spin L hL hζ.le (abs_lt.mpr hu) t)
    (fun t _ u hu => closedMagneticScalarSlope_hasDerivAt_spin L hL hη (abs_lt.mpr hu) t)
    (fun p _ => closedMagneticScalarCurvature_nonneg L hL hζ.le p)
    (fun p _ => closedMagneticScalarCurvature_nonneg L hL hη p)
    (fun p hp => closedMagneticScalarCurvature_le_one L hL hL1 hζ.le hζ1 p hp.2)
    (fun p _ => closedMagneticScalarCurvature_weighted_second_bound L hL hL1 hζ hζ1 p)
    (fun t _ => by
      have ha := closedMagneticScalarCurvature_endpoints L hL ζ t
      have hb := closedMagneticScalarCurvature_endpoints L hL η t
      exact ⟨ha.1, hb.1, ha.2, hb.2⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
  have hh := ht (v, s) ⟨⟨hv, le_rfl⟩, (abs_le.mp hs.le)⟩
  simpa only [closedMagneticScalarCurvature, hs, ite_true] using hh

end InvariantIsing

end

end OAI

import OAI.Probability.SLE.Multipoint.MultipointClippedState
import OAI.Probability.SLE.Multipoint.MultipointStoppedCoordinates
import OAI.Probability.SLE.FiniteRadiusStop

namespace OAI

/-! Safe clipped coordinates identify the actual Loewner flow separately
up to each point's completion or the common localization time. -/

noncomputable section
open Set
open scoped NNReal

namespace SLEExactGauge.Multipoint

theorem clipped_multipoint_identification {ι : Type*} [Fintype ι]
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (lo hi : ℝ) (hle : lo ≤ hi) (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane)
    (T : ι → ℝ≥0) (Q : ℝ → ι → ℂ × ℝ)
    (hQ0 : ∀ i, Q 0 i = initialLogCoordinates (z i))
    (hQd : ∀ t, 0 ≤ t → HasDerivWithinAt Q
      (fun i => clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t i)) (Ici 0) t)
    (hheight : ∀ i t, t ∈ Icc 0 (T i : ℝ) → (Q t i).1.im ∈ Icc lo hi) :
    ∀ i, z i ∈ survivingDomain γ (T i) ∧
      EqOn (fun t => Q t i) (logLoewnerCoordinates G (z i)) (Icc 0 (T i : ℝ)) := by
  intro i
  apply clipped_log_identification hU hw (z i) (hz i) (T i) lo hi hle
    (fun t => Q t i) (hQ0 i)
  · intro t ht
    exact ((hasDerivWithinAt_pi.mp (hQd t ht.1)) i).mono (fun _ hs => hs.1)
  · exact hheight i

theorem stopped_height_gives_local_identification
    {Ω ι : Type*} [Fintype ι]
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hU : Continuous U) (hw : IsCapacityTwoWitness U γ G F)
    (lo hi : ℝ) (hle : lo ≤ hi) (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane)
    (Q : ℝ → Ω → ι → ℂ × ℝ) (τ : ι → Ω → ℝ≥0) (χ : Ω → ℝ≥0) (ω : Ω)
    (hQ0 : ∀ i, Q 0 ω i = initialLogCoordinates (z i))
    (hQd : ∀ t, 0 ≤ t → HasDerivWithinAt (fun t => Q t ω)
      (fun i => clippedLogLoewnerField lo hi hle (U t.toNNReal) (Q t ω i)) (Ici 0) t)
    (hheight : ∀ (t : ℝ≥0), t ≤ χ ω → ∀ i,
      (stoppedCoordinateState Q τ t ω i).1.im ∈ Icc lo hi) :
    ∀ i, z i ∈ survivingDomain γ (min (τ i ω) (χ ω)) ∧
      EqOn (fun t => Q t ω i) (logLoewnerCoordinates G (z i))
        (Icc 0 (min (τ i ω) (χ ω) : ℝ≥0)) := by
  apply clipped_multipoint_identification hU hw lo hi hle z hz
    (fun i => min (τ i ω) (χ ω)) (fun t => Q t ω) hQ0 hQd
  intro i t ht
  have htτ : t ≤ (τ i ω : ℝ) := ht.2.trans (by exact_mod_cast min_le_left (τ i ω) (χ ω))
  have htχ : t ≤ (χ ω : ℝ) := ht.2.trans (by exact_mod_cast min_le_right (τ i ω) (χ ω))
  have hh := hheight t.toNNReal (Real.toNNReal_le_iff_le_coe.mpr htχ) i
  simpa only [stoppedCoordinateState, Real.coe_toNNReal t ht.1, min_eq_left htτ] using hh

end SLEExactGauge.Multipoint

end

end OAI

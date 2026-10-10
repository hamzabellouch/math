import OAI.Probability.SLE.Multipoint.MultipointLocalIdentification
import OAI.Probability.SLE.Multipoint.MultipointLocalization

namespace OAI

/-! The concrete localized state used by the multipoint product. Each
coordinate is frozen at its own completion; the common stop only bounds
the driver and the remaining coordinate heights. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SLEExactGauge.Multipoint

structure LocalizedState {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (κ lo hi M : ℝ) (H : ℝ≥0) (z : ι → ℂ) (τ : ι → Ω → ℝ≥0)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ) where
  L : ℝ≥0
  Q : ℝ → Ω → ι → ℂ × ℝ
  V : ℝ → Ω → ι → ℂ × ℝ
  χ : Ω → ℝ≥0
  measurable : Measurable (fun p : ℝ × Ω => Q p.1 p.2)
  adapted : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun t : ℝ≥0 => Q t)
  lipschitz : ∀ ω, LipschitzWith L (fun t => Q t ω)
  velocity_measurable : Measurable (fun p : ℝ × Ω => V p.1 p.2)
  velocity_bound : ∀ t ω, ‖V t ω‖ ≤ L
  derivative : ∀ ω, ∀ᵐ t : ℝ, 0 < t → HasDerivAt (fun u => Q u ω) (V t ω) t
  initial : ∀ ω i, Q 0 ω i = initialLogCoordinates (z i)
  frozen : ∀ ω (t : ℝ≥0) i, τ i ω ≤ t → Q t ω i = Q (τ i ω) ω i
  stopping : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
    (fun ω => (χ ω : WithTop ℝ≥0))
  bounded : ∀ ω, χ ω ≤ H
  heights : ∀ ω (t : ℝ≥0), t ≤ χ ω → ∀ i, (Q t ω i).1.im ∈ Icc lo hi
  driver_bound : ∀ ω t, t ≤ χ ω → |B t ω| ≤ M
  strict_heights : ∀ ω (t : ℝ≥0), t < χ ω → ∀ i, (Q t ω i).1.im ∈ Ioo lo hi
  strict_driver : ∀ ω t, t < χ ω → |B t ω| < M
  boundary : ∀ ω, χ ω < H →
    (∃ i, (Q (χ ω) ω i).1.im = lo ∨ (Q (χ ω) ω i).1.im = hi) ∨ |B (χ ω) ω| = M
  physical_velocity : ∀ ω (t : ℝ≥0), t < χ ω → ∀ i, t < τ i ω →
    V t ω i = physicalLogLoewnerField (Real.sqrt κ*B t ω) (Q t ω i)
  actual : ∀ ω i, z i ∈ survivingDomain (γ ω) (min (τ i ω) (χ ω)) ∧
    EqOn (fun t => Q t ω i) (logLoewnerCoordinates (G ω) (z i))
      (Icc 0 (min (τ i ω) (χ ω) : ℝ≥0))

theorem exists_localizedState
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
    (B : ℝ≥0 → Ω → ℝ) (hm : ∀ t, Measurable (B t))
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ lo hi M : ℝ) (hle : lo ≤ hi) (H : ℝ≥0)
    (z : ι → ℂ) (hz : ∀ i, z i ∈ upperHalfPlane)
    (hzlo : ∀ i, lo ≤ Real.log (z i).im) (hzhi : ∀ i, Real.log (z i).im ≤ hi)
    (hB0 : ∀ ω, |B 0 ω| ≤ M)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => (τ i ω : WithTop ℝ≥0)))
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω)) :
    Nonempty (LocalizedState B hm κ lo hi M H z τ γ G) := by
  classical
  obtain ⟨L,Q,V,hQm,hQa,hQl,hVm,hVb,hQd,hQdw,hQ0,hfield⟩ :=
    exists_clipped_multipoint_state B hm hBm hBc κ lo hi hle (fun i => initialLogCoordinates (z i))
  obtain ⟨hSm,hSa,hSl,hSVm,hSVb,hSd⟩ := stoppedCoordinateState_regular _ Q V τ L
    hQm hQa hQl hVm hVb hQd hτ
  let S := stoppedCoordinateState Q τ
  let W := stoppedCoordinateVelocity V τ
  have hS0 (ω : Ω) (i : ι) : S 0 ω i = initialLogCoordinates (z i) := by
    rw [show S 0 ω = Q 0 ω from stoppedCoordinateState_initial Q τ ω, hQ0 ω]
  have hBa : Adapted (Filtration.natural B (fun t => (hm t).stronglyMeasurable)) B :=
    (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).adapted
  obtain ⟨χ,hχ,hχH,hbounds,hstrict,hboundary⟩ := exists_multipoint_localization _ S B hSa
    (fun ω => (hSl ω).continuous) hBa hBc lo hi M H
    (fun ω i => by simpa only [hS0 ω i, initialLogCoordinates, Complex.add_im,
      Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
      mul_one, mul_zero, add_zero, zero_add] using And.intro (hzlo i) (hzhi i)) hB0
  have hheight (ω : Ω) (t : ℝ≥0) (ht : t ≤ χ ω) (i : ι) :
      (S t ω i).1.im ∈ Icc lo hi := (hbounds ω t ht).1 i
  refine ⟨{
    L := L, Q := S, V := W, χ := χ, measurable := hSm, adapted := hSa,
    lipschitz := hSl, velocity_measurable := hSVm, velocity_bound := hSVb,
    derivative := hSd, initial := hS0,
    frozen := fun ω t i ht => by
      have ht' : (τ i ω : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      simp only [S,stoppedCoordinateState,min_eq_right ht',min_self],
    stopping := hχ, bounded := hχH,
    heights := hheight, driver_bound := fun ω t ht => (hbounds ω t ht).2,
    strict_heights := fun ω t ht i => (hstrict ω t ht).1 i,
    strict_driver := fun ω t ht => (hstrict ω t ht).2, boundary := hboundary,
    physical_velocity := ?_, actual := ?_ }⟩
  · intro ω t ht i hti
    have htir : (t : ℝ) < (τ i ω : ℝ) := by exact_mod_cast hti
    have he : S t ω i = Q t ω i := by simp only [S,stoppedCoordinateState,min_eq_left htir.le]
    change (if (t : ℝ) < (τ i ω : ℝ) then V t ω i else 0) = _
    rw [ite_eq_left htir, hfield, ← he, Real.toNNReal_coe]
    exact clippedLogLoewnerField_eq_physical lo hi hle _ _ (hheight ω t ht.le i)
  · intro ω i
    have hid := stopped_height_gives_local_identification (continuous_const.mul (hBc ω))
      (hw ω) lo hi hle z hz Q τ χ ω (fun i => congrFun (hQ0 ω) i)
      (fun t ht => by
        have hv : V t ω = fun i => clippedLogLoewnerField lo hi hle
            (Real.sqrt κ*B t.toNNReal ω) (Q t ω i) := funext (hfield t ω)
        simpa only [hv, Pi.mul_apply] using hQdw ω t ht) (hheight ω)
    refine ⟨(hid i).1, ?_⟩
    intro t ht
    have hti : t ≤ (τ i ω : ℝ) := ht.2.trans (by exact_mod_cast min_le_left (τ i ω) (χ ω))
    change S t ω i = logLoewnerCoordinates (G ω) (z i) t
    rw [show S t ω i = Q t ω i by simp only [S,stoppedCoordinateState,min_eq_left hti]]
    exact (hid i).2 ht

end SLEExactGauge.Multipoint

end

end OAI

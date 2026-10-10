import OAI.Probability.SLE.Mass.CanonicalMassContinuity
import OAI.Probability.SLE.Geometry.MonotoneRationalLimit

namespace OAI

/-! One common convex sequence converges at every finite time, on one
event of full probability. In particular it can be evaluated at a random time. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem RationalCanonicalMass.all_finite_times_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hκ : 0 < κ) (hκ8 : κ < 8)
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (C : RationalCanonicalMass P κ B hBm γ G)
    (N : ℝ≥0 → Ω → Measure upperHalfPlane)
    (hNr : ∀ t ω, (N t ω).Regular ∧ IsFiniteMeasureOnCompacts (N t ω))
    (hpath : ∀ᵐ ω ∂P, ContinuousMassPath (γ ω) (fun q => C.mass q ω)
      (C.terminal ω) (fun t => N t ω)) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) (f : C_c(upperHalfPlane,ℝ)),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ))
        C.supports C.weights n t ω) atTop (𝓝 (∫ z, f z ∂N t ω)) := by
  filter_upwards [C.mass_limit,hpath] with ω hl hp
  let M (n : ℕ) (t : ℝ≥0) := convexLevelMeasure κ B γ G (fun n => (n:ℝ))
    C.supports C.weights n t ω
  let (n : ℕ) (t : ℝ≥0) : IsFiniteMeasureOnCompacts (M n t) :=
    convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω)
      _ C.supports C.weights n t
  let (t : ℝ≥0) : IsFiniteMeasureOnCompacts (N t ω) := (hNr t ω).2
  have hpositive (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z) (t : ℝ≥0) :
      Tendsto (fun n => ∫ z, f z ∂M n t) atTop (𝓝 (∫ z, f z ∂N t ω)) := by
    have hrat (q : ℚ) :
        Tendsto (fun n => ∫ z, f z ∂M n (q:ℝ).toNNReal) atTop
          (𝓝 (∫ z, f z ∂N (q:ℝ).toNNReal ω)) := by
      by_cases hq : 0 ≤ q
      · rw [hp.rational q hq]
        exact hl q f
      · have he : (q:ℝ).toNNReal = 0 :=
          Real.toNNReal_eq_zero.mpr (Rat.cast_nonpos.mpr (le_of_not_ge hq))
        have hzero : N 0 ω = C.mass 0 ω := by
          simpa only [Rat.cast_zero,Real.toNNReal_zero] using hp.rational 0 le_rfl
        simpa only [he,hzero,Rat.cast_zero,Real.toNNReal_zero] using hl 0 f
    have hlim := tendsto_of_monotone_rational_limits
      (fun n r => ∫ z, f z ∂M n r.toNNReal)
      (fun r => ∫ z, f z ∂N r.toNNReal ω) (fun n r s hrs =>
        integral_mono_measure (convexLevelMeasure_mono κ B γ G (fun n => (n:ℝ))
          C.supports C.weights n ω (ENNReal.coe_le_coe.mpr (Real.toNNReal_mono hrs)))
          (ae_of_all _ hf) f.integrable)
      ((hp.continuous_tests f).comp continuous_real_toNNReal) hrat (t:ℝ)
    simpa only [Real.toNNReal_coe] using hlim
  intro t f
  let fp := f ⊔ 0
  let fm := (-f) ⊔ 0
  have hsplit (ρ : Measure upperHalfPlane) [IsFiniteMeasureOnCompacts ρ] :
      (∫ z, f z ∂ρ) = (∫ z, fp z ∂ρ)-(∫ z, fm z ∂ρ) := by
    rw [← integral_sub fp.integrable fm.integrable]
    apply integral_congr_ae
    filter_upwards [] with z
    change f z = max (f z) 0-max (-f z) 0
    exact (max_zero_sub_eq_self (f z)).symm
  simpa only [← hsplit] using
    (hpositive fp (fun z => le_sup_of_le_right (by rfl)) t).sub
      (hpositive fm (fun z => le_sup_of_le_right (by rfl)) t)

end SLEExactGauge.Multipoint

end

end OAI

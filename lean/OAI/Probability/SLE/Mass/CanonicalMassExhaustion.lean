import OAI.Probability.SLE.Mass.CanonicalMassContinuity
import OAI.Probability.SLE.Geometry.GreenCompactDecay
import OAI.Probability.SLE.Mass.MonotoneMassExhaustion
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

namespace OAI

/-! The actual canonical terminal measure is exhausted by finite times,
locally in total variation. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

lemma RationalCanonicalMass.mass_ambient_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : RationalCanonicalMass P κ B hBm γ G) (q : ℚ) : Measurable (C.mass q) :=
  (C.mass_measurable q).mono (Filtration.le _ _) le_rfl

lemma RationalCanonicalMass.integer_remaining_mean
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : RationalCanonicalMass P κ B hBm γ G) (K : Set upperHalfPlane) (hK : IsCompact K)
    (n : ℕ) :
    (∫⁻ ω, C.terminal ω K-C.mass n ω K ∂P) =
      P.bind (halfPlaneGreenMeasure κ B γ G n) K := by
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  have hmm : Measurable (fun ω => C.mass n ω K) :=
    (Measure.measurable_coe hK.measurableSet).comp (C.mass_ambient_measurable n)
  have hk := congrArg (fun ρ : Measure upperHalfPlane => ρ K)
    (C.conditional n univ MeasurableSet.univ)
  simp only [Measure.restrict_univ,Measure.add_apply,Rat.cast_natCast,
    Real.toNNReal_natCast] at hk
  rw [Measure.bind_apply hK.measurableSet C.terminal_measurable.aemeasurable,
    Measure.bind_apply hK.measurableSet (C.mass_ambient_measurable n).aemeasurable] at hk
  have htf : (∫⁻ ω, C.terminal ω K ∂P) < ∞ := by
    rw [← Measure.bind_apply hK.measurableSet C.terminal_measurable.aemeasurable,C.mean]
    exact hK.measure_lt_top
  have hmf : (∫⁻ ω, C.mass n ω K ∂P) ≠ ∞ :=
    (lt_of_le_of_lt (by rw [hk]; exact le_add_right le_rfl) htf).ne
  have hle : (fun ω => C.mass n ω K) ≤ᵐ[P] (fun ω => C.terminal ω K) :=
    C.increments.mono (fun _ hω => hω.dominated n K)
  rw [lintegral_sub hmm hmf hle,hk,ENNReal.add_sub_cancel_left hmf]

theorem RationalCanonicalMass.finite_times_exhaust_terminal
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (hBc : ∀ ω, Continuous (fun s => B s ω))
    (hB0 : ∀ ω, B 0 ω = 0) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (C : RationalCanonicalMass P κ B hBm γ G)
    (N : ℝ≥0 → Ω → Measure upperHalfPlane)
    (hpath : ∀ᵐ ω ∂P, ContinuousMassPath (γ ω) (fun q => C.mass q ω)
      (C.terminal ω) (fun t => N t ω)) :
    ∀ᵐ ω ∂P, ∀ K : Set upperHalfPlane, IsCompact K →
      Tendsto (fun t : ℝ≥0 => (C.terminal ω-N t ω) K) atTop (𝓝 0) := by
  let D := localTestFamily upperHalfPlane
  have hm (n j : ℕ) : Measurable (fun ω => C.terminal ω (D.compactSet j)-C.mass n ω (D.compactSet j)) :=
    ((Measure.measurable_coe (D.isCompact j).measurableSet).comp C.terminal_measurable).sub
      ((Measure.measurable_coe (D.isCompact j).measurableSet).comp (C.mass_ambient_measurable n))
  have ha (j : ℕ) : ∀ᵐ ω ∂P, Antitone (fun n : ℕ => C.terminal ω (D.compactSet j)-C.mass n ω (D.compactSet j)) := by
    filter_upwards [C.increments] with ω hω
    intro n m hnm
    exact tsub_le_tsub_left (hω.monotone (Nat.cast_le.mpr hnm) (D.compactSet j)) _
  have hmean (j : ℕ) : Tendsto (fun n : ℕ => ∫⁻ ω,
      C.terminal ω (D.compactSet j)-C.mass n ω (D.compactSet j) ∂P) atTop (𝓝 0) := by
    simp_rw [C.integer_remaining_mean _ (D.isCompact j)]
    exact halfPlaneGreenMeasure_compact_mean_tendsto_zero hB hBm hBc hB0 hκ hκ8 γ G F hw _ (D.isCompact j)
  have hzero (j : ℕ) := ae_tendsto_zero_of_antitone_lintegral P _ (fun n => hm n j) (ha j) (hmean j)
  filter_upwards [ae_all_iff.mpr hzero,hpath] with ω hz hp
  let : (C.terminal ω).Regular := (C.terminal_radon ω).1
  have hD (j : ℕ) : Tendsto (fun t : ℝ≥0 => (C.terminal ω-N t ω) (D.compactSet j))
      atTop (𝓝 0) := by
    apply ENNReal.tendsto_atTop_zero.mpr
    intro ε hε
    obtain ⟨n,hn⟩ := ENNReal.tendsto_atTop_zero.mp (hz j) ε hε
    refine ⟨n,fun t ht => ?_⟩
    have hnat : N n ω = C.mass n ω := by
      simpa only [Rat.cast_natCast,Real.toNNReal_natCast] using hp.rational n (Nat.cast_nonneg n)
    have horder : C.mass n ω ≤ N t ω := by rw [← hnat]; exact hp.monotone ht
    have hdom := hp.dominated t
    let : IsFiniteMeasureOnCompacts (N t ω) :=
      ⟨fun K hK => lt_of_le_of_lt (hdom K) hK.measure_lt_top⟩
    rw [sub_apply_of_finite_restriction hdom (D.isCompact j).measurableSet
      (D.isCompact j).measure_lt_top.ne]
    exact (tsub_le_tsub_left (horder _) _).trans (hn n le_rfl)
  intro K hK
  obtain ⟨j,hj⟩ := D.exhaustive K hK
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hD j)
    (fun _ => zero_le) (fun t => measure_mono hj)

end SLEExactGauge.Multipoint

end

end OAI

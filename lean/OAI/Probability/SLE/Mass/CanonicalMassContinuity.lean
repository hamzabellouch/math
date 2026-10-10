import OAI.Probability.SLE.Mass.RationalCanonicalMass
import OAI.Probability.SLE.Mass.RationalTraceMassSupport
import OAI.Probability.SLE.Mass.RationalTraceMassLocalVariation
import OAI.Probability.SLE.Mass.RationalTraceMassProgressiveVersion

namespace OAI

/-! The actual rational construction extends to an adapted, locally
continuous family, with simultaneous support of every finite increment. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

structure ContinuousMassPath (γ : ℝ≥0 → ℂ) (μ : ℚ → Measure upperHalfPlane)
    (ν : Measure upperHalfPlane) (N : ℝ≥0 → Measure upperHalfPlane) : Prop where
  zero : N 0 = 0
  dominated : ∀ t, N t ≤ ν
  monotone : Monotone N
  rational : ∀ q : ℚ, 0 ≤ q → N (q:ℝ).toNNReal = μ q
  continuous_tests : ∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂N t)
  increment_support : ∀ s t, s ≤ t →
    (N t-N s) {z : upperHalfPlane | (z:ℂ) ∉
      (fun r : ℝ => γ r.toNNReal) '' Icc (s:ℝ) t} = 0
  local_variation : ∀ K : Set upperHalfPlane, IsCompact K →
    ∀ t₀ : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s t : ℝ≥0, dist (s:ℝ) t₀ < δ → dist (t:ℝ) t₀ < δ →
        ∀ A : Set upperHalfPlane, MeasurableSet A → A ⊆ K →
          |(N s A).toReal-(N t A).toReal| < ε

theorem RationalCanonicalMass.exists_continuous_progressive_extension
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
    {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
    (C : RationalCanonicalMass P κ B hBm γ G) (hγ : ∀ ω, Continuous (γ ω)) :
    ∃ N : ℝ≥0 → Ω → Measure upperHalfPlane,
      IsProgressive (Filtration.natural B (fun r =>
        (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) N ∧
      (∀ t ω, (N t ω).Regular ∧ IsFiniteMeasureOnCompacts (N t ω)) ∧
      ∀ᵐ ω ∂P, ContinuousMassPath (γ ω) (fun q => C.mass q ω) (C.terminal ω) (fun t => N t ω) := by
  let Good (ω : Ω) : Prop :=
    HalfPlaneTraceIncrements (fun q => C.mass q ω) (C.terminal ω)
      (fun r : ℝ => γ ω r.toNNReal) ∧ NullSingletonClass (C.terminal ω)
  have hex (ω : Ω) : ∃ M : ℝ → Measure upperHalfPlane,
      (∀ t, (M t).Regular) ∧
      (∀ f : C_c(upperHalfPlane,ℝ), Continuous (fun t => ∫ z, f z ∂M t)) ∧
      (Good ω → (∀ t, M t ≤ C.terminal ω) ∧ (∀ q : ℚ, M q = C.mass q ω) ∧
        Monotone M ∧
        (∀ K : Set upperHalfPlane, IsCompact K →
          ∀ t₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
            ∀ s t : ℝ, dist s t₀ < δ → dist t t₀ < δ →
              ∀ A : Set upperHalfPlane, MeasurableSet A → A ⊆ K →
                |(M s A).toReal-(M t A).toReal| < ε)) := by
    by_cases h : Good ω
    · let : (C.terminal ω).Regular := (C.terminal_radon ω).1
      let : NullSingletonClass (C.terminal ω) := h.2
      obtain ⟨M,hr,hd,hq,hm,hc,hv⟩ := h.1.exists_locally_tv_continuous_extension
        ((hγ ω).comp continuous_real_toNNReal)
      exact ⟨M,hr,hc,fun _ => ⟨hd,hq,hm,hv⟩⟩
    · refine ⟨fun _ => 0,fun _ => inferInstance,?_,fun hh => (h hh).elim⟩
      intro f
      simpa only [integral_zero_measure] using (continuous_const : Continuous (fun _ : ℝ => (0:ℝ)))
  choose M hMr hMc hM using hex
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, M ω q = C.mass q ω := by
    filter_upwards [C.increments,C.nonatomic] with ω hi hn
    exact (hM ω ⟨hi,hn⟩).2.1
  let N := rationalRadonExtension C.mass
  have hNp : IsProgressive (Filtration.natural B (fun r =>
      (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable)) N :=
    rationalRadonExtension_progressive _ C.mass (fun q ω => (C.mass_radon q ω).1)
      (fun q _ => C.mass_measurable q)
  have hNr := rationalRadonExtension_regular C.mass
  have hNe := rationalRadonExtension_common_version P C.mass (fun t ω => M ω t)
    (fun t ω => hMr ω t) (Eventually.of_forall hMc) hrat
  refine ⟨N,hNp,hNr,?_⟩
  filter_upwards [C.increments,C.nonatomic,C.zero,hNe] with ω hi hn hz he
  change ∀ t : ℝ≥0, N t ω = M ω t at he
  obtain ⟨hd,hq,hm,hv⟩ := hM ω ⟨hi,hn⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · rw [he 0]
    simpa only [NNReal.coe_zero,Rat.cast_zero] using (hq 0).trans hz
  · intro t
    rw [he t]
    exact hd t
  · intro s t hst
    change N s ω ≤ N t ω
    rw [he s,he t]
    exact hm (NNReal.coe_le_coe.mpr hst)
  · intro q hq0
    rw [he _ ,Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hq0)]
    exact hq q
  · intro f
    have hc := (hMc ω f).comp NNReal.continuous_coe
    simpa only [Function.comp_def,← he] using hc
  · intro s t hst
    rw [he s,he t]
    let : (C.terminal ω).Regular := (C.terminal_radon ω).1
    exact hi.extension_increment_carried ((hγ ω).comp continuous_real_toNNReal)
      (M ω) (hMr ω) hq hm (NNReal.coe_le_coe.mpr hst)
  · intro K hK t₀ ε hε
    obtain ⟨δ,hδ,hδprop⟩ := hv K hK t₀ ε hε
    refine ⟨δ,hδ,?_⟩
    intro s t hs ht A hA hAK
    rw [he s,he t]
    exact hδprop s t hs ht A hA hAK

end SLEExactGauge.Multipoint

end

end OAI

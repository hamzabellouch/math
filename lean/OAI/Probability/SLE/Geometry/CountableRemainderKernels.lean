import OAI.Probability.SLE.Mass.CountableLevelKernel
import OAI.Probability.SLE.Geometry.RemainderKernelCancellation

namespace OAI

/-! Positive measurable remaining masses, with the exact Green kernel,
for the actual common countable-time Radon construction. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem exists_countable_radon_remainder_kernels
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (t : ℕ → ℝ≥0) :
    ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ,
    ∃ ν η : ℕ → Ω → Measure upperHalfPlane,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧ (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ j, Measurable (ν j)) ∧
      (∀ j ω, (ν j ω).Regular ∧ IsFiniteMeasureOnCompacts (ν j ω)) ∧
      (∀ᵐ ω ∂P, ∀ j (f : C_c(upperHalfPlane,ℝ)),
        Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ)) s w n
          (levelMassTimes t j) ω) atTop (𝓝 (∫ z, f z ∂ν j ω))) ∧
      (∀ j, Measurable (η j)) ∧
      (∀ j ω, (η j ω).Regular ∧ IsFiniteMeasureOnCompacts (η j ω)) ∧
      (∀ᵐ ω ∂P, ∀ j, η j ω + ν (j+1) ω = ν 0 ω) ∧
      P.bind (ν 0) = initialGreenMeasure κ ∧
      ∀ j (E : Set Ω),
        MeasurableSet[Filtration.natural B (fun r =>
          (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable) (t j)] E →
        (P.restrict E).bind (η j) = (P.restrict E).bind (halfPlaneGreenMeasure κ B γ G (t j)) := by
  obtain ⟨s,w,ν,hw₀,hw₁,hνm,hν,hlim,hmean,hkernel⟩ :=
    exists_countable_level_radon_kernels hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth t
  have horder : ∀ᵐ ω ∂P, ∀ j, ν (j+1) ω ≤ ν 0 ω := by
    filter_upwards [hlim] with ω hω
    intro j
    let (i : ℕ) : (ν i ω).Regular := (hν i ω).1
    let (n i : ℕ) : IsFiniteMeasureOnCompacts
        (convexLevelMeasure κ B γ G (fun n => (n:ℝ)) s w n (levelMassTimes t i) ω) :=
      convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) _ s w n _
    apply radon_limits_mono _ _ (ν (j+1) ω) (ν 0 ω) (hω (j+1)) (hω 0)
    intro n
    simpa only [levelMassTimes_zero,levelMassTimes_succ] using
      convexLevelMeasure_mono κ B γ G (fun n => (n:ℝ)) s w n ω
        (le_top : (t j : ℝ≥0∞) ≤ ∞)
  have hex (j : ℕ) := exists_measurable_halfPlane_difference P (ν 0) (ν (j+1))
    (hνm 0) (hνm (j+1)) (fun ω => (hν 0 ω).1) (fun ω => (hν (j+1) ω).1)
    (horder.mono (fun _ hω => hω j))
  choose η hηm hηr hηsum using hex
  refine ⟨s,w,ν,η,hw₀,hw₁,hνm,hν,hlim,hηm,hηr,ae_all_iff.mpr hηsum,hmean,?_⟩
  intro j E hE
  let : IsFiniteMeasureOnCompacts (initialGreenMeasure κ) := initialGreenMeasure_finite_on_compacts κ
  have hbound : (P.restrict E).bind (ν (j+1)) ≤ initialGreenMeasure κ := by
    rw [← hmean]
    exact restricted_bind_le_of_ae_le P (ν (j+1)) (ν 0) (hνm (j+1)) (hνm 0)
      (horder.mono (fun _ hω => hω j)) E
  let : IsFiniteMeasureOnCompacts ((P.restrict E).bind (ν (j+1))) :=
    ⟨fun K hK => lt_of_le_of_lt (hbound K) hK.measure_lt_top⟩
  exact bind_remainder_eq_of_sum (P.restrict E) (ν (j+1)) (ν 0) (η j)
    (hνm (j+1)) (hνm 0) (hηm j) _ (ae_restrict_of_ae (hηsum j)) (hkernel j E hE)

end SLEExactGauge.Multipoint

end

end OAI

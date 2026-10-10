import OAI.Probability.SLE.Mass.LevelRandomRadon

namespace OAI

/-! The measurable common Radon versions retain the L² pairings. In
particular expectations on any past event pass through the same limits. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem exists_measurable_level_radon_limits_with_pairings
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (t : ℕ → ℝ≥0∞) :
    ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ, ∃ ν : ℕ → Ω → Measure upperHalfPlane,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧ (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ j, Measurable (ν j)) ∧
      (∀ j ω, (ν j ω).Regular ∧ IsFiniteMeasureOnCompacts (ν j ω)) ∧
      (∀ᵐ ω ∂P, ∀ j (f : C_c(upperHalfPlane,ℝ)),
        Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
          atTop (𝓝 (∫ z, f z ∂ν j ω))) ∧
      ∀ j k (a : Ω → ℝ), MemLp a 2 P →
        Tendsto (fun n => ∫ ω, a ω * (∫ z, (localTestFamily upperHalfPlane).test k z
          ∂convexLevelMeasure κ B γ G u s w n (t j) ω) ∂P)
          atTop (𝓝 (∫ ω, a ω * (∫ z, (localTestFamily upperHalfPlane).test k z ∂ν j ω) ∂P)) := by
  let D := localTestFamily upperHalfPlane
  obtain ⟨x,s,w,hw₀,hw₁,_,hp,hconv⟩ := exists_common_halfPlane_test_limits_with_pairings
    hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
    (fun j => D.test (Nat.unpair j).2) u hu (fun j => t (Nat.unpair j).1)
  have hex : ∀ᵐ ω ∂P, ∃ ν : ℕ → Measure upperHalfPlane, (∀ j, (ν j).Regular) ∧
      ∀ j (f : C_c(upperHalfPlane,ℝ)),
        Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
          atTop (𝓝 (∫ z, f z ∂ν j)) := by
    filter_upwards [hconv] with ω hω
    have hj (j : ℕ) : ∃ ν : Measure upperHalfPlane, ν.Regular ∧ IsFiniteMeasureOnCompacts ν ∧
        ∀ f : C_c(upperHalfPlane,ℝ),
          Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n (t j) ω)
            atTop (𝓝 (∫ z, f z ∂ν)) := by
      let (n : ℕ) : IsFiniteMeasureOnCompacts (convexLevelMeasure κ B γ G u s w n (t j) ω) :=
        convexLevelMeasure_finite_on_compacts hκ hκ8 γ G F ω (hBc ω) (hw ω) u s w n (t j)
      apply D.exists_radon_limit
      intro k
      refine ⟨x (Nat.pair j k) ω,?_⟩
      simpa only [Nat.unpair_pair] using hω (Nat.pair j k)
    choose ν hν using hj
    exact ⟨ν,fun j => (hν j).1,fun j => (hν j).2.2⟩
  obtain ⟨ν,hνm,hνr,hlim⟩ := exists_measurable_countable_radon_limits P
    (fun n j ω => convexLevelMeasure κ B γ G u s w n (t j) ω)
    (fun n j f => convexLevelMeasure_test_measurable hm hBc hκ hκ8 γ G F hw u hu s w hw₀ n (t j) f) hex
  refine ⟨s,w,ν,hw₀,hw₁,hνm,hνr,hlim,?_⟩
  intro j k a ha
  have heq : (fun ω => x (Nat.pair j k) ω) =ᵐ[P]
      (fun ω => ∫ z, D.test k z ∂ν j ω) := by
    filter_upwards [hconv,hlim] with ω hc hl
    have hc' := hc (Nat.pair j k)
    simp only [Nat.unpair_pair] at hc'
    exact tendsto_nhds_unique hc' (hl j (D.test k))
  have ht := hp (Nat.pair j k) a ha
  simp only [Nat.unpair_pair] at ht
  convert ht using 1
  apply congrArg (fun v : ℝ => 𝓝 v)
  apply integral_congr_ae
  filter_upwards [heq] with ω hω
  exact congrArg (fun v : ℝ => a ω * v) hω.symm

end SLEExactGauge.Multipoint

end

end OAI

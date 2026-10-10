import OAI.Probability.SLE.Mass.LevelRadonKernel
import OAI.Probability.SLE.Mass.LevelRadonPairings
import OAI.Probability.SLE.Mass.LevelRadonMean

namespace OAI

/-! Actual common Radon limits with their exact conditional kernels at
any prescribed countable set of deterministic times. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

def levelMassTimes (t : ℕ → ℝ≥0) : ℕ → ℝ≥0∞
  | 0 => ∞
  | n+1 => t n

@[simp] lemma levelMassTimes_zero (t : ℕ → ℝ≥0) : levelMassTimes t 0 = ∞ := rfl
@[simp] lemma levelMassTimes_succ (t : ℕ → ℝ≥0) (n : ℕ) : levelMassTimes t (n+1) = t n := rfl

theorem exists_countable_level_radon_kernels
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (t : ℕ → ℝ≥0) :
    ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ, ∃ ν : ℕ → Ω → Measure upperHalfPlane,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧ (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ j, Measurable (ν j)) ∧
      (∀ j ω, (ν j ω).Regular ∧ IsFiniteMeasureOnCompacts (ν j ω)) ∧
      (∀ᵐ ω ∂P, ∀ j (f : C_c(upperHalfPlane,ℝ)),
        Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G (fun n => (n:ℝ)) s w n
          (levelMassTimes t j) ω) atTop (𝓝 (∫ z, f z ∂ν j ω))) ∧
      P.bind (ν 0) = initialGreenMeasure κ ∧
      ∀ j (E : Set Ω),
        MeasurableSet[Filtration.natural B (fun r =>
          (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)).stronglyMeasurable) (t j)] E →
        (P.restrict E).bind (ν 0) = (P.restrict E).bind (ν (j+1)) +
          (P.restrict E).bind (halfPlaneGreenMeasure κ B γ G (t j)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let u (n : ℕ) : ℝ := n
  have hu (n : ℕ) : 0 ≤ u n := Nat.cast_nonneg n
  have hmono : Monotone u := fun _ _ h => Nat.cast_le.mpr h
  have huLim : Tendsto u atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨s,w,ν,hw₀,hw₁,hνm,hν,hlim,hpair⟩ := exists_measurable_level_radon_limits_with_pairings
    hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth u hu (levelMassTimes t)
  refine ⟨s,w,ν,hw₀,hw₁,hνm,hν,hlim,?_,?_⟩
  · apply level_radon_terminal_mean hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
      u hu s w hw₀ hw₁ (ν 0) (hνm 0) (fun ω => (hν 0 ω).1)
    · filter_upwards [hlim] with ω hω
      simpa only [levelMassTimes_zero] using hω 0
    · intro k
      simpa only [one_mul,levelMassTimes_zero] using hpair 0 k (fun _ => 1) (memLp_const 1)
  · intro j E hE
    let v (i : Fin 2) := if i = 0 then ν (j+1) else ν 0
    have hvm (i : Fin 2) : Measurable (v i) := by
      dsimp only [v]; split_ifs <;> exact hνm _
    have hvr (i : Fin 2) (ω : Ω) : (v i ω).Regular ∧ IsFiniteMeasureOnCompacts (v i ω) := by
      dsimp only [v]; split_ifs <;> exact hν _ ω
    have hvl (i : Fin 2) : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
        Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n
          (if i = 0 then (t j : ℝ≥0∞) else ∞) ω) atTop (𝓝 (∫ z, f z ∂v i ω)) := by
      filter_upwards [hlim] with ω hω
      by_cases hi : i = 0
      · simpa only [v,ite_eq_left hi,levelMassTimes_succ] using hω (j+1)
      · simpa only [v,ite_eq_right hi,levelMassTimes_zero] using hω 0
    have hvp (i : Fin 2) (k : ℕ) (a : Ω → ℝ) (ha : MemLp a 2 P) :
        Tendsto (fun n => ∫ ω, a ω * (∫ z, (localTestFamily upperHalfPlane).test k z
          ∂convexLevelMeasure κ B γ G u s w n (if i = 0 then (t j : ℝ≥0∞) else ∞) ω) ∂P)
          atTop (𝓝 (∫ ω, a ω * (∫ z, (localTestFamily upperHalfPlane).test k z ∂v i ω) ∂P)) := by
      by_cases hi : i = 0
      · simpa only [v,ite_eq_left hi,levelMassTimes_succ] using hpair (j+1) k a ha
      · simpa only [v,ite_eq_right hi,levelMassTimes_zero] using hpair 0 k a ha
    have hk := level_radon_conditional_kernel hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
      u hu hmono huLim s w hw₀ hw₁ (t j) v hvm hvr hvl hvp E hE
    simpa [v] using hk

end SLEExactGauge.Multipoint

end

end OAI

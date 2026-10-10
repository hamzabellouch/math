import OAI.Probability.SLE.Mass.WeightedLevelMoments
import OAI.Probability.SLE.Multipoint.NearDiagonalKernel

namespace OAI

/-! Weighted two-point control of the actual limiting Radon measure.
Finite spatial cutoff sums are bounded by the near-diagonal kernel. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

theorem level_radon_limit_test_moment_le_cappedKernel
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (t : ℝ≥0∞) (ν : Ω → Measure upperHalfPlane)
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)
        atTop (𝓝 (∫ z, f z ∂ν ω)))
    (K : Set ℂ) (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane)
    (b : ℝ) (hb : 0 < b) (hbR : ∀ z ∈ K, b ≤ 2*z.im)
    (f : C_c(upperHalfPlane,ℝ)) (hf : ∀ z, 0 ≤ f z)
    (hz : ∀ z ∉ K, extendHalfPlaneTest f z = 0) (m : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (∫ z, f z ∂ν ω)^m ∂P) ≤
      ENNReal.ofReal (multipointConstant κ m) *
        ∫⁻ z : Fin m → ℂ, (∏ i, ENNReal.ofReal (extendHalfPlaneTest f (z i))) *
          cappedDistanceKernel (codimension κ) b z
          ∂Measure.pi (fun _ : Fin m => volume.restrict K) := by
  apply level_radon_limit_test_moment_le hm hBc hκ hκ8 γ G F hw u hu s w hw₀ hw₁
    t ν hlim f hf m
  intro n
  simp_rw [ofReal_integral_halfPlaneLevelMeasure hκ hκ8 γ G F _ (hBc _) (hw _) (u n) t f hf]
  exact levelApproximationTest_moment_le_cappedKernel hB hm hBm hBc hB0 hκ hκ8 γ G F hw
    hgrowth K hK hKH (fun z => ENNReal.ofReal (extendHalfPlaneTest f z))
    (extendHalfPlaneTest_measurable f f.continuous.measurable).ennreal_ofReal
    (fun z hzK => by rw [hz z hzK,ENNReal.ofReal_zero]) b hb hbR m (u n) (hu n) t

theorem level_radon_cutoff_square_sum_le
    {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (hw₀ : ∀ n i, i ∈ s n → 0 ≤ w n i) (hw₁ : ∀ n, ∑ i ∈ s n, w n i = 1)
    (t : ℝ≥0∞) (ν : Ω → Measure upperHalfPlane) (hνm : Measurable ν)
    (hν : ∀ ω, IsFiniteMeasureOnCompacts (ν ω))
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)
        atTop (𝓝 (∫ z, f z ∂ν ω)))
    (K : Set ℂ) (hK : MeasurableSet K) (hKH : K ⊆ upperHalfPlane)
    (b : ℝ) (hb : 0 < b) (hbR : ∀ z ∈ K, b ≤ 2*z.im)
    (I : Finset ι) (f : ι → C_c(upperHalfPlane,ℝ)) (hf : ∀ i z, 0 ≤ f i z)
    (hz : ∀ i z, z ∉ K → extendHalfPlaneTest (f i) z = 0)
    (r : ℝ) (N : ℝ≥0∞)
    (hoverlap : ∀ x y, (∑ i ∈ I, ENNReal.ofReal (extendHalfPlaneTest (f i) x) *
      ENNReal.ofReal (extendHalfPlaneTest (f i) y)) ≤ if dist x y ≤ r then N else 0) :
    (∫⁻ ω, ∑ i ∈ I, ENNReal.ofReal (∫ z, f i z ∂ν ω)^2 ∂P) ≤
      ENNReal.ofReal (multipointConstant κ 2) * (N *
        ∫⁻ z : Fin 2 → ℂ, nearDiagonalKernel (codimension κ) b r z
          ∂Measure.pi (fun _ : Fin 2 => volume.restrict K)) := by
  have hfm (i : ι) : Measurable (fun ω => ENNReal.ofReal (∫ z, f i z ∂ν ω)) := by
    have he (ω : Ω) : ENNReal.ofReal (∫ z, f i z ∂ν ω) =
        ∫⁻ z, ENNReal.ofReal (f i z) ∂ν ω := by
      let := hν ω
      exact ofReal_integral_eq_lintegral_ofReal (f i).integrable (Eventually.of_forall (hf i))
    simp_rw [he]
    exact (Measure.measurable_lintegral (f i).continuous.measurable.ennreal_ofReal).comp hνm
  rw [lintegral_finsetSum I (f := fun i ω => ENNReal.ofReal (∫ z, f i z ∂ν ω)^2)
    (fun i _ => (hfm i).pow_const 2)]
  apply (Finset.sum_le_sum (fun i _ => level_radon_limit_test_moment_le_cappedKernel
    hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth u hu s w hw₀ hw₁ t ν hlim K hK hKH
    b hb hbR (f i) (hf i) (hz i) 2)).trans
  rw [← Finset.mul_sum]
  exact mul_le_mul' le_rfl (sum_weighted_pair_kernel_le I
    (fun i z => ENNReal.ofReal (extendHalfPlaneTest (f i) z))
    (fun i _ => (extendHalfPlaneTest_measurable (f i) (f i).continuous.measurable).ennreal_ofReal)
    (codimension κ) b r N hoverlap K)

end SLEExactGauge.Multipoint

end

end OAI

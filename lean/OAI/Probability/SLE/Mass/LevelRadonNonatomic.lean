import OAI.Probability.SLE.Mass.LevelRadonTwoPoint
import OAI.Probability.SLE.Mass.MassGridCutoffs
import OAI.Probability.SLE.Gauge.ShrinkingCoverAtoms

namespace OAI

/-! Nonatomicity of every actual convex Radon limit, from the two-point
bound and one deterministic family of shrinking grid cutoffs. -/

noncomputable section
open Set Metric Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge.Multipoint

local instance : LocallyCompactSpace upperHalfPlane := isOpen_upperHalfPlane.locallyCompactSpace

theorem level_radon_limit_compact_null_singletons
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
    (t : ℝ≥0∞) (ν : Ω → Measure upperHalfPlane) (hνm : Measurable ν)
    (hν : ∀ ω, IsFiniteMeasureOnCompacts (ν ω))
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)
        atTop (𝓝 (∫ z, f z ∂ν ω)))
    (K : Set upperHalfPlane) (hK : IsCompact K) :
    ∀ᵐ ω ∂P, ∀ x ∈ K, ν ω {x}=0 := by
  obtain ⟨χ,hχ,hχK⟩ := exists_unit_compact_test_cutoff K hK
  let L := (Subtype.val : upperHalfPlane → ℂ) '' tsupport χ
  have hL : IsCompact L := χ.hasCompactSupport.image continuous_subtype_val
  have hLH : L ⊆ upperHalfPlane := by rintro _ ⟨x,_,rfl⟩; exact x.property
  obtain ⟨b,hb,hbL⟩ := compact_positive_radius_cap hL hLH
  have hKI := hK.image (continuous_subtype_val : Continuous (Subtype.val : upperHalfPlane → ℂ))
  obtain ⟨R,hR,hRK⟩ := hKI.isBounded.exists_pos_norm_le
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let I (n : ℕ) := coverGridIndex R (r n)
  let f (n : ℕ) (i : ℤ×ℤ) := massGridCutoff χ (r n) i
  have hf (n : ℕ) (i : ℤ×ℤ) (z : upperHalfPlane) : 0 ≤ f n i z :=
    (massGridCutoff_bounds χ hχ (r n) i z).1
  let A (n : ℕ) (ω : Ω) := ∑ i ∈ I n, ENNReal.ofReal (∫ z, f n i z ∂ν ω)^2
  have hA (n : ℕ) : Measurable (A n) := by
    apply Finset.measurable_sum
    intro i hi
    have he (ω : Ω) : ENNReal.ofReal (∫ z, f n i z ∂ν ω) =
        ∫⁻ z, ENNReal.ofReal (f n i z) ∂ν ω := by
      let := hν ω
      exact ofReal_integral_eq_lintegral_ofReal (f n i).integrable (Eventually.of_forall (hf n i))
    simp_rw [he]
    exact ((Measure.measurable_lintegral (f n i).continuous.measurable.ennreal_ofReal).comp hνm).pow_const 2
  apply ae_null_singletons_on_of_square_bounds P ν K A hA
  · intro ω x hx n
    have hxR : (x:ℂ) ∈ closedBall (0:ℂ) R := by
      simpa only [mem_closedBall,dist_zero_right] using hRK x ⟨x,hx,rfl⟩
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (coverGrid_covers_disk hR.le (hr n) hxR)
    have hfx : f n i x = 1 := massGridCutoff_eq_one χ (hr n) i x (hχK x hx) hxi
    let := hν ω
    have hμ : ν ω {x} ≤ ENNReal.ofReal (∫ z, f n i z ∂ν ω) :=
      measure_compact_le_nonneg_test (ν ω) {x} isCompact_singleton (f n i) (hf n i)
        (by intro z hz; simpa only [mem_singleton_iff.mp hz,hfx] using (le_refl (1:ℝ)))
    exact (pow_le_pow_left' hμ 2).trans
      (Finset.single_le_sum (f := fun j => ENNReal.ofReal (∫ z, f n j z ∂ν ω)^2)
        (fun _ _ => zero_le) hi)
  · have hbound (n : ℕ) : (∫⁻ ω, A n ω ∂P) ≤
        ENNReal.ofReal (multipointConstant κ 2) * (81 *
          ∫⁻ z : Fin 2 → ℂ, nearDiagonalKernel (codimension κ) b (6*r n) z
            ∂Measure.pi (fun _ : Fin 2 => volume.restrict L)) := by
      exact level_radon_cutoff_square_sum_le hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
        u hu s w hw₀ hw₁ t ν hνm hν hlim L hL.measurableSet hLH b hb hbL (I n) (f n)
        (hf n) (fun i z hz => massGridCutoff_common_support χ (r n) i z hz)
        (6*r n) 81 (massGridCutoff_sum_bound χ hχ (hr n) (I n))
    have hr0 : Tendsto (fun n => 6*r n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 6
    have hnear := nearDiagonalKernel_integral_tendsto_zero (codimension_pos κ hκ8)
      (by unfold codimension dimension; linarith) b L hL.isBounded (fun n => 6*r n) hr0
    have hupper : Tendsto (fun n => ENNReal.ofReal (multipointConstant κ 2) * (81 *
          ∫⁻ z : Fin 2 → ℂ, nearDiagonalKernel (codimension κ) b (6*r n) z
            ∂Measure.pi (fun _ : Fin 2 => volume.restrict L))) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul
        (ENNReal.Tendsto.const_mul hnear (Or.inr (by norm_num : (81:ℝ≥0∞)≠⊤)))
        (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => zero_le) hbound

theorem level_radon_limit_nonatomic
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
    (t : ℝ≥0∞) (ν : Ω → Measure upperHalfPlane) (hνm : Measurable ν)
    (hν : ∀ ω, IsFiniteMeasureOnCompacts (ν ω))
    (hlim : ∀ᵐ ω ∂P, ∀ f : C_c(upperHalfPlane,ℝ),
      Tendsto (fun n => ∫ z, f z ∂convexLevelMeasure κ B γ G u s w n t ω)
        atTop (𝓝 (∫ z, f z ∂ν ω))) :
    ∀ᵐ ω ∂P, NullSingletonClass (ν ω) := by
  let D := localTestFamily upperHalfPlane
  apply ae_nullSingletonClass_of_exhaustion P ν D.compactSet
  · intro x
    obtain ⟨j,hj⟩ := D.exhaustive {x} isCompact_singleton
    exact ⟨j,hj (mem_singleton x)⟩
  · intro j
    exact level_radon_limit_compact_null_singletons hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth
      u hu s w hw₀ hw₁ t ν hνm hν hlim (D.compactSet j) (D.isCompact j)

end SLEExactGauge.Multipoint

end

end OAI

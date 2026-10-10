import OAI.Geometry.RCD.Sobolev.BochnerMixedTerm
import OAI.Geometry.RCD.Sobolev.GammaL2Bound

namespace OAI

/-! # Mixed integration by parts with an arbitrary L2 source

Bounded Sobolev recovery converges strongly. With one bounded-gradient
factor, both remaining products are L² pairings, so the product identity
passes to an unbounded Sobolev Laplacian.
-/

open Set Filter MeasureTheory
open scoped NNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

private theorem mixed_bounded_source_test (f w b : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (A C : ℝ≥0)
    (hb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ b x| ≤ A)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x| ≤ C)
    (hΔ : IsWeakLaplacian μ hQ f d) :
    weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f b +
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ b) f w =
        -(∫ x, SobolevSpace.toLp μ hQ w x * d x * SobolevSpace.toLp μ hQ b x ∂μ) := by
  have hbn : ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ b x‖ ≤ (A : ℝ) := by
    simpa only [Real.norm_eq_abs] using hb
  have hwn : ∀ᵐ x ∂μ, ‖SobolevSpace.toLp μ hQ w x‖ ≤ (C : ℝ) := by
    simpa only [Real.norm_eq_abs] using hw
  have hi₁ := (localGamma_memL1 μ hQ f b).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ w)) hwn
  have hi₂ := (localGamma_memL1 μ hQ f w).bdd_mul
    (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ b)) hbn
  have htest := hΔ (SobolevSpace.product μ hQ b w A C)
  have hleft : energyForm μ hQ f (SobolevSpace.product μ hQ b w A C) =
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f b +
        weightedGamma μ hQ (SobolevSpace.toLp μ hQ b) f w := by
    rw [← integral_localGamma_eq_energyForm]
    unfold weightedGamma
    rw [← integral_add hi₁ hi₂]
    apply integral_congr_ae
    filter_upwards [localGamma_product_right μ hQ f b w A C hb hw] with x hx
    rw [hx]
    ring
  have hright : inner ℝ d (SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ b w A C)) =
      ∫ x, SobolevSpace.toLp μ hQ w x * d x * SobolevSpace.toLp μ hQ b x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [SobolevSpace.product_coe μ hQ b w A C hb hw] with x hx
    simp only [Real.inner_apply, hx]
    ring
  rw [hleft, hright] at htest
  exact htest

theorem weakLaplacian_mixed_source_L2 (f b w : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (C L : ℝ≥0) (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x≤L)
    (hd : IsWeakLaplacian μ hQ f d) :
    weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f b+
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ b) f w =
      -(∫ x, SobolevSpace.toLp μ hQ w x*d x*SobolevSpace.toLp μ hQ b x ∂μ) := by
  let W := SobolevSpace.toLp μ hQ w
  let B := SobolevSpace.toLp μ hQ b
  have hwn : ∀ᵐ x ∂μ, ‖W x‖≤(C:ℝ) := by simpa only [Real.norm_eq_abs] using hw
  have hΓ := localGamma_memLp_of_bounded_gradient μ hQ f w L hf
  let Q := hΓ.toLp (localGamma μ hQ f w)
  have hT : MemLp (fun x => W x*d x) 2 μ := by
    apply ((Lp.memLp d).norm.const_mul (C:ℝ)).mono'
      ((Lp.aestronglyMeasurable W).mul (Lp.aestronglyMeasurable d))
    filter_upwards [hwn] with x hx
    change ‖W x*d x‖≤(C:ℝ)*‖d x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  let T := hT.toLp _
  have hpair (v : SobolevSpace μ hQ) :
      (∫ x, W x*d x*SobolevSpace.toLp μ hQ v x ∂μ)=inner ℝ (SobolevSpace.toLp μ hQ v) T := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp] with x hx
    change T x = W x*d x at hx
    simp only [Real.inner_apply,hx]
    ring
  obtain ⟨bs,hbs,hbound⟩ := SobolevSpace.bounded_strong_recovery μ hQ b
  have heq (k : ℕ) : weightedGamma μ hQ W f (bs k)+
      inner ℝ (SobolevSpace.toLp μ hQ (bs k)) Q+
      inner ℝ (SobolevSpace.toLp μ hQ (bs k)) T=0 := by
    have hh := mixed_bounded_source_test μ hQ f w (bs k) d k C (hbound k) hw hd
    rw [weightedGamma_eq_L2_inner μ hQ f w hΓ,hpair] at hh
    linarith
  have h₁ : Tendsto (fun k => weightedGamma μ hQ W f (bs k)) atTop
      (𝓝 (weightedGamma μ hQ W f b)) :=
    (((weightedGammaCLM μ hQ (Lp.aestronglyMeasurable W) hwn) f).continuous.tendsto b).comp hbs
  have hlp := ((SobolevSpace.toLpCLM μ hQ).continuous.tendsto b).comp hbs
  have h₂ : Tendsto (fun k => inner ℝ (SobolevSpace.toLp μ hQ (bs k)) Q) atTop
      (𝓝 (inner ℝ B Q)) := hlp.inner tendsto_const_nhds
  have h₃ : Tendsto (fun k => inner ℝ (SobolevSpace.toLp μ hQ (bs k)) T) atTop
      (𝓝 (inner ℝ B T)) := hlp.inner tendsto_const_nhds
  have hz : weightedGamma μ hQ W f b+inner ℝ B Q+inner ℝ B T=0 :=
    tendsto_nhds_unique ((h₁.add h₂).add h₃)
      (tendsto_const_nhds.congr' (Eventually.of_forall fun k => (heq k).symm))
  rw [←weightedGamma_eq_L2_inner μ hQ f w hΓ,←hpair b] at hz
  linarith

/-- An L² source can be replaced by a Sobolev representative only near
the test support. No amplitude bound on that representative is needed. -/
theorem weakLaplacian_local_mixed_source_L2 {Ω : Set X} (hΩ : MeasurableSet Ω)
    (f b w : SobolevSpace μ hQ) (d e : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ f d)
    (he : e =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ b)
    (C L : ℝ≥0)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C)
    (hf : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ f x≤L)
    (q : X → ℝ) (hwr : SobolevSpace.toLp μ hQ w =ᵐ[μ] q)
    (hq : tsupport q ⊆ Ω) :
    (∫ x, q x*d x*e x ∂μ)+weightedGamma μ hQ e f w =
      -(∫ x, q x*localGamma μ hQ f b x ∂μ) := by
  have hzero (x : X) (hx : x ∉ Ω) : q x=0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hx (hq hs))
  have he' := (ae_restrict_iff' hΩ).mp he
  have hsource : (∫ x, SobolevSpace.toLp μ hQ w x*d x*
      SobolevSpace.toLp μ hQ b x ∂μ) = ∫ x, q x*d x*e x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hwr,he'] with x hx hy
    rw [hx]
    by_cases hm : x ∈ Ω
    · rw [hy hm]
    · simp only [hzero x hm,zero_mul]
  have hweight : weightedGamma μ hQ e f w =
      weightedGamma μ hQ (SobolevSpace.toLp μ hQ b) f w := by
    unfold weightedGamma
    apply integral_congr_ae
    filter_upwards [he',hwr,localGamma_zero_on_level μ hQ w f 0,
      localGamma_comm μ hQ f w] with x hex hx hz hc
    by_cases hm : x ∈ Ω
    · rw [hex hm]
    · rw [hc,hz (hx.trans (hzero x hm)),mul_zero,mul_zero]
  have hpair : weightedGamma μ hQ (SobolevSpace.toLp μ hQ w) f b =
      ∫ x, q x*localGamma μ hQ f b x ∂μ := by
    exact integral_congr_ae (hwr.mono fun x hx =>
      congrArg (fun z => z*localGamma μ hQ f b x) hx)
  have ht := weakLaplacian_mixed_source_L2 μ hQ f b w d C L hw hf hd
  rw [hsource,hpair,←hweight] at ht
  linarith only [ht]

end RegularPointCoordinates

end

end OAI

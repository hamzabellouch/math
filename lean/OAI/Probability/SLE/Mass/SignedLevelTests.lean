import OAI.Probability.SLE.Mass.LevelApproximationL2

namespace OAI

/-! Real compact tests of the actual level measures. Both signs are
controlled by the same compact moment estimate. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint

def levelApproximationRealTest {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0∞) (f : ℂ → ℝ) (ω : Ω) : ℝ :=
  ∫ z, f z ∂levelApproximation κ B γ G u t ω

lemma integrable_of_bounded_support (μ : Measure ℂ) (K : Set ℂ)
    (hK : MeasurableSet K) (hμK : μ K < ⊤) (f : ℂ → ℝ)
    (hfm : Measurable f) (C : ℝ) (hf : ∀ z ∈ K, ‖f z‖ ≤ C)
    (hz : ∀ z ∉ K, f z = 0) : Integrable f μ := by
  have hi : Integrable (K.indicator (fun _ : ℂ => C)) μ :=
    (integrableOn_const hμK.ne).integrable_indicator hK
  apply hi.mono' hfm.aestronglyMeasurable
  filter_upwards [] with z
  by_cases h : z ∈ K
  · simpa only [indicator_of_mem h] using hf z h
  · simp only [hz z h,norm_zero,indicator_of_notMem h,le_refl]

lemma levelApproximationRealTest_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ u : ℝ) (hu : 0 ≤ u)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (t : ℝ≥0∞) (f : ℂ → ℝ) (hfm : Measurable f) :
    Measurable (levelApproximationRealTest κ B γ G u t f) := by
  have hd := levelApproximationDensity_joint_measurable hm hBc κ u hu γ G F hw t
  have he (ω : Ω) : levelApproximationRealTest κ B γ G u t f ω =
      ∫ z, (levelApproximationDensity κ B γ G u t ω z).toReal * f z := by
    apply integral_withDensity_eq_integral_toReal_smul hd.of_uncurry_left
    filter_upwards [] with z
    unfold levelApproximationDensity
    split_ifs <;> simp
  simp_rw [show levelApproximationRealTest κ B γ G u t f =
    (fun ω => ∫ z, (levelApproximationDensity κ B γ G u t ω z).toReal * f z)
    from funext he]
  exact (hd.ennreal_toReal.mul (hfm.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

lemma levelApproximationRealTest_eq_parts
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (u : ℝ) (t : ℝ≥0∞) (f : ℂ → ℝ) (ω : Ω)
    (K : Set ℂ) (hK : MeasurableSet K) (hM : levelMass κ B γ G u K ω < ⊤)
    (hfm : Measurable f) (C : ℝ) (hf : ∀ z ∈ K, ‖f z‖ ≤ C)
    (hz : ∀ z ∉ K, f z = 0) :
    levelApproximationRealTest κ B γ G u t f ω =
      (levelApproximationTest κ B γ G u t (fun z => ENNReal.ofReal (f z)) ω).toReal -
      (levelApproximationTest κ B γ G u t (fun z => ENNReal.ofReal (-f z)) ω).toReal := by
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    (integrable_of_bounded_support _ K hK
      ((levelApproximation_apply_le κ B γ G u t ω hK).trans_lt hM) f hfm C hf hz)

theorem levelMass_ae_finite
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (u : ℝ) (hu : 0 ≤ u) : ∀ᵐ ω ∂P, levelMass κ B γ G u K ω < ⊤ := by
  obtain ⟨M,hM,hbound⟩ := uniform_levelMass_compact_moments hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth K hK hKH 1
  apply ae_lt_top (levelMass_measurable hm hBc κ u hu γ G F hw K)
  exact (lt_of_le_of_lt (by simpa only [pow_one] using hbound u hu) hM).ne

theorem uniform_signed_levelTest_L2
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hBm : Measurable (Function.uncurry B))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth)
    (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ upperHalfPlane)
    (f : ℂ → ℝ) (hfm : Measurable f) (C : ℝ) (hf : ∀ z ∈ K, ‖f z‖ ≤ C)
    (hz : ∀ z ∉ K, f z = 0) :
    (∀ u : ℝ, 0 ≤ u → ∀ t : ℝ≥0∞, MemLp (levelApproximationRealTest κ B γ G u t f) 2 P) ∧
      ∃ D : ℝ, ∀ u : ℝ, ∀ _hu : 0 ≤ u, ∀ t : ℝ≥0∞,
        ∀ hp : MemLp (levelApproximationRealTest κ B γ G u t f) 2 P,
          ‖hp.toLp (levelApproximationRealTest κ B γ G u t f)‖ ≤ D := by
  let fp : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (f z)
  let fn : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (-f z)
  have hfp (z : ℂ) (hzK : z ∈ K) : fp z ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hf z hzK))
  have hfn (z : ℂ) (hzK : z ∈ K) : fn z ≤ ENNReal.ofReal C :=
    ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hf z hzK))
  obtain ⟨Mp,hMp,hpb⟩ := uniform_levelApproximationTest_moments hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth K hK hKH fp (ENNReal.ofReal C) ENNReal.ofReal_lt_top hfp
    (fun z hzK => by simp only [fp,hz z hzK,ENNReal.ofReal_zero]) 2
  obtain ⟨Mn,hMn,hnb⟩ := uniform_levelApproximationTest_moments hB hm hBm hBc hB0 hκ hκ8
    γ G F hw hgrowth K hK hKH fn (ENNReal.ofReal C) ENNReal.ofReal_lt_top hfn
    (fun z hzK => by simp only [fn,hz z hzK,neg_zero,ENNReal.ofReal_zero]) 2
  have hpm (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0∞) :=
    levelApproximationTest_measurable hm hBc κ u hu γ G F hw t fp hfm.ennreal_ofReal
  have hnm (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0∞) :=
    levelApproximationTest_measurable hm hBc κ u hu γ G F hw t fn hfm.neg.ennreal_ofReal
  have hpLp (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0∞) :=
    memLp_toReal_two P _ (hpm u hu t) Mp hMp (hpb u hu t)
  have hnLp (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0∞) :=
    memLp_toReal_two P _ (hnm u hu t) Mn hMn (hnb u hu t)
  have he (u : ℝ) (hu : 0 ≤ u) (t : ℝ≥0∞) : levelApproximationRealTest κ B γ G u t f =ᵐ[P]
      fun ω => (levelApproximationTest κ B γ G u t fp ω).toReal -
        (levelApproximationTest κ B γ G u t fn ω).toReal := by
    filter_upwards [levelMass_ae_finite hB hm hBm hBc hB0 hκ hκ8 γ G F hw hgrowth K hK hKH u hu]
      with ω hω
    exact levelApproximationRealTest_eq_parts κ B γ G u t f ω K hK.measurableSet hω hfm C hf hz
  refine ⟨fun u hu t => MemLp.ae_eq (he u hu t).symm ((hpLp u hu t).sub (hnLp u hu t)),
    ⟨(Mp ^ (1/2 : ℝ)).toReal + (Mn ^ (1/2 : ℝ)).toReal, ?_⟩⟩
  intro u hu t hp
  have hclass : hp.toLp (levelApproximationRealTest κ B γ G u t f) =
      (hpLp u hu t).toLp _ - (hnLp u hu t).toLp _ := by
    apply Lp.ext
    filter_upwards [hp.coeFn_toLp, (hpLp u hu t).coeFn_toLp,
      (hnLp u hu t).coeFn_toLp,Lp.coeFn_sub ((hpLp u hu t).toLp _) ((hnLp u hu t).toLp _),
      he u hu t] with ω h₁ h₂ h₃ h₄ h₅
    rw [h₁,h₄,Pi.sub_apply,h₂,h₃,h₅]
  rw [hclass]
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_toLp_toReal_two_le P _ (hpm u hu t) Mp hMp (hpb u hu t) (hpLp u hu t))
    (norm_toLp_toReal_two_le P _ (hnm u hu t) Mn hMn (hnb u hu t) (hnLp u hu t)))

end SLEExactGauge.Multipoint

end

end OAI

import OAI.Probability.SLE.Mass.ConformalMassTransport
import OAI.Probability.SLE.RetainedSeedMoments

namespace OAI

/-! Exact area and measure transport for positive real dilations of the
half-plane. These are the spatial factors in capacity scaling. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge

lemma source_scale_area_lintegral (c : ℝ≥0) (hc : 0 < c)
    (f : ℂ → ℝ≥0∞) (K : Set ℂ) :
    (∫⁻ z in (fun z : ℂ => (c:ℂ)*z) '' K, f z) =
      ENNReal.ofReal ((c:ℝ)^2) * ∫⁻ z in K, f ((c:ℂ)*z) := by
  have hcR : 0 < (c:ℝ) := hc
  have hcC : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let e := Homeomorph.mulLeft₀ (c:ℂ) hcC
  have hvol (s : Set ℂ) : volume (e ⁻¹' s)=
      ENNReal.ofReal (((c:ℝ)^2)⁻¹)*volume s := by
    change volume ((fun z : ℂ => (c:ℂ)*z) ⁻¹' s)=_
    simpa only [Complex.real_smul,smul_eq_mul,Complex.finrank_real_complex,
      abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (c:ℝ)))] using
      (volume : Measure ℂ).addHaar_preimage_smul hcR.ne' s
  have hp : MeasurePreserving e (ENNReal.ofReal ((c:ℝ)^2) • (volume : Measure ℂ)) volume := by
    refine ⟨e.continuous.measurable,?_⟩
    apply Measure.ext
    intro s hs
    rw [e.measurableEmbedding.map_apply,Measure.smul_apply,smul_eq_mul,hvol,← mul_assoc,
      ← ENNReal.ofReal_mul (sq_nonneg (c:ℝ)),mul_inv_cancel₀ (pow_ne_zero 2 hcR.ne'),
      ENNReal.ofReal_one,one_mul]
  have h := hp.setLIntegral_comp_emb e.measurableEmbedding f K
  rw [Measure.restrict_smul,lintegral_smul_measure] at h
  exact h.symm

def halfPlaneDilation (c : ℝ≥0) (hc : 0 < c) : upperHalfPlane ≃ₜ upperHalfPlane where
  toFun z := ⟨(c:ℂ)*(z:ℂ),by
    change 0 < ((c:ℂ)*(z:ℂ)).im
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      using mul_pos (show 0 < (c:ℝ) from hc) z.property⟩
  invFun z := ⟨(c:ℂ)⁻¹*(z:ℂ),by
    change 0 < ((c:ℂ)⁻¹*(z:ℂ)).im
    rw [← Complex.ofReal_inv]
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      using mul_pos (inv_pos.mpr (show 0 < (c:ℝ) from hc)) z.property⟩
  left_inv z := by
    apply Subtype.ext
    change (c:ℂ)⁻¹*((c:ℂ)*(z:ℂ))=(z:ℂ)
    exact inv_mul_cancel_left₀ (by exact_mod_cast hc.ne') _
  right_inv z := by
    apply Subtype.ext
    change (c:ℂ)*((c:ℂ)⁻¹*(z:ℂ))=(z:ℂ)
    exact mul_inv_cancel_left₀ (by exact_mod_cast hc.ne') _
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] lemma halfPlaneDilation_apply (c : ℝ≥0) (hc : 0 < c) (z : upperHalfPlane) :
    ((halfPlaneDilation c hc z : upperHalfPlane):ℂ)=(c:ℂ)*(z:ℂ) := rfl

namespace Multipoint

def dilationMass (κ : ℝ) (c : ℝ≥0) (hc : 0 < c) (μ : Measure upperHalfPlane) :
    Measure upperHalfPlane :=
  conformalMass (halfPlaneDilation c hc) (ContinuousMap.const _ (Real.toNNReal ((c:ℝ)^dimension κ))) μ

lemma dilationMass_apply (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (μ : Measure upperHalfPlane) (A : Set upperHalfPlane) (hA : MeasurableSet A) :
    dilationMass κ c hc μ A=ENNReal.ofReal ((c:ℝ)^dimension κ)*
      μ ((halfPlaneDilation c hc) ⁻¹' A) := by
  rw [dilationMass,conformalMass,Measure.map_apply (halfPlaneDilation c hc).continuous.measurable hA,
    withDensity_apply _ ((halfPlaneDilation c hc).continuous.measurable hA)]
  simp only [ContinuousMap.const_apply]
  change (∫⁻ _ in (halfPlaneDilation c hc) ⁻¹' A, ENNReal.ofReal ((c:ℝ)^dimension κ) ∂μ)=_
  exact setLIntegral_const _ _

lemma dilationMass_realDensity (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (ρ ρ' : ℂ → ℝ)
    (hρ : ∀ z ∈ upperHalfPlane, ρ' ((c:ℂ)*z)=(c:ℝ)^(-codimension κ)*ρ z) :
    (volume.withDensity (fun z => ENNReal.ofReal (ρ' z))).comap Subtype.val =
      dilationMass κ c hc ((volume.withDensity (fun z => ENNReal.ofReal (ρ z))).comap Subtype.val) := by
  let J := halfPlaneDilation c hc
  have hpos : 0 < (c:ℝ) := hc
  have hpower : ENNReal.ofReal ((c:ℝ)^2)*ENNReal.ofReal ((c:ℝ)^(-codimension κ))=
      ENNReal.ofReal ((c:ℝ)^dimension κ) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg _),← Real.rpow_natCast (c:ℝ) 2,
      ← Real.rpow_add hpos]
    have hexp : (2:ℝ)+ -codimension κ=dimension κ := by unfold codimension; ring
    norm_num only [Nat.cast_ofNat]
    rw [hexp]
  apply Measure.ext
  intro A hA
  have hpre : MeasurableSet (J ⁻¹' A) := J.continuous.measurable hA
  have hAI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hA
  have hKI := (MeasurableEmbedding.subtype_coe isOpen_upperHalfPlane.measurableSet).measurableSet_image.mpr hpre
  have himage : (fun z : ℂ => (c:ℂ)*z) '' ((Subtype.val : upperHalfPlane → ℂ) '' (J ⁻¹' A))=
      (Subtype.val : upperHalfPlane → ℂ) '' A := by
    ext z
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨J x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      refine ⟨(J.symm x:ℂ),⟨J.symm x,?_,rfl⟩,?_⟩
      · change J (J.symm x) ∈ A
        simpa only [J.apply_symm_apply] using hx
      · exact congrArg Subtype.val (J.apply_symm_apply x)
  rw [dilationMass_apply κ c hc _ A hA,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    comap_subtype_coe_apply isOpen_upperHalfPlane.measurableSet,
    withDensity_apply _ hAI,withDensity_apply _ hKI,← himage,
    source_scale_area_lintegral c hc]
  have hi : (∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' (J ⁻¹' A),
      ENNReal.ofReal (ρ' ((c:ℂ)*z))) =
      ∫⁻ z in (Subtype.val : upperHalfPlane → ℂ) '' (J ⁻¹' A),
        ENNReal.ofReal ((c:ℝ)^(-codimension κ))*ENNReal.ofReal (ρ z) := by
    apply setLIntegral_congr_fun hKI
    rintro z ⟨x,_hx,rfl⟩
    dsimp only
    rw [hρ x x.property,ENNReal.ofReal_mul (Real.rpow_nonneg c.coe_nonneg _)]
  rw [hi,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← mul_assoc,hpower]

lemma dilationMass_initialGreen (κ : ℝ) (c : ℝ≥0) (hc : 0 < c) :
    dilationMass κ c hc (initialGreenMeasure κ)=initialGreenMeasure κ := by
  exact (dilationMass_realDensity κ c hc (initialGreen κ) (initialGreen κ)
    (fun z hz => source_scale_initialGreen κ c hc z hz.le)).symm

lemma dilationMass_bind {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (μ : Ω → Measure upperHalfPlane) (hμ : Measurable μ) :
    P.bind (fun ω => dilationMass κ c hc (μ ω))=dilationMass κ c hc (P.bind μ) := by
  have hM : Measurable (fun ω => dilationMass κ c hc (μ ω)) :=
    (conformalMass_measurable _ _).comp hμ
  apply Measure.ext
  intro A hA
  have hpre : MeasurableSet ((halfPlaneDilation c hc) ⁻¹' A) :=
    (halfPlaneDilation c hc).continuous.measurable hA
  rw [Measure.bind_apply hA hM.aemeasurable,dilationMass_apply κ c hc _ A hA]
  simp_rw [dilationMass_apply κ c hc _ A hA]
  rw [Measure.bind_apply hpre hμ.aemeasurable,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma dilationMass_mono (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    {μ ν : Measure upperHalfPlane} (h : μ ≤ ν) :
    dilationMass κ c hc μ ≤ dilationMass κ c hc ν := conformalMass_mono _ _ h

lemma dilationMass_ne_zero_iff (κ : ℝ) (c : ℝ≥0) (hc : 0 < c)
    (μ : Measure upperHalfPlane) : dilationMass κ c hc μ ≠ 0 ↔ μ ≠ 0 := by
  rw [← Measure.measure_univ_pos,← Measure.measure_univ_pos,dilationMass_apply κ c hc _ univ MeasurableSet.univ]
  simp only [preimage_univ]
  constructor
  · intro h
    by_contra hn
    have hzero : μ univ=0 := le_antisymm (le_of_not_gt hn) bot_le
    simp only [hzero,mul_zero,lt_self_iff_false] at h
  · intro h
    exact pos_iff_ne_zero.mpr (mul_ne_zero
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hc _)).ne' h.ne')

end Multipoint
end SLEExactGauge

end

end OAI

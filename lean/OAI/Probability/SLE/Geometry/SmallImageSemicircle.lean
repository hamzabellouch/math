import OAI.Probability.SLE.DyadicStrips

namespace OAI

/-!
Angular Sobolev estimates for the small-image semicircle lemma
`es:good-semicircle`. In particular, the absolute continuity used below is
proved for the actual clipped conformal logarithm.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace SLEExactGauge.SmallImageSemicircle

lemma integral_abs_le_angular_energy {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioo 0 Real.pi))) :
    (∫ θ in Ioo 0 Real.pi, |g θ|) ≤
      Real.sqrt Real.pi * Real.sqrt (∫ θ in Ioo 0 Real.pi, (g θ) ^ 2) := by
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume.restrict (Ioo 0 Real.pi)) :=
    memLp_const 1
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ (fun θ => norm_nonneg (g θ))) (ae_of_all _ (fun _ => zero_le_one))
    (by simpa using hg.norm) (by simpa using h1)
  simpa only [mul_one, Real.rpow_two, one_pow, Real.norm_eq_abs, sq_abs,
    integral_const, smul_eq_mul, mul_one, one_mul, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ioo, sub_zero,
    ENNReal.toReal_ofReal Real.pi_pos.le, Real.sqrt_eq_rpow, mul_comm] using h

/-- A section which is absolutely continuous on compact subintervals has
oscillation controlled by its full angular derivative energy. -/
theorem angular_oscillation_bound {f : ℝ → ℝ} {x y : ℝ}
    (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi)
    (hf : AbsolutelyContinuousOnInterval f x y)
    (hderiv : MemLp (deriv f) 2 (volume.restrict (Ioo 0 Real.pi))) :
    |f y - f x| ≤ Real.sqrt Real.pi *
      Real.sqrt (∫ θ in Ioo 0 Real.pi, (deriv f θ) ^ 2) := by
  have hsub : uIoc x y ⊆ Ioo 0 Real.pi := by
    intro θ hθ
    have hθ' := uIoc_subset_uIcc hθ
    exact ordConnected_Ioo.uIcc_subset hx hy hθ'
  have hi : IntegrableOn (fun θ => |deriv f θ|) (Ioo 0 Real.pi) := by
    simpa only [IntegrableOn, Real.norm_eq_abs] using (hderiv.integrable (by norm_num)).norm
  calc
    |f y - f x| = ‖∫ θ in x..y, deriv f θ‖ := by
      rw [hf.integral_deriv_eq_sub, Real.norm_eq_abs]
    _ ≤ ∫ θ in uIoc x y, |deriv f θ| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm_uIoc (f := deriv f) (a := x) (b := y))
    _ ≤ ∫ θ in Ioo 0 Real.pi, |deriv f θ| :=
      setIntegral_mono_set hi (ae_of_all _ (fun θ => abs_nonneg (deriv f θ)))
        hsub.eventuallySubset
    _ ≤ _ := integral_abs_le_angular_energy hderiv

theorem anchored_angular_bound {f : ℝ → ℝ} {θ₀ : ℝ}
    (hθ₀ : θ₀ ∈ Ioo 0 Real.pi) (hzero : f θ₀ = 0)
    (hac : ∀ θ ∈ Ioo 0 Real.pi, AbsolutelyContinuousOnInterval f θ₀ θ)
    (hderiv : MemLp (deriv f) 2 (volume.restrict (Ioo 0 Real.pi))) :
    ∀ θ ∈ Ioo 0 Real.pi, |f θ| ≤ Real.sqrt Real.pi *
      Real.sqrt (∫ φ in Ioo 0 Real.pi, (deriv f φ) ^ 2) := by
  intro θ hθ
  simpa only [hzero, sub_zero] using angular_oscillation_bound hθ₀ hθ (hac θ hθ) hderiv

/-- The exact angular constant in the manuscript. -/
theorem anchored_angular_bound_of_energy {f : ℝ → ℝ} {θ₀ H : ℝ}
    (hH : 0 ≤ H) (hθ₀ : θ₀ ∈ Ioo 0 Real.pi) (hzero : f θ₀ = 0)
    (hac : ∀ θ ∈ Ioo 0 Real.pi, AbsolutelyContinuousOnInterval f θ₀ θ)
    (hderiv : MemLp (deriv f) 2 (volume.restrict (Ioo 0 Real.pi)))
    (henergy : (∫ φ in Ioo 0 Real.pi, (deriv f φ) ^ 2) ≤ 2 * Real.pi * H) :
    ∀ θ ∈ Ioo 0 Real.pi, f θ ≤ Real.pi * Real.sqrt (2 * H) := by
  intro θ hθ
  have h := anchored_angular_bound hθ₀ hzero hac hderiv θ hθ
  have hE : 0 ≤ ∫ φ in Ioo 0 Real.pi, (deriv f φ) ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hs := sq_le_sq₀ (abs_nonneg (f θ)) (by positivity) |>.mpr h
  rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hE] at hs
  have hr : (Real.pi * Real.sqrt (2 * H)) ^ 2 = Real.pi ^ 2 * (2 * H) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hsq : |f θ| ^ 2 ≤ (Real.pi * Real.sqrt (2 * H)) ^ 2 := by
    rw [hr]
    nlinarith [mul_le_mul_of_nonneg_left henergy Real.pi_pos.le]
  exact (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hsq)

def stripPoint (v θ : ℝ) : ℂ := (v : ℂ) + (θ : ℂ) * Complex.I

lemma stripPoint_mem {v θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi) :
    stripPoint v θ ∈ {z : ℂ | 0 < z.im ∧ z.im < Real.pi} := by
  simpa only [stripPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
    zero_add, Set.mem_ofPred_eq, Set.mem_Ioo] using hθ

/-- Compact angular sections of the actual conformal logarithm are
absolutely continuous. The omitted point removes the logarithmic singularity. -/
theorem conformal_section_absolutelyContinuous
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    {a : ℂ} (ha : ∀ z, 0 < z.im → F z ≠ a)
    {r : ℝ} (hr : 0 < r) (H v : ℝ) {x y : ℝ}
    (hx : x ∈ Ioo 0 Real.pi) (hy : y ∈ Ioo 0 Real.pi) :
    AbsolutelyContinuousOnInterval
      (fun θ => conformalStripLog F a r H (stripPoint v θ)) x y := by
  let g : ℝ → ℝ := fun θ => Real.log (‖F (Complex.exp (stripPoint v θ)) - a‖ / r)
  have hgd : ContDiffOn ℝ 1 g (uIcc x y) := by
    intro θ hθ
    have hθ' : θ ∈ Ioo 0 Real.pi := ordConnected_Ioo.uIcc_subset hx hy hθ
    have hz := exp_strip_halfplane (stripPoint_mem (v := v) hθ')
    have hFo : ContDiffAt ℝ 1 F (Complex.exp (stripPoint v θ)) :=
      ((hF.analyticAt (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hz)).restrictScalars
        (𝕜 := ℝ)).contDiffAt
    have hpt : ContDiffAt ℝ 1 (fun t => Complex.exp (stripPoint v t)) θ := by
      dsimp only [stripPoint]
      have hcast : ContDiffAt ℝ 1 (fun t : ℝ => (t : ℂ)) θ :=
        Complex.ofRealCLM.contDiff.contDiffAt
      fun_prop
    have hnonzero := sub_ne_zero.mpr (ha _ hz)
    exact ((((hFo.comp θ hpt).sub contDiffAt_const).norm ℝ hnonzero).div_const r).log
      (div_ne_zero (norm_ne_zero_iff.mpr hnonzero) hr.ne') |>.contDiffWithinAt
  obtain ⟨K, hK⟩ := hgd.exists_lipschitzOnWith (by norm_num) (convex_uIcc x y) isCompact_uIcc
  exact ((lipschitz_clip H).comp_lipschitzOnWith hK).absolutelyContinuousOnInterval

lemma angular_deriv_le_gradient {u : ℂ → ℝ} {v θ : ℝ}
    (hu : DifferentiableAt ℝ u (stripPoint v θ)) :
    |deriv (fun t => u (stripPoint v t)) θ| ≤ ‖gradient u (stripPoint v θ)‖ := by
  have hp : HasDerivAt (stripPoint v) Complex.I θ := by
    change HasDerivAt (fun t : ℝ => (v : ℂ) + (t : ℂ) * Complex.I) Complex.I θ
    simpa [stripPoint] using
      ((Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I).const_add (v : ℂ)
  change |deriv (u ∘ stripPoint v) θ| ≤ _
  rw [(hu.hasFDerivAt.comp_hasDerivAt θ hp).deriv, ← real_gradient_im]
  exact Complex.abs_im_le_norm _

/-- A unit logarithmic slab contains a section whose full angular energy
is at most the total strip energy. Differentiability is required only almost
everywhere, as supplied by the locally Lipschitz conformal logarithm. -/
theorem exists_section_of_strip_energy
    (u : ℂ → ℝ) (q : ℝ)
    (hg : MemLp (gradient u) 2
      (volume.restrict {z : ℂ | 0 < z.im ∧ z.im < Real.pi}))
    (hd : ∀ᵐ z ∂volume, z ∈ {z : ℂ | 0 < z.im ∧ z.im < Real.pi} →
      DifferentiableAt ℝ u z) :
    ∃ v ∈ Ioo q (q + 1),
      MemLp (deriv (fun θ => u (stripPoint v θ))) 2 (volume.restrict (Ioo 0 Real.pi)) ∧
      (∫ θ in Ioo 0 Real.pi, (deriv (fun t => u (stripPoint v t)) θ) ^ 2) ≤
        ∫ z in {z : ℂ | 0 < z.im ∧ z.im < Real.pi}, ‖gradient u z‖ ^ 2 := by
  let J := Ioo q (q + 1)
  let K := Ioo 0 Real.pi
  let S := {z : ℂ | 0 < z.im ∧ z.im < Real.pi}
  let T := {z : ℂ | q < z.re ∧ z.re < q + 1 ∧ 0 < z.im ∧ z.im < Real.pi}
  let e := Complex.measurableEquivRealProd.symm
  have he : MeasurePreserving e volume volume := Complex.volume_preserving_equiv_real_prod.symm _
  have hpre : e ⁻¹' T = J ×ˢ K := by
    ext z
    simp [e, T, J, K, and_assoc]
  have hTS : T ⊆ S := fun _ hz => hz.2.2
  have hiS : IntegrableOn (fun z => ‖gradient u z‖ ^ 2) S := hg.norm.integrable_sq
  have hiT := hiS.mono_set hTS
  have hip : Integrable (fun z : ℝ × ℝ => ‖gradient u (e z)‖ ^ 2)
      ((volume.restrict J).prod (volume.restrict K)) := by
    rw [Measure.prod_restrict]
    exact hpre ▸ (he.integrableOn_comp_preimage e.measurableEmbedding).mpr hiT
  have heq : (∫ v in J, ∫ θ in K, ‖gradient u (e (v, θ))‖ ^ 2) =
      ∫ z in T, ‖gradient u z‖ ^ 2 := by
    rw [← integral_prod _ hip, Measure.prod_restrict, ← hpre]
    simpa only [Measure.volume_eq_prod] using
      he.setIntegral_preimage_emb e.measurableEmbedding (fun z => ‖gradient u z‖ ^ 2) T
  have hep : (∫ v in J, ∫ θ in K, ‖gradient u (e (v, θ))‖ ^ 2) ≤
      ∫ z in S, ‖gradient u z‖ ^ 2 := by
    rw [heq]
    exact setIntegral_mono_set hiS (ae_of_all _ (fun _ => sq_nonneg _)) hTS.eventuallySubset
  have had : ∀ᵐ v ∂volume.restrict J, ∀ᵐ θ ∂volume.restrict K,
      DifferentiableAt ℝ u (e (v, θ)) := by
    have hdp : ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)), e z ∈ S → DifferentiableAt ℝ u (e z) :=
      ae_of_ae_map he.measurable.aemeasurable (he.map_eq.symm ▸ hd)
    have hdr := ae_restrict_of_ae (s := J ×ˢ K) hdp
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hdr
    filter_upwards [Measure.ae_ae_of_ae_prod hdr] with v hv
    filter_upwards [hv, ae_restrict_mem measurableSet_Ioo] with θ hθ hθK
    exact hθ hθK
  let energy (v : ℝ) := ∫ θ in K, ‖gradient u (e (v, θ))‖ ^ 2
  have hei : Integrable energy (volume.restrict J) := hip.integral_prod_left
  have hgood : ∀ᵐ v ∂volume.restrict J,
      v ∈ J ∧ Integrable (fun θ => ‖gradient u (e (v, θ))‖ ^ 2) (volume.restrict K) ∧
        ∀ᵐ θ ∂volume.restrict K, DifferentiableAt ℝ u (e (v, θ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hip.prod_right_ae, had] with v hv hi hdv
    exact ⟨hv, hi, hdv⟩
  have hprob : IsProbabilityMeasure (volume.restrict J) := by
    constructor
    simp [J, Real.volume_Ioo]
  let := hprob
  let Good (v : ℝ) := v ∈ J ∧
    Integrable (fun θ => ‖gradient u (e (v, θ))‖ ^ 2) (volume.restrict K) ∧
      ∀ᵐ θ ∂volume.restrict K, DifferentiableAt ℝ u (e (v, θ))
  have hnull : (volume.restrict J) {v | ¬ Good v} = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hgood] with v hv
    exact fun h => h hv
  obtain ⟨v, hv, hve⟩ := exists_notMem_null_le_integral hei hnull
  have hv' : Good v := not_not.mp hv
  obtain ⟨hvJ, hvI, hvD⟩ := hv'
  have hbound : ∀ᵐ θ ∂volume.restrict K,
      |deriv (fun t => u (stripPoint v t)) θ| ≤ ‖gradient u (e (v, θ))‖ := by
    filter_upwards [hvD] with θ hθ
    have hepoint : e (v, θ) = stripPoint v θ := by
      apply Complex.ext <;> simp [e, stripPoint]
    simpa only [hepoint] using angular_deriv_le_gradient (hepoint ▸ hθ)
  have hdi : Integrable (fun θ => (deriv (fun t => u (stripPoint v t)) θ) ^ 2)
      (volume.restrict K) := by
    apply hvI.mono' ((aestronglyMeasurable_deriv _ _).pow 2)
    filter_upwards [hbound] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs, Pi.pow_apply] using
      (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hθ
  refine ⟨v, hvJ, ?_, ?_⟩
  · exact (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_deriv _ _)).mpr
      (by simpa only [Real.norm_eq_abs, sq_abs] using hdi)
  · apply (integral_mono_ae hdi hvI ?_).trans (hve.trans hep)
    filter_upwards [hbound] with θ hθ
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hθ

/-- The guide crosses every smaller semicircle, supplying the anchor required
by the angular Sobolev estimate. -/
theorem access_segment_section_anchor
    {F : ℂ → ℂ} {a : ℂ} {r t₀ : ℝ} {β : ℝ → ℂ}
    (ht₀ : 0 < t₀) (hβ : ContinuousOn β (Icc 0 t₀)) (hβ₀ : β 0 = 0)
    (hβH : ∀ t ∈ Ioc 0 t₀, 0 < (β t).im)
    (hsmall : ∀ t ∈ Ioc 0 t₀, ‖F (β t) - a‖ ≤ r)
    {v : ℝ} (hv : v < Real.log ‖β t₀‖) :
    ∃ θ ∈ Ioo 0 Real.pi, ‖F (Complex.exp (stripPoint v θ)) - a‖ ≤ r := by
  have hbH := hβH t₀ ⟨ht₀, le_rfl⟩
  have hbne : β t₀ ≠ 0 := by intro h; simp [h] at hbH
  have hbpos : 0 < ‖β t₀‖ := norm_pos_iff.mpr hbne
  have hB : Real.exp v < ‖β t₀‖ := by
    simpa only [Real.exp_log hbpos] using Real.exp_lt_exp.mpr hv
  obtain ⟨t, ht, htnorm⟩ := intermediate_value_Icc ht₀.le hβ.norm
    (show Real.exp v ∈ Icc ‖β 0‖ ‖β t₀‖ by
      simpa only [hβ₀, norm_zero, Set.mem_Icc] using And.intro (Real.exp_pos v).le hB.le)
  change ‖β t‖ = Real.exp v at htnorm
  have htpos : 0 < t := by
    by_contra hn
    have heq : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
    rw [heq, hβ₀, norm_zero] at htnorm
    exact (Real.exp_pos v).ne' htnorm.symm
  have htH := hβH t ⟨htpos, ht.2⟩
  have htne : β t ≠ 0 := by intro h; simp [h] at htH
  have harg : (β t).arg ∈ Ioo 0 Real.pi := by
    refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr htH.le) ?_,
      Complex.arg_lt_pi_iff.mpr (Or.inr htH.ne')⟩
    intro heq
    exact htH.ne' (Complex.arg_eq_zero_iff.mp heq.symm).2
  have hlog : Complex.log (β t) = stripPoint v (β t).arg := by
    apply Complex.ext <;> simp [stripPoint, Complex.log_re, Complex.log_im, htnorm]
  refine ⟨(β t).arg, harg, ?_⟩
  rw [← hlog, Complex.exp_log htne]
  exact hsmall t ⟨htpos, ht.2⟩

/-- The exact semicircle estimate before writing the base radius as
`r * exp (-A)`. The section anchor is a direct consequence of an access guide,
as proved above. -/
theorem exists_small_image_semicircle_of_anchors
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hi : InjOn F {z | 0 < z.im}) {a : ℂ}
    (ha : ∀ z, 0 < z.im → F z ≠ a) {r A q : ℝ}
    (hr : 0 < r) (hA : 2 * Real.pi ^ 2 < A)
    (hanchor : ∀ v ∈ Ioo q (q + 1),
      ∃ θ ∈ Ioo 0 Real.pi, ‖F (Complex.exp (stripPoint v θ)) - a‖ ≤ r) :
    ∃ B ∈ Ioo (Real.exp q) (Real.exp (q + 1)),
      ∀ θ ∈ Ioo 0 Real.pi,
        ‖F ((B : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - a‖ ≤
          r * Real.exp (Real.pi * Real.sqrt (2 * A)) := by
  have hApos : 0 < A := (by positivity : 0 < 2 * Real.pi ^ 2).trans hA
  let u := conformalStripLog F a r A
  have hD : IsOpen {z : ℂ | 0 < z.im ∧ z.im < Real.pi} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hcomp : DifferentiableOn ℂ (F ∘ Complex.exp)
      {z : ℂ | 0 < z.im ∧ z.im < Real.pi} :=
    hF.comp Complex.differentiable_exp.differentiableOn exp_strip_halfplane
  have hd : ∀ᵐ z ∂volume, z ∈ {z : ℂ | 0 < z.im ∧ z.im < Real.pi} →
      DifferentiableAt ℝ u z :=
    truncated_log_ae_differentiable hD hcomp a r A hr hApos
  obtain ⟨hg, he, -⟩ := conformal_strip_total_energy hF hi a r A hr hApos
  obtain ⟨v, hv, hvd, hve⟩ := exists_section_of_strip_energy u q hg hd
  obtain ⟨θ₀, hθ₀, hzero⟩ := hanchor v hv
  have hz : u (stripPoint v θ₀) = 0 :=
    truncatedConformalLog_eq_zero (F := F ∘ Complex.exp) hr hApos.le hzero
  have hbound := anchored_angular_bound_of_energy hApos.le hθ₀ hz
    (fun θ hθ => conformal_section_absolutelyContinuous hF ha hr A v hθ₀ hθ)
    hvd (hve.trans he)
  have hstrict : Real.pi * Real.sqrt (2 * A) < A := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * A by positivity)
    have hsq : (Real.pi * Real.sqrt (2 * A)) ^ 2 < A ^ 2 := by
      rw [mul_pow, hs]
      nlinarith [mul_lt_mul_of_pos_right hA hApos]
    exact (sq_lt_sq₀ (by positivity) hApos.le).mp hsq
  refine ⟨Real.exp v, ⟨Real.exp_lt_exp.mpr hv.1, Real.exp_lt_exp.mpr hv.2⟩, ?_⟩
  intro θ hθ
  have hb := hbound θ hθ
  have hlog : Real.log (‖F (Complex.exp (stripPoint v θ)) - a‖ / r) ≤
      Real.pi * Real.sqrt (2 * A) := by
    change min A (max 0 (Real.log (‖F (Complex.exp (stripPoint v θ)) - a‖ / r))) ≤ _ at hb
    have hmax : max 0 (Real.log (‖F (Complex.exp (stripPoint v θ)) - a‖ / r)) < A := by
      by_contra hn
      rw [min_eq_left (le_of_not_gt hn)] at hb
      exact (not_le_of_gt hstrict) hb
    rw [min_eq_right hmax.le] at hb
    exact (le_max_right _ _).trans hb
  have hn : 0 < ‖F (Complex.exp (stripPoint v θ)) - a‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (ha _ (exp_strip_halfplane (stripPoint_mem hθ))))
  have hnorm := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (div_pos hn hr)] at hnorm
  have hnorm' := (div_le_iff₀ hr).mp hnorm
  simpa only [stripPoint, Complex.exp_add, Complex.ofReal_exp, mul_comm] using hnorm'

/-- `es:good-semicircle`, with the initial short guide segment appearing
explicitly. This proves the manuscript's bound in every unit logarithmic slab
below the segment's terminal radius. -/
theorem exists_small_image_semicircle
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hi : InjOn F {z | 0 < z.im}) {a : ℂ}
    (ha : ∀ z, 0 < z.im → F z ≠ a) {r A q t₀ : ℝ} {β : ℝ → ℂ}
    (hr : 0 < r) (hA : 2 * Real.pi ^ 2 < A)
    (ht₀ : 0 < t₀) (hβ : ContinuousOn β (Icc 0 t₀)) (hβ₀ : β 0 = 0)
    (hβH : ∀ t ∈ Ioc 0 t₀, 0 < (β t).im)
    (hsmall : ∀ t ∈ Ioc 0 t₀, ‖F (β t) - a‖ ≤ r * Real.exp (-A))
    (hq : q + 1 ≤ Real.log ‖β t₀‖) :
    ∃ B ∈ Ioo (Real.exp q) (Real.exp (q + 1)),
      ∀ θ ∈ Ioo 0 Real.pi,
        ‖F ((B : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - a‖ ≤
          r * Real.exp (-A + Real.pi * Real.sqrt (2 * A)) := by
  obtain ⟨B, hB, hbound⟩ := exists_small_image_semicircle_of_anchors hF hi ha
    (mul_pos hr (Real.exp_pos _)) hA (fun v hv =>
      access_segment_section_anchor ht₀ hβ hβ₀ hβH hsmall (hv.2.trans_le hq))
  refine ⟨B, hB, ?_⟩
  intro θ hθ
  simpa only [Real.exp_add, mul_assoc] using hbound θ hθ

/-- The numerical choice used after the semicircle and sector estimates. -/
lemma semicircle_exponential_lt_quarter {A : ℝ} (hA : 64 ≤ A) :
    Real.exp (-A + Real.pi * Real.sqrt (2 * A) + 6) < 1 / 4 := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hsqrt : Real.sqrt (2 * A) ≤ A / 5 := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [mul_nonneg (show 0 ≤ A by positivity) (show 0 ≤ A - 50 by linarith)]
  have hpi : Real.pi * Real.sqrt (2 * A) ≤ 4 * (A / 5) :=
    mul_le_mul Real.pi_lt_four.le hsqrt (Real.sqrt_nonneg _) (by norm_num)
  have hexp : -A + Real.pi * Real.sqrt (2 * A) + 6 < -3 := by linarith
  have hthree : (4 : ℝ) < Real.exp 3 := by
    have hh := Real.add_one_lt_exp (show (3 : ℝ) ≠ 0 by norm_num)
    norm_num only at hh
    exact hh
  calc
    Real.exp (-A + Real.pi * Real.sqrt (2 * A) + 6) < Real.exp (-3) :=
      Real.exp_lt_exp.mpr hexp
    _ < 1 / 4 := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_lt_one_div_of_lt (by norm_num) hthree

/-- The guide supplies small-image semicircles at arbitrarily small radii.
The image estimate is uniform in the chosen radius. -/
theorem exists_arbitrarily_small_image_semicircle
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {z | 0 < z.im})
    (hi : InjOn F {z | 0 < z.im}) {a : ℂ}
    (ha : ∀ z, 0 < z.im → F z ≠ a) {r A t₀ : ℝ} {β : ℝ → ℂ}
    (hr : 0 < r) (hA : 2 * Real.pi ^ 2 < A)
    (ht₀ : 0 < t₀) (hβ : ContinuousOn β (Icc 0 t₀)) (hβ₀ : β 0 = 0)
    (hβH : ∀ t ∈ Ioc 0 t₀, 0 < (β t).im)
    (hsmall : ∀ t ∈ Ioc 0 t₀, ‖F (β t) - a‖ ≤ r * Real.exp (-A)) :
    ∀ δ : ℝ, 0 < δ → ∃ B ∈ Ioo 0 δ, ∀ θ ∈ Ioo 0 Real.pi,
      ‖F ((B : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) - a‖ ≤
        r * Real.exp (-A + Real.pi * Real.sqrt (2 * A)) := by
  intro δ hδ
  let q := min (Real.log δ) (Real.log ‖β t₀‖) - 1
  have hq : q + 1 ≤ Real.log ‖β t₀‖ := by
    dsimp [q]
    linarith [min_le_right (Real.log δ) (Real.log ‖β t₀‖)]
  obtain ⟨B, hB, hbound⟩ := exists_small_image_semicircle hF hi ha hr hA ht₀
    hβ hβ₀ hβH hsmall hq
  refine ⟨B, ⟨(Real.exp_pos q).trans hB.1, hB.2.trans_le ?_⟩, hbound⟩
  calc
    Real.exp (q + 1) ≤ Real.exp (Real.log δ) := by
      apply Real.exp_le_exp.mpr
      dsimp [q]
      linarith [min_le_left (Real.log δ) (Real.log ‖β t₀‖)]
    _ = δ := Real.exp_log hδ

end SLEExactGauge.SmallImageSemicircle

end

end OAI

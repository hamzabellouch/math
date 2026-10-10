import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.LevelLocality
import OAI.Geometry.CAT0Fillings.Gradient.Chart
import OAI.Geometry.CAT0Fillings.Gradient.HilbertAtlas

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

noncomputable def positiveTrunc (τ t : ℝ) : ℝ := max (|t|-τ) 0

lemma positiveTrunc_lipschitz (τ : ℝ) : LipschitzWith 1 (positiveTrunc τ) := by
  have ha : LipschitzWith 1 (abs : ℝ → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using abs_abs_sub_abs_le_abs_sub x y
  change LipschitzWith 1 (fun t : ℝ => max (|t|-τ) 0)
  have hh := (ha.sub (LipschitzWith.const τ)).max (LipschitzWith.const (0:ℝ))
  norm_num only [add_zero,max_eq_left zero_le_one] at hh
  exact hh

lemma positiveTrunc_nonneg (τ t : ℝ) : 0 ≤ positiveTrunc τ t := le_max_right _ _

lemma positiveTrunc_sub_bounds {τ : ℝ} (hτ : 0 ≤ τ) (t : ℝ) :
    0 ≤ |t|-positiveTrunc τ t ∧ |t|-positiveTrunc τ t ≤ τ := by
  dsimp only [positiveTrunc]
  constructor
  · apply sub_nonneg.mpr
    exact max_le (by linarith) (abs_nonneg _)
  · linarith [le_max_left (|t|-τ) (0:ℝ)]

lemma ae_fderiv_trunc_cases {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] {F : E → ℝ} {K : ℝ≥0}
    (hF : LipschitzWith K F) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ᵐ z ∂μ, fderiv ℝ (positiveTrunc τ ∘ F) z = 0 ∨
      fderiv ℝ (positiveTrunc τ ∘ F) z = fderiv ℝ F z ∨
      fderiv ℝ (positiveTrunc τ ∘ F) z = -fderiv ℝ F z := by
  have hcomp := (positiveTrunc_lipschitz τ).comp hF
  filter_upwards [LipschitzWith.ae_fderiv_zero_on_level μ hcomp 0] with z hz
  by_cases hzero : positiveTrunc τ (F z) = 0
  · exact Or.inl (hz hzero)
  have hzpos : 0 < |F z|-τ := by
    by_contra hn
    exact hzero (max_eq_right (le_of_not_gt hn))
  have hne : F z ≠ 0 := by
    intro h
    simp only [h,abs_zero,zero_sub] at hzpos
    linarith
  have hev : ∀ᶠ y in 𝓝 z, τ < |F y| := hF.continuous.abs.continuousAt
    (Ioi_mem_nhds (by linarith : τ < |F z|))
  by_cases hpos : 0 < F z
  · right; left
    have hp : ∀ᶠ y in 𝓝 z, 0 < F y := hF.continuous.continuousAt (Ioi_mem_nhds hpos)
    have he : positiveTrunc τ ∘ F =ᶠ[𝓝 z] fun y => F y-τ := by
      filter_upwards [hev,hp] with y hy hp
      simp only [Function.comp_apply,positiveTrunc,abs_of_pos hp]
      rw [abs_of_pos hp] at hy
      exact max_eq_left (by linarith)
    exact he.fderiv_eq.trans (fderiv_sub_const τ)
  · right; right
    have hn : F z < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
    have hp : ∀ᶠ y in 𝓝 z, F y < 0 := hF.continuous.continuousAt (Iio_mem_nhds hn)
    have he : positiveTrunc τ ∘ F =ᶠ[𝓝 z] fun y => -F y-τ := by
      filter_upwards [hev,hp] with y hy hp
      simp only [Function.comp_apply,positiveTrunc,abs_of_neg hp]
      rw [abs_of_neg hp] at hy
      exact max_eq_left (by linarith)
    rw [he.fderiv_eq,fderiv_sub_const,fderiv_fun_neg]

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_normSq_trunc_le (i : ℕ) {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      q.normSq i (positiveTrunc τ ∘ u) z ≤ q.normSq i u z := by
  let C := q.chart i
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨F,hF,heF⟩ := (C.scalar_lipschitzOn hL hu).extend_real
  have hecomp : EqOn (C.scalar (positiveTrunc τ ∘ u)) (positiveTrunc τ ∘ F) C.domain := by
    intro z hz
    simp only [IntegerChart.scalar,dite_eq_left hz,Function.comp_apply]
    rw [←heF hz]
    simp only [IntegerChart.scalar,dite_eq_left hz]
  have hcase := ae_fderiv_trunc_cases volume hF hτ
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hF heF,
    ae_fderivWithin_eq_fderiv_extension volume C.borel ((positiveTrunc_lipschitz τ).comp hF) hecomp,
    hcase.filter_mono ae_restrict_le,q.ae_normSq_bounds i hu] with z hz hc hcase hb
  change fderivWithin ℝ (C.scalar u) C.domain z = _ at hz
  rcases hcase with hzero | heq | heq
  · have he : q.covector i (positiveTrunc τ ∘ u) z = 0 := by
      dsimp only [covector]
      change differentialRow (fderivWithin ℝ (C.scalar (positiveTrunc τ ∘ u)) C.domain z) = 0
      rw [hc,hzero]
      ext j
      rfl
    simpa only [normSq,he,zero_dotProduct] using hb.1
  · have he : q.covector i (positiveTrunc τ ∘ u) z = q.covector i u z := by
      dsimp only [covector]
      change differentialRow (fderivWithin ℝ (C.scalar (positiveTrunc τ ∘ u)) C.domain z) =
        differentialRow (fderivWithin ℝ (C.scalar u) C.domain z)
      rw [hc,hz,heq]
    simp only [normSq,he,le_refl]
  · have he : q.covector i (positiveTrunc τ ∘ u) z = -q.covector i u z := by
      dsimp only [covector]
      change differentialRow (fderivWithin ℝ (C.scalar (positiveTrunc τ ∘ u)) C.domain z) =
        -differentialRow (fderivWithin ℝ (C.scalar u) C.domain z)
      rw [hc,hz,heq]
      ext j
      rfl
    simp only [normSq,he,Matrix.mulVec_neg,neg_dotProduct,dotProduct_neg,neg_neg,le_refl]

lemma energyMeasure_trunc_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    q.energyMeasure (positiveTrunc τ ∘ u) ≤ q.energyMeasure u := by
  apply Measure.le_iff.mpr
  intro E hE
  simp only [energyMeasure,weightedMeasure,Measure.sum_apply _ hE]
  apply ENNReal.tsum_le_tsum
  intro i
  exact densityPush_mono_ae (q.chart i).measurable_paramExtended
    ((q.ae_normSq_trunc_le i hu hτ).mono fun z hz =>
      mul_le_mul_of_nonneg_left hz (q.density_nonneg i z)) E

lemma energy_trunc_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (q.energyMeasure (positiveTrunc τ ∘ u)).real univ ≤ (q.energyMeasure u).real univ := by
  let := q.energyMeasure_finite hu
  exact ENNReal.toReal_mono (measure_ne_top _ _) (q.energyMeasure_trunc_le hu hτ univ)

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma continuous_memLp {u : X → ℝ} (hu : Continuous u) (p : ℝ≥0∞) : MemLp u p μ :=
  hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace u)

lemma lpNorm_sq_moment {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℝ} (hu : Continuous u) (hu0 : ∀ x, 0 ≤ u x)
    {p : ℝ} (hp : 0 < p) :
    lpNorm u (ENNReal.ofReal p) μ ^2 =
      ((∫⁻ x, ENNReal.ofReal ((u x)^p) ∂μ).toReal)^(2/p) := by
  rw [←toReal_eLpNorm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
      hu.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  simp only [←ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hu0 _),
    ←ENNReal.ofReal_rpow_of_nonneg (hu0 _) hp.le,←ENNReal.toReal_rpow]
  rw [←Real.rpow_natCast,←Real.rpow_mul ENNReal.toReal_nonneg]
  congr 1
  ring

lemma lpNorm_two_sq {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ} (hu : Continuous u) :
    lpNorm u 2 μ ^2 = ∫ x, (u x)^2 ∂μ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hu.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs]
  rw [←Real.rpow_natCast,←Real.rpow_mul (integral_nonneg fun x => sq_nonneg (u x))]
  norm_num

lemma truncation_small_support {u : X → ℝ} (hu : Continuous u) {δ : ℝ} (hδ : 0 < δ)
    (hu2 : 0 < lpNorm u 2 μ) :
    μ.real {x | 0 < positiveTrunc (lpNorm u 2 μ / Real.sqrt δ) (u x)} ≤ δ := by
  let τ := lpNorm u 2 μ / Real.sqrt δ
  have hτ : 0 < τ := div_pos hu2 (Real.sqrt_pos.mpr hδ)
  have he : τ^2*δ = lpNorm u 2 μ ^2 := by
    dsimp [τ]
    rw [div_pow,Real.sq_sqrt hδ.le]
    exact div_mul_cancel₀ _ hδ.ne'
  have hi : Integrable (fun x => (u x)^2) μ := (continuous_memLp μ (hu.pow 2) 1).integrable (by norm_num)
  have hb := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun x => sq_nonneg (u x)) hi (τ^2)
  have hsub : {x | 0 < positiveTrunc τ (u x)} ⊆ {x | τ^2 ≤ (u x)^2} := by
    intro x hx
    have ha : τ < |u x| := by
      simpa only [mem_ofPred_eq,positiveTrunc,lt_max_iff,lt_self_iff_false,or_false,sub_pos] using hx
    change τ^2 ≤ (u x)^2
    nlinarith [sq_abs (u x)]
  have hm := measureReal_mono (μ := μ) hsub
  rw [←lpNorm_two_sq μ hu] at hb
  have hh := (mul_le_mul_of_nonneg_left hm (sq_nonneg τ)).trans hb
  change μ.real {x | 0 < positiveTrunc τ (u x)} ≤ δ
  nlinarith [sq_pos_of_pos hτ]

lemma truncation_norm_bound {u : X → ℝ} (hu : Continuous u) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpfin : p ≠ ∞) {τ : ℝ} (hτ : 0 ≤ τ) :
    lpNorm u p μ ≤ lpNorm (positiveTrunc τ ∘ u) p μ +
      μ.real univ ^ p.toReal⁻¹ * τ := by
  let z := positiveTrunc τ ∘ u
  have hz : Continuous z := (positiveTrunc_lipschitz τ).continuous.comp hu
  have ht := lpNorm_le_lpNorm_add_lpNorm_sub' (continuous_memLp μ hz p) hp
    (f := fun x => |u x|)
  rw [lpNorm_fun_abs hu.aestronglyMeasurable] at ht
  apply ht.trans
  apply add_le_add_right
  have hb : lpNorm (fun x => |u x|-z x) p μ ≤ lpNorm (fun _ : X => τ) p μ := by
    apply lpNorm_mono_real (memLp_const τ)
    intro x
    change abs (|u x|-positiveTrunc τ (u x)) ≤ τ
    have h := positiveTrunc_sub_bounds hτ (u x)
    exact (abs_le.mpr ⟨by linarith [h.1],h.2⟩)
  rw [lpNorm_const' (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hpfin,
    Real.norm_eq_abs,abs_of_nonneg hτ] at hb
  exact hb.trans_eq (mul_comm _ _)

end CAT0Fillings
end

end OAI

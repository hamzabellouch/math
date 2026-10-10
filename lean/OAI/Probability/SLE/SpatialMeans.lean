import Mathlib
import OAI.Probability.SLE.InverseMoments

namespace OAI

/-! Spatial Means for chordal SLE. -/

section
section
section
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace SpatialClippedFamily
variable {Ω : Type*} [MeasurableSpace Ω] {U : ℝ≥0 → Ω → ℝ}
  (c : SpatialClippedFamily U)
noncomputable def jointChart (p : ℝ≥0 × (ℂ × Ω)) : ℂ :=
  limUnder atTop (fun n => c.chartApprox n p)

lemma jointChart_measurable : Measurable c.jointChart :=
  (StronglyMeasurable.limUnder (fun n => (c.chartApprox_measurable n).stronglyMeasurable)).measurable

lemma jointChart_eq {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ} (ω : Ω)
    (hUc : Continuous (fun t => U t ω))
    (hw : IsCapacityTwoWitness (fun t => U t ω) γ G F)
    (t : ℝ≥0) (z : ℂ) :
    c.jointChart (t, z, ω) = if z ∈ survivingDomain γ t then G t z else 0 := by
  classical
  unfold jointChart
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_nhds_of_eventually_eq
  by_cases hz : z ∈ survivingDomain γ t
  · filter_upwards [c.eventually_valid_agrees ω hUc hw t z hz] with n hn
    rw [ite_eq_left hz, chartApprox, ite_eq_left hn.1, hn.2, logCoordinates_re, logCoordinates_im,
      Real.exp_log (hw.imag_positive t z hz)]
    exact Complex.re_add_im _
  · filter_upwards [] with n
    have hn : ¬ c.valid n t z ω := fun hv => hz (c.live_of_valid ω hUc hw n t z hv)
    simp only [chartApprox, ite_eq_right hn, ite_eq_right hz]

include c

 

lemma live_measurable
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hUc : ∀ ω, Continuous (fun t => U t ω))
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => U t ω) (γ ω) (G ω) (F ω)) :
    MeasurableSet {p : ℝ≥0 × (ℂ × Ω) | p.2.1 ∈ survivingDomain (γ p.2.2) p.1} := by
  have he : {p : ℝ≥0 × (ℂ × Ω) | p.2.1 ∈ survivingDomain (γ p.2.2) p.1} =
      ⋃ n : ℕ, {p | c.valid n p.1 p.2.1 p.2.2} := by
    ext p
    constructor
    · intro hp
      obtain ⟨n, hn⟩ := (c.eventually_valid_agrees p.2.2 (hUc _) (hw _) p.1 p.2.1 hp).exists
      exact mem_iUnion.mpr ⟨n, hn.1⟩
    · intro hp
      obtain ⟨n, hn⟩ := mem_iUnion.mp hp
      exact c.live_of_valid p.2.2 (hUc _) (hw _) n p.1 p.2.1 hn
  rw [he]
  exact MeasurableSet.iUnion (c.valid_measurable)

end SpatialClippedFamily
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma spatialHitTime_mem {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (t : ℝ≥0) (ht : spatialHitTime γ z r = t) :
    dist (γ t) z = r := by
  obtain ⟨s, hs, he⟩ := (spatialHitTime_le_iff hc z r t).mp ht.le
  have hle := (spatialHitTime_le_iff hc z r s).mpr ⟨s, ⟨bot_le, le_rfl⟩, he⟩
  rw [ht] at hle
  have hst : s = t := le_antisymm hs.2 (WithTop.coe_le_coe.mp hle)
  exact hst ▸ he

 

noncomputable def liveSpatialHitTime (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) : WithTop ℝ≥0 :=
  if ({t : ℝ≥0 | z ∈ survivingDomain γ t ∧ dist (γ t) z ≤ r}).Nonempty then
    ↑(sInf {t : ℝ≥0 | z ∈ survivingDomain γ t ∧ dist (γ t) z ≤ r}) else ⊤

lemma spatialHitTime_le_of_dist_le {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z)
    (t : ℝ≥0) (ht : dist (γ t) z ≤ r) : spatialHitTime γ z r ≤ t := by
  obtain ⟨s, hst, he⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ t from bot_le)
    (hc.dist continuous_const).continuousOn ⟨ht, hs⟩
  exact (spatialHitTime_le_iff hc z r t).mpr ⟨s, hst, he⟩

lemma liveSpatialHitTime_eq {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z) :
    liveSpatialHitTime γ z r =
      if spatialHitTime γ z r = ⊤ then ⊤ else
        if z ∈ survivingDomain γ ((spatialHitTime γ z r).untopD 0) then
          spatialHitTime γ z r else ⊤ := by
  let V := {t : ℝ≥0 | z ∈ survivingDomain γ t ∧ dist (γ t) z ≤ r}
  by_cases hv : V.Nonempty
  · obtain ⟨t, ht⟩ := hv
    have hhit := spatialHitTime_le_of_dist_le hc z r hs t ht.2
    have hn : spatialHitTime γ z r ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hhit
    obtain ⟨v, he⟩ := WithTop.ne_top_iff_exists.mp hn
    have hvle : v ≤ t := WithTop.coe_le_coe.mp (he ▸ hhit)
    have hvl : z ∈ survivingDomain γ v := survivingDomain_antitone γ hvle ht.1
    have hvm : v ∈ V := ⟨hvl, (spatialHitTime_mem hc z r v he.symm).le⟩
    have hmin : sInf V = v := by
      apply le_antisymm (csInf_le ⟨0, fun _ _ => bot_le⟩ hvm)
      apply le_csInf ⟨v, hvm⟩
      intro s hs'
      exact WithTop.coe_le_coe.mp (he ▸ spatialHitTime_le_of_dist_le hc z r hs s hs'.2)
    change (if V.Nonempty then ((sInf V : ℝ≥0) : WithTop ℝ≥0) else ⊤) = _
    rw [ite_eq_left ⟨v, hvm⟩, hmin, ite_eq_right hn, ← he, WithTop.untopD_coe, ite_eq_left hvl]
  · change (if V.Nonempty then ((sInf V : ℝ≥0) : WithTop ℝ≥0) else ⊤) = _
    rw [ite_eq_right hv]
    by_cases hn : spatialHitTime γ z r = ⊤
    · rw [ite_eq_left hn]
    · rw [ite_eq_right hn]
      obtain ⟨v, he⟩ := WithTop.ne_top_iff_exists.mp hn
      rw [← he, WithTop.untopD_coe]
      have hnl : z ∉ survivingDomain γ v := fun h =>
        hv ⟨v, h, (spatialHitTime_mem hc z r v he.symm).le⟩
      rw [ite_eq_right hnl]

 

lemma spatialGreenWeight_eq_live {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (κ : ℝ) (U : ℝ≥0 → ℝ) (G : ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z) :
    spatialGreenWeight κ U γ G z r =
      if liveSpatialHitTime γ z r = ⊤ then 0 else
        greenDensity κ U γ G ((liveSpatialHitTime γ z r).untopD 0) z := by
  rw [liveSpatialHitTime_eq hc z r hs]
  by_cases hn : spatialHitTime γ z r = ⊤
  · simp only [spatialGreenWeight, ite_eq_left hn, ite_true]
  · rw [ite_eq_right hn]
    by_cases hl : z ∈ survivingDomain γ ((spatialHitTime γ z r).untopD 0)
    · simp only [ite_eq_left hl, ite_eq_right hn, spatialGreenWeight]
    · simp only [spatialGreenWeight, ite_eq_right hn,
        greenDensity, ite_eq_right hl, ite_true]

lemma spatialHitTime_measurable {Ω : Type*} [MeasurableSpace Ω]
    (γ : Ω → ℝ≥0 → ℂ) (hc : ∀ ω, Continuous (γ ω))
    (hm : ∀ t, Measurable (fun ω => γ ω t)) (r : ℝ) :
    Measurable (fun p : ℂ × Ω => spatialHitTime (γ p.2) p.1 r) := by
  let X (t : ℝ≥0) (p : ℂ × Ω) : ℝ := dist (γ p.2 t) p.1 - r
  have hXa : Adapted (⊤ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℂ × Ω))) X := by
    intro t
    exact (((hm t).comp measurable_snd).dist measurable_fst).sub_const r
  have hXc (p : ℂ × Ω) : Continuous (fun t => X t p) :=
    ((hc p.2).dist continuous_const).sub continuous_const
  have h := continuous_zero_hit_stopping ⊤ X hXa hXc 0
  exact h.measurable.mono h.measurableSpace_le le_rfl

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma jointGreen_measurable :
    Measurable (fun p : ℝ≥0 × (ℂ × a.samples) => greenDensity κ
      (fun t => Real.sqrt κ * a.B t p.2.2) (γ p.2.2) (a.G p.2.2) p.1 p.2.1) := by
  have hm : Measurable (fun p : ℝ≥0 × a.samples => a.B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable a.continuous_B a.measurable_B
  let c := spatialClippedFamily (fun t ω => Real.sqrt κ * a.B t ω)
    (hm.const_mul _) (fun ω => (a.continuous_B ω).const_mul _)
  convert c.jointGreen_measurable κ a.B hm using 1
  funext p
  exact (c.jointGreen_eq κ a.B p.2.2 ((a.continuous_B _).const_mul _)
    (fun _ => rfl) (a.witness _) p.1 p.2.1).symm

lemma spatialGreenWeight_measurable (r : ℝ) :
    Measurable (fun p : ℂ × a.samples => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t p.2) (γ p.2) (a.G p.2) p.1 r) := by
  classical
  have hm (t : ℝ≥0) : Measurable (fun ω : a.samples => γ ω t) :=
    (a.trace_adapted t).mono (a.filtration.le t) le_rfl
  have hc (ω : a.samples) : Continuous (γ ω) := a.trace_continuous ω
  have ht : Measurable (fun p : ℂ × a.samples => spatialHitTime (γ p.2) p.1 r) :=
    spatialHitTime_measurable (fun ω : a.samples => γ ω) hc hm r
  have he : MeasurableSet {p : ℂ × a.samples | spatialHitTime (γ p.2) p.1 r = ⊤} :=
    measurableSet_eq_fun ht measurable_const
  have hg := a.jointGreen_measurable.comp ((ht.untopD 0).prodMk measurable_id)
  have hh := @Measurable.ite _ _ _ _ _ _ _ (fun _ => Classical.propDecidable _) he
    (measurable_const (a := (0 : ℝ))) hg
  simpa only [spatialGreenWeight, Function.comp_def, id_eq] using hh

end RegularSLEPresentation
end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

noncomputable def spatialSlabCoefficient (κ : ℝ) (U : ℝ≥0 → ℝ)
    (γ : ℝ≥0 → ℂ) (G : ℝ≥0 → ℂ → ℂ) (r ε : ℝ) (t : ℝ≥0) (z : ℂ) : ℝ :=
  if spatialHitTime γ z r ≤ t ∧ (t : WithTop ℝ≥0) ≤ spatialHitTime γ z ε ∧
      z ∈ survivingDomain γ t then greenBrownianCoefficient κ U γ G t z else 0

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.radius_before_spatial_hit
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (z : ℂ) (r : ℝ) (hr : 0 < r) (hy : r ≤ z.im) (t : ℝ≥0)
    (hz : z ∈ survivingDomain γ t) (ht : (t : WithTop ℝ≥0) ≤ spatialHitTime γ z r) :
    r ≤ fullRadius G t z := by
  apply h.radius_ge_of_no_trace_approach hU t z hz hr hy
  intro s hs
  by_contra hn
  have hstart : r ≤ dist (γ 0) z := by
    rw [h.2.1, dist_zero_left]
    exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  have hhit := spatialHitTime_lt_of_dist_lt h.1 z r hstart s (lt_of_not_ge hn)
  exact (not_lt_of_ge ht) (hhit.trans_le (WithTop.coe_le_coe.mpr hs.2))

lemma IsCapacityTwoWitness.slab_coefficient_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε)
    (r : ℝ) (z : ℂ) (hy : ε ≤ z.im) (t : ℝ≥0) :
    |spatialSlabCoefficient κ U γ G r ε t z| ≤
      if z ∈ survivingDomain γ t then
        (Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) * chartPoissonRate U G t z
      else 0 := by
  by_cases ha : spatialHitTime γ z r ≤ t ∧ (t : WithTop ℝ≥0) ≤ spatialHitTime γ z ε ∧
      z ∈ survivingDomain γ t
  · rw [spatialSlabCoefficient, ite_eq_left ha, ite_eq_left ha.2.2]
    exact h.green_coefficient_le_poisson hU hκ hκ4 hε t z ha.2.2
      (h.radius_before_spatial_hit hU z ε hε hy t ha.2.2 ha.2.1)
  · rw [spatialSlabCoefficient, ite_eq_right ha, abs_zero]
    split_ifs with hz
    · exact mul_nonneg (by
        have hg := greenExponent_ge_one hκ hκ4
        exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
          (Real.rpow_nonneg hε.le _)) (h.poissonRate_nonneg t z hz)
    · exact le_rfl

 

theorem IsCapacityTwoWitness.slab_pair_later_start
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ ε : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (hε : 0 < ε)
    (r : ℝ) (z w : ℂ) (hzy : ε ≤ z.im) (hwy : ε ≤ w.im) (hne : z ≠ w)
    (s : ℝ≥0) (hs : spatialHitTime γ z r = s) :
    (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
      spatialSlabCoefficient κ U γ G r ε t.toNNReal w|) ≤
      ENNReal.ofReal ((Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)) ^ 2) *
        ENNReal.ofReal (halfPlaneGreen (G s z) (G s w) / 4) := by
  let C := Real.sqrt κ * greenExponent κ * ε ^ (-codimension κ)
  let S := {t : ℝ | (s : ℝ) ≤ t ∧ z ∈ survivingDomain γ t.toNNReal ∧
    w ∈ survivingDomain γ t.toNNReal}
  let f := fun t : ℝ => ENNReal.ofReal (chartPoissonRate U G t.toNNReal z *
    chartPoissonRate U G t.toNNReal w)
  have hC : 0 ≤ C := by
    have hg := greenExponent_ge_one hκ hκ4
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (Real.rpow_nonneg hε.le _)
  have hpoint (t : ℝ) (ht0 : 0 ≤ t) : ENNReal.ofReal |spatialSlabCoefficient κ U γ G r ε t.toNNReal z *
      spatialSlabCoefficient κ U γ G r ε t.toNNReal w| ≤
      S.indicator (fun t => ENNReal.ofReal (C ^ 2) * f t) t := by
    by_cases ha : spatialHitTime γ z r ≤ t.toNNReal ∧
        (t.toNNReal : WithTop ℝ≥0) ≤ spatialHitTime γ z ε ∧ z ∈ survivingDomain γ t.toNNReal
    · by_cases hb : spatialHitTime γ w r ≤ t.toNNReal ∧
          (t.toNNReal : WithTop ℝ≥0) ≤ spatialHitTime γ w ε ∧ w ∈ survivingDomain γ t.toNNReal
      · have hst : (s : ℝ) ≤ t := by
          have hst' : s ≤ t.toNNReal := WithTop.coe_le_coe.mp (hs ▸ ha.1)
          rw [← Real.coe_toNNReal t ht0]
          exact hst'
        rw [Set.indicator_of_mem (show t ∈ S from ⟨hst, ha.2.2, hb.2.2⟩),
          ← ENNReal.ofReal_mul (sq_nonneg C)]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_mul]
        have hz := h.slab_coefficient_bound hU hκ hκ4 hε r z hzy t.toNNReal
        have hw := h.slab_coefficient_bound hU hκ hκ4 hε r w hwy t.toNNReal
        rw [ite_eq_left ha.2.2] at hz
        rw [ite_eq_left hb.2.2] at hw
        calc
          _ ≤ (C * chartPoissonRate U G t.toNNReal z) *
              (C * chartPoissonRate U G t.toNNReal w) :=
            mul_le_mul hz hw (abs_nonneg _) (mul_nonneg hC (h.poissonRate_nonneg _ z ha.2.2))
          _ = _ := by ring
      · simp only [spatialSlabCoefficient, ite_eq_right hb, mul_zero, abs_zero, ENNReal.ofReal_zero, zero_le]
    · simp only [spatialSlabCoefficient, ite_eq_right ha, zero_mul, abs_zero, ENNReal.ofReal_zero, zero_le]
  calc
    _ ≤ ∫⁻ t in Ici (0 : ℝ), S.indicator (fun t => ENNReal.ofReal (C ^ 2) * f t) t := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact hpoint t ht
    _ ≤ ∫⁻ t, S.indicator (fun t => ENNReal.ofReal (C ^ 2) * f t) t :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ ∫⁻ t in S, ENNReal.ofReal (C ^ 2) * f t := lintegral_indicator_le _ _
    _ = ENNReal.ofReal (C ^ 2) * ∫⁻ t in S, f t := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul le_rfl (h.live_green_pair_bound hU s z w hne) (by positivity) (by positivity)

end SLEExactGauge

end

 
section

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

variable {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}

lemma IsCapacityTwoWitness.green_before_spatial_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ r : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hr : 0 < r)
    (z : ℂ) (hy : r ≤ z.im) (t : ℝ≥0)
    (ht : (t : WithTop ℝ≥0) ≤ spatialHitTime γ z r) :
    greenDensity κ U γ G t z ≤ r ^ (-codimension κ) := by
  by_cases hz : z ∈ survivingDomain γ t
  · have hR := h.radius_before_spatial_hit hU z r hr hy t hz ht
    have hs : 0 ≤ Real.sin (Complex.arg (G t z - (U t : ℂ))) := by
      rw [Complex.sin_arg]
      have hi := (h.imag_positive t z hz).le
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact div_nonneg hi (norm_nonneg _)
    rw [greenDensity, ite_eq_left hz]
    calc
      _ ≤ r ^ (-codimension κ) * 1 := mul_le_mul
        (Real.rpow_le_rpow_of_nonpos hr hR (neg_nonpos.mpr (codimension_pos κ hκ8).le))
        (Real.rpow_le_one hs (Real.sin_le_one _) (greenExponent_pos κ hκ hκ8).le)
        (Real.rpow_nonneg hs _) (Real.rpow_nonneg hr.le _)
      _ = _ := mul_one _
  · rw [greenDensity, ite_eq_right hz]
    exact Real.rpow_nonneg hr.le _

lemma IsCapacityTwoWitness.spatialGreenWeight_bound
    (h : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    {κ r : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hr : 0 < r)
    (z : ℂ) (hy : r ≤ z.im) :
    0 ≤ spatialGreenWeight κ U γ G z r ∧
      spatialGreenWeight κ U γ G z r ≤ r ^ (-codimension κ) := by
  by_cases ht : spatialHitTime γ z r = ⊤
  · simp only [spatialGreenWeight, ite_eq_left ht]
    exact ⟨le_rfl, Real.rpow_nonneg hr.le _⟩
  · rw [spatialGreenWeight, ite_eq_right ht]
    refine ⟨greenDensity_nonneg h κ _ z, h.green_before_spatial_bound hU hκ hκ8 hr z hy _ ?_⟩
    exact WithTop.coe_untopD_le _ _

noncomputable def spatialRealMass (κ : ℝ) (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (r : ℝ) (A : Set ℂ) : ℝ :=
  ∫ z in A, spatialGreenWeight κ U γ G z r

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

lemma spatialRealMass_measurable (A : Set ℂ) (r : ℝ) :
    Measurable (fun ω : a.samples => spatialRealMass κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) r A) :=
  (a.spatialGreenWeight_measurable r).stronglyMeasurable.integral_prod_left'.measurable

lemma spatialGreenWeight_spatial_integrable
    (hκ : 0 < κ) (hκ8 : κ < 8) (r : ℝ) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (hheight : ∀ z ∈ A, r ≤ z.im) (ω : a.samples) :
    IntegrableOn (fun z => spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r) A := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  apply Integrable.of_bound
    ((a.spatialGreenWeight_measurable r).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    (r ^ (-codimension κ))
  filter_upwards [ae_restrict_mem hA] with z hz
  have h := (a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _) hκ hκ8 hr z (hheight z hz)
  simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

lemma spatialRealMass_bound
    (hκ : 0 < κ) (hκ8 : κ < 8) (r : ℝ) (hr : 0 < r)
    (A : Set ℂ) (hA : MeasurableSet A) (hfin : volume A ≠ ∞)
    (hheight : ∀ z ∈ A, r ≤ z.im) (ω : a.samples) :
    0 ≤ spatialRealMass κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) r A ∧
      spatialRealMass κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) r A ≤
        (volume A).toReal * r ^ (-codimension κ) := by
  let : IsFiniteMeasure (volume.restrict A) := ⟨by
    simpa only [Measure.restrict_apply_univ] using lt_top_iff_ne_top.mpr hfin⟩
  have hi := a.spatialGreenWeight_spatial_integrable hκ hκ8 r hr A hA hfin hheight ω
  have hb : ∀ᵐ z ∂(volume.restrict A), 0 ≤ spatialGreenWeight κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r ∧
      spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z r ≤ r ^ (-codimension κ) := by
    filter_upwards [ae_restrict_mem hA] with z hz
    exact (a.witness ω).spatialGreenWeight_bound ((a.continuous_B ω).const_mul _) hκ hκ8 hr z (hheight z hz)
  refine ⟨integral_nonneg_of_ae (hb.mono fun _ h => h.1), ?_⟩
  calc
    _ ≤ ∫ _z in A, r ^ (-codimension κ) := integral_mono_ae hi (integrable_const _) (hb.mono fun _ h => h.2)
    _ = _ := by simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, measureReal_def]

end RegularSLEPresentation
end SLEExactGauge

end

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

universe u_source_stopped

 

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

local instance spatialMeansStoppedRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance spatialMeansStoppedComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance spatialMeansStoppedRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance spatialMeansStoppedComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

end
end SLEExactGauge

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

end SLEExactGauge

open Set Filter MeasureTheory Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance spatialMeansDrivingRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance spatialMeansDrivingRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance spatialMeansSourceRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance spatialMeansSourceComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance spatialMeansSourceRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance spatialMeansSourceComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance spatialMeansMapRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance spatialMeansMapComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance spatialMeansMapRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance spatialMeansMapComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance spatialMeansTraceRealPathMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance spatialMeansTraceComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance spatialMeansTraceRealPathBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance spatialMeansTraceComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
end
end SLEExactGauge

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge
 

lemma source_halfplane_map_local_bound {f : ℂ → ℂ} {z w : ℂ} {r ε : ℝ}
    (hr : 0 < r) (hε : 0 ≤ ε) (hεr : ε ≤ r / 2)
    (hd : DifferentiableOn ℂ f (ball z r))
    (hm : MapsTo f (ball z r) upperHalfPlane) (hw : dist w z ≤ ε) :
    dist (f w) (f z) ≤ 4 * (f z).im * ε / r := by
  have hz : z ∈ ball z r := mem_ball_self hr
  have hwr : w ∈ ball z r := mem_ball.mpr (hw.trans_lt (by linarith))
  have hy : 0 < (f z).im := hm hz
  have hden (v : ℂ) (hv : v ∈ ball z r) : f v - star (f z) ≠ 0 := by
    intro he
    have hx := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.star_def, Complex.conj_im, Complex.zero_im] at hx
    have hvy : 0 < (f v).im := hm hv
    linarith
  let g := fun v => (f v - f z) / (f v - star (f z))
  have hg0 : g z = 0 := by simp [g]
  have hgd : DifferentiableOn ℂ g (ball z r) :=
    (hd.sub_const _).div (hd.sub_const _) hden
  have hgm : MapsTo g (ball z r) (closedBall (g z) 1) := by
    intro v hv
    rw [hg0, mem_closedBall_zero_iff]
    exact (upper_mobius_norm_lt_one (hm hv) hy).le
  have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hgd hgm hwr
  rw [hg0, dist_zero_right] at hsch
  have hsch' : ‖g w‖ ≤ ε / r :=
    hsch.trans (by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using
      div_le_div_of_nonneg_right hw hr.le)
  have hmult : ‖f w - f z‖ ≤ (ε / r) * ‖f w - star (f z)‖ := by
    simpa only [g, norm_div, div_le_iff₀ (norm_pos_iff.mpr (hden w hwr))] using hsch'
  have hn : ‖f z - star (f z)‖ = 2 * (f z).im := by
    rw [Complex.star_def, Complex.sub_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hy), Complex.norm_I, mul_one]
  have htri : ‖f w - star (f z)‖ ≤ ‖f w - f z‖ + 2 * (f z).im := by
    rw [← hn]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have ha : 0 ≤ ε / r := div_nonneg hε hr.le
  have hb : ε / r ≤ 1 / 2 := (div_le_iff₀ hr).mpr (by linarith)
  have hmain := hmult.trans (mul_le_mul_of_nonneg_left htri ha)
  rw [dist_eq_norm]
  have hp := mul_nonneg (sub_nonneg.mpr hb) (norm_nonneg (f w - f z))
  calc
    ‖f w - f z‖ ≤ 4 * (f z).im * (ε / r) := by nlinarith
    _ = _ := by ring
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
namespace SLEExactGauge

 

end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

 

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section

theorem source_killedGreen_progressive
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (z : ℂ) :
    IsStronglyProgressive (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun t ω => greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z) := by
  classical
  let f := Filtration.natural B (fun t => (hm t).stronglyMeasurable)
  have hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable hc hm
  have hnn (n : ℕ) : -(n : ℝ) ≤ n := by linarith [Nat.cast_nonneg (α := ℝ) n]
  let c (n : ℕ) := (exists_clippedLogSolution B hm hBm hc κ (-(n : ℝ)) n (hnn n)
    (initialLogCoordinates z)).some
  let v (n : ℕ) (t : ℝ≥0) (ω : Ω) : Prop :=
    0 < z.im ∧ Real.log z.im ≤ (n : ℝ) ∧ -(n : ℝ) ≤ ((c n).Q t ω).1.im
  let A (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    if v n t ω then greenLogDensity κ ((c n).Q t ω) (B t ω) else 0
  have hQp (n : ℕ) : IsStronglyProgressive f (fun t : ℝ≥0 => (c n).Q t) :=
    (show StronglyAdapted f (fun t : ℝ≥0 => (c n).Q t) from
      fun t => ((c n).adapted t).stronglyMeasurable).isStronglyProgressive_of_continuous
      (fun ω => ((c n).lipschitz ω).continuous.comp NNReal.continuous_coe)
  have hAp (n : ℕ) : IsStronglyProgressive f (A n) := by
    intro T
    have hQ := (hQp n T).measurable
    let : MeasurableSpace Ω := f T
    have hv : MeasurableSet {p : Iic T × Ω | v n p.1 p.2} :=
      (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
        (measurableSet_le measurable_const (Complex.measurable_im.comp hQ.fst)))
    have hBp := (Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)).isStronglyProgressive_of_continuous hc
    have hBm := (hBp T).measurable
    exact (Measurable.ite hv ((greenLogDensity_contDiff κ).continuous.measurable.comp
      (hQ.prodMk hBm)) measurable_const).stronglyMeasurable
  have hlim (t : ℝ≥0) (ω : Ω) : Tendsto (fun n => A n t ω) atTop
      (𝓝 (greenDensity κ (fun s => Real.sqrt κ * B s ω) (γ ω) (G ω) t z)) := by
    apply tendsto_nhds_of_eventually_eq
    have hU : Continuous (fun s => Real.sqrt κ * B s ω) := (hc ω).const_mul _
    have hd (n : ℕ) (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) :=
      ((c n).derivative ω s hs.1).mono (show Icc (0 : ℝ) (t : ℝ) ⊆ Ici 0 from Icc_subset_Ici_self)
    by_cases hz : z ∈ survivingDomain (γ ω) t
    · obtain ⟨N, hN⟩ := exists_nat_ge (max (-Real.log (G ω t z).im) (Real.log z.im))
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hlo : -(n : ℝ) ≤ Real.log (G ω t z).im := by
        have hh := (le_max_left (-Real.log (G ω t z).im) (Real.log z.im)).trans (hN.trans hNn)
        linarith
      have hhi : Real.log z.im ≤ (n : ℝ) := (le_max_right _ _).trans (hN.trans hNn)
      have he : (c n).Q t ω = logLoewnerCoordinates (G ω) z t :=
        clipped_log_loewner_agrees hU (hw ω) t z hz _ _ _ hlo hhi
          (fun s => (c n).Q s ω) ((c n).initial ω) (hd n) ⟨t.coe_nonneg, le_rfl⟩
      have hv : v n t ω := ⟨hz.1.1, hhi, by simpa only [he, logCoordinates_im] using hlo⟩
      simp only [A, ite_eq_left hv, he]
      exact greenLogDensity_logCoordinates hU (hw ω) κ (B t ω) z t hz rfl
    · filter_upwards [] with n
      have hv : ¬ v n t ω := by
        intro hv
        exact hz (clipped_log_identification_of_endpoint hU (hw ω) t z hv.1 _ _ _
          (fun s => (c n).Q s ω) ((c n).initial ω) (hd n) hv.2.2 hv.2.1).1
      simp only [A, ite_eq_right hv, greenDensity, ite_eq_right hz]
  exact isStronglyProgressive_of_tendsto hAp
    (tendsto_pi_nhds.mpr (fun t => tendsto_pi_nhds.mpr (hlim t)))

end
end SLEExactGauge

open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance sourceApproachComplexPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance sourceApproachComplexPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

noncomputable def sourceApproachKernel (ε r : ℝ) (p : ℂ × C(ℝ≥0, ℂ)) : ℝ :=
  if ∃ t : ℝ≥0, dist (p.2 t) p.1 < 8 * p.1.im * ε / r then 1 else 0

lemma sourceApproachKernel_measurable (ε r : ℝ) : Measurable (sourceApproachKernel ε r) := by
  have he (p : ℂ × C(ℝ≥0, ℂ)) :
      (∃ t : ℝ≥0, dist (p.2 t) p.1 < 8 * p.1.im * ε / r) ↔
      ∃ n : ℕ, dist (p.2 (denseSeq ℝ≥0 n)) p.1 < 8 * p.1.im * ε / r := by
    constructor
    · intro h
      exact (denseRange_denseSeq ℝ≥0).exists_mem_open
        (isOpen_lt (p.2.continuous.dist continuous_const) continuous_const) h
    · rintro ⟨n, hn⟩
      exact ⟨_, hn⟩
  apply Measurable.ite _ measurable_const measurable_const
  simp_rw [he]
  rw [ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_lt
    (((continuous_eval_const _).comp continuous_snd).dist continuous_fst).measurable
    ((((continuous_im.comp continuous_fst).const_mul 8).mul_const ε).div_const r).measurable

lemma sourceApproachKernel_norm_le (ε r : ℝ) (p : ℂ × C(ℝ≥0, ℂ)) :
    ‖sourceApproachKernel ε r p‖ ≤ 1 := by
  unfold sourceApproachKernel
  split_ifs <;> norm_num

lemma sourceApproachKernel_zero {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r)
    {p : ℂ × C(ℝ≥0, ℂ)} (hp : p.1.im ≤ 0) : sourceApproachKernel ε r p = 0 := by
  apply ite_eq_right
  rintro ⟨t, ht⟩
  have hh : 8 * p.1.im * ε / r ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hp) hε) hr
  exact not_lt_of_ge (dist_nonneg.trans' hh) ht

lemma source_rpow_scale (p y ε r R : ℝ) (hy : 0 < y) (he : 0 < ε)
    (hr : 0 < r) (hR : 0 < R) :
    (2 * y) ^ (-p) * (8 * y * ε / r) ^ p =
      (4 * R / r) ^ p * ε ^ p * R ^ (-p) := by
  rw [Real.rpow_def_of_pos (by positivity : 0 < 2*y),
    Real.rpow_def_of_pos (by positivity : 0 < 8*y*ε/r),
    Real.rpow_def_of_pos (by positivity : 0 < 4*R/r),
    Real.rpow_def_of_pos he, Real.rpow_def_of_pos hR,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_div (by positivity) hr.ne', Real.log_div (by positivity) hr.ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hy.ne',
    Real.log_mul (by positivity : 8*y ≠ 0) he.ne',
    Real.log_mul (by norm_num : (8:ℝ) ≠ 0) hy.ne',
    Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hR.ne']
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ)=2^3 by norm_num, Real.log_pow]; ring
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; ring
  rw [h8, h4]
  ring
end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory Metric Bornology
open scoped Topology NNReal
namespace SLEExactGauge
 

end SLEExactGauge

open Set Filter MeasureTheory Complex
open scoped Topology NNReal
namespace SLEExactGauge

end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

end
end SLEExactGauge
end
end

end OAI

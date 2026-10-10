import Mathlib

namespace OAI

/-! Cardy integrals and hypergeometric formulas with Poisson-Voronoi crossing definitions. -/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace Cardy

def PositivelyOriented (D : Set ℂ) (γ : ℝ → ℂ) : Prop :=
  ∃ p ∈ D, ∃ H : ℝ × ℝ → ℂ,
    ContinuousOn H (Icc 0 1 ×ˢ Icc 0 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, H (0, t) = γ t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      H (1, t) = p + Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (s, 0) = H (s, 1)) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, H (s, t) ≠ p)

structure JordanQuadrilateral where
  domain : Set ℂ
  domain_open : IsOpen domain
  domain_connected : IsConnected domain
  domain_bounded : Bornology.IsBounded domain
  boundary : ℝ → ℂ
  boundary_continuous : ContinuousOn boundary (Icc 0 1)
  boundary_closed : boundary 0 = boundary 1
  boundary_injective : InjOn boundary (Ico 0 1)
  boundary_image : boundary '' Icc 0 1 = frontier domain
  boundary_positive : PositivelyOriented domain boundary
  tb : ℝ
  tc : ℝ
  td : ℝ
  zero_lt_tb : 0 < tb
  tb_lt_tc : tb < tc
  tc_lt_td : tc < td
  td_lt_one : td < 1

namespace JordanQuadrilateral

def a (Q : JordanQuadrilateral) : ℂ := Q.boundary 0

def b (Q : JordanQuadrilateral) : ℂ := Q.boundary Q.tb

def c (Q : JordanQuadrilateral) : ℂ := Q.boundary Q.tc

def d (Q : JordanQuadrilateral) : ℂ := Q.boundary Q.td

def arcAB (Q : JordanQuadrilateral) : Set ℂ := Q.boundary '' Icc 0 Q.tb

def arcCD (Q : JordanQuadrilateral) : Set ℂ := Q.boundary '' Icc Q.tc Q.td

end JordanQuadrilateral

def upperHalfPlane : Set ℂ := {z | 0 < z.im}

def IsConformalParameter (Q : JordanQuadrilateral) (x : ℝ) : Prop :=
  x ∈ Ioo 0 1 ∧ ∃ f g : ℂ → ℂ,
    DifferentiableOn ℂ f Q.domain ∧
    DifferentiableOn ℂ g upperHalfPlane ∧
    MapsTo f Q.domain upperHalfPlane ∧
    MapsTo g upperHalfPlane Q.domain ∧
    (∀ z ∈ Q.domain, g (f z) = z) ∧
    (∀ w ∈ upperHalfPlane, f (g w) = w) ∧
    Tendsto f (𝓝[Q.domain] Q.a) (𝓝 0) ∧
    Tendsto f (𝓝[Q.domain] Q.b) (𝓝 (x : ℂ)) ∧
    Tendsto f (𝓝[Q.domain] Q.c) (𝓝 1) ∧
    Tendsto (fun z => ‖f z‖) (𝓝[Q.domain] Q.d) atTop

abbrev Box := ℤ × ℤ
abbrev Slot := Box × ℕ
abbrev GeometrySample := (Box → ℕ) × (Slot → ℝ × ℝ)
abbrev Sample := GeometrySample × (Slot → Bool)

def unitUniform : Measure ℝ := volume.restrict (Ico 0 1)

instance : IsProbabilityMeasure unitUniform := by
  constructor
  simp [unitUniform]

def fairColor : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

instance : IsProbabilityMeasure fairColor := by
  unfold fairColor
  infer_instance

def rate (ε : ℝ) : ℝ≥0 := Real.toNNReal ((ε⁻¹) ^ 2)

def countLaw (ε : ℝ) : Measure (Box → ℕ) :=
  Measure.infinitePi (fun _ => poissonMeasure (rate ε))

def locationLaw : Measure (Slot → ℝ × ℝ) :=
  Measure.infinitePi (fun _ => unitUniform.prod unitUniform)

def colorLaw : Measure (Slot → Bool) :=
  Measure.infinitePi (fun _ => fairColor)

instance (ε : ℝ) : IsProbabilityMeasure (countLaw ε) := by
  unfold countLaw
  infer_instance

instance : IsProbabilityMeasure locationLaw := by
  unfold locationLaw
  infer_instance

instance : IsProbabilityMeasure colorLaw := by
  unfold colorLaw
  infer_instance

def geometryLaw (ε : ℝ) : Measure GeometrySample := (countLaw ε).prod locationLaw

instance (ε : ℝ) : IsProbabilityMeasure (geometryLaw ε) := by
  unfold geometryLaw
  infer_instance

def sampleLaw (ε : ℝ) : Measure Sample := (geometryLaw ε).prod colorLaw

instance (ε : ℝ) : IsProbabilityMeasure (sampleLaw ε) := by
  unfold sampleLaw
  infer_instance

def Active (ω : Sample) (i : Slot) : Prop := i.2 < ω.1.1 i.1

def position (ω : Sample) (i : Slot) : ℂ :=
  (((i.1.1 : ℝ) + (ω.1.2 i).1 : ℝ) : ℂ) +
    (((i.1.2 : ℝ) + (ω.1.2 i).2 : ℝ) : ℂ) * Complex.I

def sites (ω : Sample) : Set ℂ := {v | ∃ i, Active ω i ∧ position ω i = v}

def blackSites (ω : Sample) : Set ℂ :=
  {v | ∃ i, Active ω i ∧ ω.2 i = true ∧ position ω i = v}

def voronoiCell (η : Set ℂ) (v : ℂ) : Set ℂ :=
  {z | ∀ u ∈ η, dist z v ≤ dist z u}

def blackRegion (ω : Sample) : Set ℂ :=
  ⋃ v ∈ blackSites ω, voronoiCell (sites ω) v

def Crosses (Q : JordanQuadrilateral) (B : Set ℂ) : Prop :=
  ∃ K : Set ℂ, IsConnected K ∧ K ⊆ B ∩ closure Q.domain ∧
    (K ∩ Q.arcAB).Nonempty ∧ (K ∩ Q.arcCD).Nonempty

def crossingEvent (Q : JordanQuadrilateral) : Set Sample :=
  {ω | Crosses Q (blackRegion ω)}

def crossingProbability (ε : ℝ) (Q : JordanQuadrilateral) : ℝ :=
  (sampleLaw ε (crossingEvent Q)).toReal

def cardyWeight (u : ℝ) : ℝ := (u * (1 - u)) ^ (-(2 : ℝ) / 3)

def cardyIntegral (x : ℝ) : ℝ :=
  (∫ u in 0..x, cardyWeight u) / (∫ u in 0..1, cardyWeight u)

def cardyHypergeometric (x : ℝ) : ℝ :=
  (Real.Gamma (2 / 3) * x ^ ((1 : ℝ) / 3)) /
    (Real.Gamma (1 / 3) * Real.Gamma (4 / 3)) *
      ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3) (4 / 3) x

namespace JordanQuadrilateral

lemma boundary_ne_of_lt (Q : JordanQuadrilateral) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (ht : t < 1) : Q.boundary s ≠ Q.boundary t := by
  intro heq
  exact hst.ne (Q.boundary_injective ⟨hs, hst.trans ht⟩ ⟨hs.trans hst.le, ht⟩ heq)

theorem marks_distinct (Q : JordanQuadrilateral) :
    Q.a ≠ Q.b ∧ Q.a ≠ Q.c ∧ Q.a ≠ Q.d ∧ Q.b ≠ Q.c ∧ Q.b ≠ Q.d ∧ Q.c ≠ Q.d := by
  have h0b := Q.zero_lt_tb
  have hbc := Q.tb_lt_tc
  have hcd := Q.tc_lt_td
  have hd1 := Q.td_lt_one
  exact ⟨Q.boundary_ne_of_lt le_rfl h0b (by linarith),
    Q.boundary_ne_of_lt le_rfl (by linarith) (by linarith),
    Q.boundary_ne_of_lt le_rfl (by linarith) hd1,
    Q.boundary_ne_of_lt h0b.le hbc (by linarith),
    Q.boundary_ne_of_lt h0b.le (by linarith) hd1,
    Q.boundary_ne_of_lt (by linarith) hcd hd1⟩

theorem arcAB_subset_frontier (Q : JordanQuadrilateral) : Q.arcAB ⊆ frontier Q.domain := by
  rw [← Q.boundary_image]
  apply image_mono
  exact Icc_subset_Icc le_rfl (Q.tb_lt_tc.trans (Q.tc_lt_td.trans Q.td_lt_one)).le

theorem arcCD_subset_frontier (Q : JordanQuadrilateral) : Q.arcCD ⊆ frontier Q.domain := by
  rw [← Q.boundary_image]
  apply image_mono
  exact Icc_subset_Icc (Q.zero_lt_tb.trans Q.tb_lt_tc).le Q.td_lt_one.le

theorem endpoints_mem_arcs (Q : JordanQuadrilateral) :
    Q.a ∈ Q.arcAB ∧ Q.b ∈ Q.arcAB ∧ Q.c ∈ Q.arcCD ∧ Q.d ∈ Q.arcCD := by
  exact ⟨mem_image_of_mem _ ⟨le_rfl, Q.zero_lt_tb.le⟩,
    mem_image_of_mem _ ⟨Q.zero_lt_tb.le, le_rfl⟩,
    mem_image_of_mem _ ⟨le_rfl, Q.tc_lt_td.le⟩,
    mem_image_of_mem _ ⟨Q.tc_lt_td.le, le_rfl⟩⟩

end JordanQuadrilateral

theorem voronoiCell_closed (η : Set ℂ) (v : ℂ) : IsClosed (voronoiCell η v) := by
  have h : voronoiCell η v = ⋂ u ∈ η, {z : ℂ | dist z v ≤ dist z u} := by
    ext z
    simp [voronoiCell]
  rw [h]
  exact isClosed_biInter fun u _ => isClosed_le (by fun_prop) (by fun_prop)

theorem site_mem_voronoiCell (η : Set ℂ) (v : ℂ) : v ∈ voronoiCell η v := by
  intro u _
  simp

theorem blackSites_subset_sites (ω : Sample) : blackSites ω ⊆ sites ω := by
  rintro v ⟨i, hi, _, hv⟩
  exact ⟨i, hi, hv⟩

theorem blackSites_subset_blackRegion (ω : Sample) : blackSites ω ⊆ blackRegion ω := by
  intro v hv
  exact mem_iUnion₂.mpr ⟨v, hv, site_mem_voronoiCell _ _⟩

theorem crosses_mono {Q : JordanQuadrilateral} {B B' : Set ℂ}
    (hBB' : B ⊆ B') (h : Crosses Q B) : Crosses Q B' := by
  rcases h with ⟨K, hK, hKB, ha, hc⟩
  exact ⟨K, hK, fun z hz => ⟨hBB' (hKB hz).1, (hKB hz).2⟩, ha, hc⟩

theorem crossingProbability_nonneg (ε : ℝ) (Q : JordanQuadrilateral) :
    0 ≤ crossingProbability ε Q := ENNReal.toReal_nonneg

theorem crossingProbability_le_one (ε : ℝ) (Q : JordanQuadrilateral) :
    crossingProbability ε Q ≤ 1 := by
  exact measureReal_le_one

theorem countLaw_marginal (ε : ℝ) (j : Box) :
    (countLaw ε).map (fun N => N j) = poissonMeasure (rate ε) := by
  exact Measure.infinitePi_map_eval _ j

theorem colorLaw_marginal (i : Slot) :
    colorLaw.map (fun χ => χ i) = fairColor := by
  exact Measure.infinitePi_map_eval _ i

theorem rate_coe (ε : ℝ) : (rate ε : ℝ) = (ε⁻¹) ^ 2 := by
  exact Real.coe_toNNReal _ (sq_nonneg _)

theorem geometry_colors_independent (ε : ℝ) :
    IndepFun (fun ω : Sample => ω.1) (fun ω : Sample => ω.2) (sampleLaw ε) := by
  exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id

theorem sampleLaw_color_marginal (ε : ℝ) :
    (sampleLaw ε).map (fun ω : Sample => ω.2) = colorLaw := by
  exact measurePreserving_snd.map_eq

theorem sampleLaw_geometry_marginal (ε : ℝ) :
    (sampleLaw ε).map (fun ω : Sample => ω.1) = geometryLaw ε := by
  exact measurePreserving_fst.map_eq

theorem counts_independent (ε : ℝ) :
    iIndepFun (fun j : Box => fun N : Box → ℕ => N j) (countLaw ε) := by
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem colors_independent :
    iIndepFun (fun i : Slot => fun χ : Slot → Bool => χ i) colorLaw := by
  exact iIndepFun_infinitePi (fun _ => measurable_id)

theorem fairColor_singleton (b : Bool) : fairColor {b} = (1 / 2 : ℝ≥0∞) := by
  rw [fairColor, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply]
  norm_num

theorem colorLaw_singleton (i : Slot) (b : Bool) :
    colorLaw {χ | χ i = b} = (1 / 2 : ℝ≥0∞) := by
  rw [← fairColor_singleton b, ← colorLaw_marginal i]
  exact (Measure.map_apply (by fun_prop) (measurableSet_singleton b)).symm

lemma cardyWeight_complex {u : ℝ} (hu : u ∈ Icc 0 1) :
    (cardyWeight u : ℂ) =
      (u : ℂ) ^ ((1 / 3 : ℂ) - 1) * (1 - (u : ℂ)) ^ ((1 / 3 : ℂ) - 1) := by
  have h₁ : (1 / 3 : ℂ) - 1 = ((-(2 : ℝ) / 3 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [cardyWeight, Real.mul_rpow hu.1 (sub_nonneg.mpr hu.2),
    Complex.ofReal_mul, Complex.ofReal_cpow hu.1,
    Complex.ofReal_cpow (sub_nonneg.mpr hu.2), h₁]
  push_cast
  rfl

theorem cardyDenominator_eq_beta :
    ((∫ u in 0..1, cardyWeight u : ℝ) : ℂ) =
      Complex.betaIntegral (1 / 3) (1 / 3) := by
  rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro u hu
  exact cardyWeight_complex (by simpa only [uIcc_of_le zero_le_one] using hu)

theorem cardyDenominator_eq_gamma :
    (∫ u in 0..1, cardyWeight u) =
      Real.Gamma (1 / 3) ^ 2 / Real.Gamma (2 / 3) := by
  apply Complex.ofReal_injective
  rw [cardyDenominator_eq_beta,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ (by norm_num) (by norm_num)]
  have h : (1 / 3 : ℂ) + 1 / 3 = 2 / 3 := by norm_num
  rw [h]
  rw [show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by norm_num,
    show (2 / 3 : ℂ) = ((2 / 3 : ℝ) : ℂ) by norm_num,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  push_cast
  ring

theorem cardyDenominator_pos : 0 < ∫ u in 0..1, cardyWeight u := by
  rw [cardyDenominator_eq_gamma]
  exact div_pos (pow_pos (Real.Gamma_pos_of_pos (by norm_num)) _)
    (Real.Gamma_pos_of_pos (by norm_num))

@[simp] theorem cardyIntegral_zero : cardyIntegral 0 = 0 := by
  simp [cardyIntegral]

@[simp] theorem cardyIntegral_one : cardyIntegral 1 = 1 := by
  exact div_self (ne_of_gt cardyDenominator_pos)

theorem cardyWeight_integrable : IntervalIntegrable cardyWeight volume 0 1 := by
  have h := Complex.betaIntegral_convergent
    (u := (1 / 3 : ℂ)) (v := (1 / 3 : ℂ)) (by norm_num) (by norm_num)
  have h' : IntervalIntegrable (fun u : ℝ =>
      ((u : ℂ) ^ ((1 / 3 : ℂ) - 1) *
        (1 - (u : ℂ)) ^ ((1 / 3 : ℂ) - 1)).re) volume 0 1 := ⟨h.1.re, h.2.re⟩
  refine IntervalIntegrable.congr ?_ h'
  intro u hu
  have hu' : u ∈ Icc (0 : ℝ) 1 := by
    exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le zero_le_one] using hu)
  simpa only [Complex.ofReal_re] using congrArg Complex.re (cardyWeight_complex hu').symm

theorem cardyWeight_integrable_subinterval {s t : ℝ} (hs : 0 ≤ s)
    (ht : t ≤ 1) (hst : s ≤ t) : IntervalIntegrable cardyWeight volume s t := by
  apply cardyWeight_integrable.mono_set
  rw [uIcc_of_le hst, uIcc_of_le zero_le_one]
  exact Icc_subset_Icc hs ht

theorem cardyWeight_nonneg {u : ℝ} (hu : u ∈ Icc 0 1) : 0 ≤ cardyWeight u := by
  exact Real.rpow_nonneg (mul_nonneg hu.1 (sub_nonneg.mpr hu.2)) _

theorem cardyWeight_pos {u : ℝ} (hu : u ∈ Ioo 0 1) : 0 < cardyWeight u := by
  exact Real.rpow_pos_of_pos (mul_pos hu.1 (sub_pos.mpr hu.2)) _

lemma cardyWeight_symm (u : ℝ) : cardyWeight (1 - u) = cardyWeight u := by
  unfold cardyWeight
  congr 1
  ring

theorem cardyIntegral_continuousOn : ContinuousOn cardyIntegral (Icc 0 1) := by
  have h := intervalIntegral.continuousOn_primitive_interval
    ((intervalIntegrable_iff' (by finiteness)).mp cardyWeight_integrable)
  rw [uIcc_of_le zero_le_one] at h
  exact h.div_const _

theorem cardyIntegral_strictMonoOn : StrictMonoOn cardyIntegral (Icc 0 1) := by
  intro a ha b hb hab
  have h0a := cardyWeight_integrable_subinterval (s := 0) le_rfl ha.2 ha.1
  have habi := cardyWeight_integrable_subinterval ha.1 hb.2 hab.le
  have hp : 0 < ∫ u in a..b, cardyWeight u := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on habi _ hab
    intro u hu
    exact cardyWeight_pos ⟨ha.1.trans_lt hu.1, hu.2.trans_le hb.2⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0a habi
  apply (div_lt_div_iff_of_pos_right cardyDenominator_pos).mpr
  linarith

theorem cardyIntegral_mem_Icc {x : ℝ} (hx : x ∈ Icc 0 1) :
    cardyIntegral x ∈ Icc 0 1 := by
  have h := cardyIntegral_strictMonoOn.monotoneOn
  constructor
  · simpa using h (show (0 : ℝ) ∈ Icc 0 1 by simp) hx hx.1
  · simpa using h hx (show (1 : ℝ) ∈ Icc 0 1 by simp) hx.2

theorem cardyIntegral_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 1) :
    cardyIntegral x ∈ Ioo 0 1 := by
  constructor
  · simpa using cardyIntegral_strictMonoOn (show (0 : ℝ) ∈ Icc 0 1 by simp)
      ⟨hx.1.le, hx.2.le⟩ hx.1
  · simpa using cardyIntegral_strictMonoOn ⟨hx.1.le, hx.2.le⟩
      (show (1 : ℝ) ∈ Icc 0 1 by simp) hx.2

theorem cardyIntegral_reflection {x : ℝ} (hx : x ∈ Icc 0 1) :
    cardyIntegral (1 - x) = 1 - cardyIntegral x := by
  have hx' : 1 - x ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have h0 := cardyWeight_integrable_subinterval (s := 0) le_rfl hx'.2 hx'.1
  have h1 := cardyWeight_integrable_subinterval hx'.1 le_rfl hx'.2
  have hsub : (∫ u in 0..x, cardyWeight u) = ∫ u in (1 - x)..1, cardyWeight u := by
    simpa only [cardyWeight_symm, sub_zero] using
      intervalIntegral.integral_comp_sub_left (a := 0) (b := x) cardyWeight 1
  apply (eq_sub_iff_add_eq).mpr
  unfold cardyIntegral
  rw [← add_div, hsub, intervalIntegral.integral_add_adjacent_intervals h0 h1]
  exact div_self (ne_of_gt cardyDenominator_pos)

@[simp] theorem cardyIntegral_half : cardyIntegral (1 / 2) = 1 / 2 := by
  have h := cardyIntegral_reflection (x := 1 / 2) (by norm_num)
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h
  linarith

def cardyBinomialCoefficient (n : ℕ) : ℝ :=
  (n.factorial : ℝ)⁻¹ * (ascPochhammer ℝ n).eval (2 / 3)

lemma cardyBinomialCoefficient_pos (n : ℕ) : 0 < cardyBinomialCoefficient n := by
  exact mul_pos (inv_pos.mpr (by positivity)) (ascPochhammer_pos n _ (by norm_num))

lemma cardyBinomialCoefficient_eq_choose (n : ℕ) :
    cardyBinomialCoefficient n = Ring.choose ((2 / 3 : ℝ) + n - 1) n := by
  rw [← Ring.multichoose_eq]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (2 / 3 : ℝ) n
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
  rw [cardyBinomialCoefficient, ← h, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast n.factorial_ne_zero

lemma cardy_binomial_hasSum {u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasSum (fun n : ℕ => cardyBinomialCoefficient n * u ^ n)
      ((1 - u) ^ (-(2 : ℝ) / 3)) := by
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (2 / 3)).hasSum
    (y := u) (by
      rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
      simpa [Real.dist_eq, abs_of_pos hu.1] using hu.2)
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    ← cardyBinomialCoefficient_eq_choose, zero_add, one_div, neg_div,
    Real.rpow_neg (sub_pos.mpr hu.2).le]
    using h

lemma cardyWeight_hasSum {u : ℝ} (hu : u ∈ Ioo 0 1) :
    HasSum (fun n : ℕ => cardyBinomialCoefficient n * u ^ ((n : ℝ) - 2 / 3))
      (cardyWeight u) := by
  have h := (cardy_binomial_hasSum hu).mul_left (u ^ (-(2 : ℝ) / 3))
  have heq (n : ℕ) : cardyBinomialCoefficient n * u ^ ((n : ℝ) - 2 / 3) =
      u ^ (-(2 : ℝ) / 3) * (cardyBinomialCoefficient n * u ^ n) := by
    rw [show (n : ℝ) - 2 / 3 = -(2 : ℝ) / 3 + n by ring,
      Real.rpow_add hu.1, Real.rpow_natCast]
    ring
  simpa only [heq, cardyWeight, Real.mul_rpow hu.1.le (sub_pos.mpr hu.2).le] using h

theorem cardyNumerator_hasSum {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasSum (fun n : ℕ => ∫ u in 0..x,
      cardyBinomialCoefficient n * u ^ ((n : ℝ) - 2 / 3))
      (∫ u in 0..x, cardyWeight u) := by
  let S : ℕ → ℝ → ℝ := fun n u =>
    cardyBinomialCoefficient n * u ^ ((n : ℝ) - 2 / 3)
  have hpoint {u : ℝ} (hu : u ∈ uIoc 0 x) : HasSum (fun n => S n u) (cardyWeight u) := by
    rw [uIoc_of_le hx.1.le] at hu
    exact cardyWeight_hasSum ⟨hu.1, hu.2.trans_lt hx.2⟩
  have hi (n : ℕ) : IntervalIntegrable (S n) volume 0 x := by
    exact (intervalIntegral.intervalIntegrable_rpow'
      (r := (n : ℝ) - 2 / 3) (by linarith [Nat.cast_nonneg (α := ℝ) n])).const_mul _
  have htotal : IntervalIntegrable (fun u => ∑' n, S n u) volume 0 x := by
    apply IntervalIntegrable.congr (fun u hu => (hpoint hu).tsum_eq.symm)
    exact cardyWeight_integrable_subinterval le_rfl hx.2.le hx.1.le
  apply intervalIntegral.hasSum_integral_of_dominated_convergence S
    (fun n => ((intervalIntegrable_iff).mp (hi n)).1) ?_ ?_ htotal ?_
  · intro n
    refine Filter.Eventually.of_forall fun u hu => ?_
    rw [uIoc_of_le hx.1.le] at hu
    have hpos : 0 ≤ S n u :=
      mul_nonneg (cardyBinomialCoefficient_pos n).le (Real.rpow_nonneg hu.1.le _)
    exact (Real.norm_of_nonneg hpos).le
  · exact Filter.Eventually.of_forall fun u hu => (hpoint hu).summable
  · exact Filter.Eventually.of_forall fun u hu => hpoint hu

lemma cardyBinomialTerm_integral (x : ℝ) (n : ℕ) :
    (∫ u in 0..x, cardyBinomialCoefficient n * u ^ ((n : ℝ) - 2 / 3)) =
      cardyBinomialCoefficient n * x ^ ((n : ℝ) + 1 / 3) / ((n : ℝ) + 1 / 3) := by
  rw [intervalIntegral.integral_const_mul, integral_rpow
    (Or.inl (by linarith [Nat.cast_nonneg (α := ℝ) n]))]
  rw [show (n : ℝ) - 2 / 3 + 1 = (n : ℝ) + 1 / 3 by ring,
    Real.zero_rpow (by linarith [Nat.cast_nonneg (α := ℝ) n]), sub_zero]
  ring

lemma cardyHypergeometricCoefficient_eq (n : ℕ) :
    cardyBinomialCoefficient n / ((n : ℝ) + 1 / 3) =
      3 * ordinaryHypergeometricCoefficient (1 / 3 : ℝ) (2 / 3) (4 / 3) n := by
  have hc : (ascPochhammer ℝ n).eval (4 / 3) ≠ 0 :=
    ne_of_gt (ascPochhammer_pos n _ (by norm_num))
  have hn : (n : ℝ) + 1 / 3 ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hshift : (ascPochhammer ℝ n).eval (1 / 3) * ((1 / 3 : ℝ) + n) =
      (1 / 3 : ℝ) * (ascPochhammer ℝ n).eval (4 / 3) := by
    rw [← ascPochhammer_succ_eval, ascPochhammer_succ_left]
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
      Polynomial.eval_add, Polynomial.eval_one]
    norm_num
  have hratio : ((ascPochhammer ℝ n).eval (1 / 3) /
      (ascPochhammer ℝ n).eval (4 / 3)) * ((n : ℝ) + 1 / 3) = 1 / 3 := by
    calc
      _ = ((ascPochhammer ℝ n).eval (1 / 3) * ((1 / 3 : ℝ) + n)) /
          (ascPochhammer ℝ n).eval (4 / 3) := by ring
      _ = ((1 / 3 : ℝ) * (ascPochhammer ℝ n).eval (4 / 3)) /
          (ascPochhammer ℝ n).eval (4 / 3) := by rw [hshift]
      _ = 1 / 3 := mul_div_cancel_right₀ _ hc
  symm
  apply (eq_div_iff hn).mpr
  calc
    _ = (3 * (((ascPochhammer ℝ n).eval (1 / 3) /
          (ascPochhammer ℝ n).eval (4 / 3)) * ((n : ℝ) + 1 / 3))) *
        cardyBinomialCoefficient n := by
      unfold ordinaryHypergeometricCoefficient cardyBinomialCoefficient
      ring
    _ = cardyBinomialCoefficient n := by rw [hratio]; ring

theorem cardyNumerator_eq_hypergeometric {x : ℝ} (hx : x ∈ Ioo 0 1) :
    (∫ u in 0..x, cardyWeight u) =
      3 * x ^ ((1 : ℝ) / 3) *
        ordinaryHypergeometric (1 / 3 : ℝ) (2 / 3) (4 / 3) x := by
  rw [← (cardyNumerator_hasSum hx).tsum_eq, ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [cardyBinomialTerm_integral, Real.rpow_add hx.1, Real.rpow_natCast]
  calc
    _ = (cardyBinomialCoefficient n / ((n : ℝ) + 1 / 3)) *
        (x ^ n * x ^ ((1 : ℝ) / 3)) := by ring
    _ = _ := by rw [cardyHypergeometricCoefficient_eq]; ring

theorem cardyIntegral_eq_hypergeometric {x : ℝ} (hx : x ∈ Ioo 0 1) :
    cardyIntegral x = cardyHypergeometric x := by
  have hγ : Real.Gamma (4 / 3) = (1 / 3 : ℝ) * Real.Gamma (1 / 3) := by
    convert Real.Gamma_add_one (s := 1 / 3) (by norm_num) using 1
    norm_num
  have h₁ : Real.Gamma (1 / 3) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  have h₂ : Real.Gamma (2 / 3) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by norm_num))
  rw [cardyIntegral, cardyNumerator_eq_hypergeometric hx,
    cardyDenominator_eq_gamma, cardyHypergeometric, hγ]
  field_simp

end Cardy

end

end OAI

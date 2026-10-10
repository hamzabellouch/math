import Mathlib
import OAI.Analysis.CoulombRadii.RadialBounds.SpatialAnnulus
import OAI.Analysis.CoulombRadii.RandomFields.ConditionalDensity
import OAI.Analysis.CoulombRadii.FieldAnalysis.Field

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology BigOperators ContDiff Convolution Pointwise ENNReal
namespace NeutralAtom

theorem packetMass_annulus_localization {n : ℕ} (g : Position → ℝ)
    (hgnorm : (∫ y, g y^2) = 1) (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0)
    {c₁ r₀ s a b : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (ha : 0 < a) (hab : a < b)
    (hδ : c₁*s^packetExponent < 1/2)
    (hclamp : (1+c₁*s^packetExponent)*r₀ ≤ a*s)
    (x : Configuration n) :
    packetMass g c₁ r₀ s (spatialAnnulus (a*s) (b*s)) x ≤
      rawCount (spatialAnnulus ((a/2)*s) ((2*b)*s)) x := by
  have hdpos : 0 < c₁*s^packetExponent := mul_pos hc (Real.rpow_pos_of_pos hs _)
  have hb : 0 < b := ha.trans hab
  apply packetMass_le_rawCount g hgnorm hc hr hs
  intro z y hy hK
  change a*s < ‖y‖ ∧ ‖y‖ < b*s at hy
  have hz : r₀ ≤ ‖z‖ := by
    by_contra! hz
    have hyc := packetKernel_clamped_support g hgsupp hc hr hs z y hz.le hK
    linarith
  obtain ⟨hl,hu⟩ := packetKernel_relative_support g hgsupp hc hr hs z y hz hK
  change (a/2)*s < ‖z‖ ∧ ‖z‖ < (2*b)*s
  constructor
  · have hn := norm_nonneg z
    have hsmall : (c₁*s^packetExponent)*‖z‖ < ‖z‖ :=
      mul_lt_of_lt_one_left (hr.trans_le hz) (by linarith)
    nlinarith
  · have hlarge : ‖z‖/2 < (1-c₁*s^packetExponent)*‖z‖ := by
      nlinarith [mul_pos (show 0 < 1/2-c₁*s^packetExponent by linarith) (hr.trans_le hz)]
    nlinarith

theorem packet_relative_width_tendsto {s : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0))
    (c₁ : ℝ) : Tendsto (fun n => c₁*s n^packetExponent) atTop (𝓝 0) := by
  simpa using (hs.rpow_const_nhds_zero (by norm_num [packetExponent])).const_mul c₁

theorem packet_clamp_tendsto {s r₀ : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0))
    (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0)) (c₁ : ℝ) :
    Tendsto (fun n => ((1+c₁*s n^packetExponent)*r₀ n)/s n) atTop (𝓝 0) := by
  simpa only [mul_zero, add_zero, one_mul, mul_div_assoc] using
    (tendsto_const_nhds.add (packet_relative_width_tendsto hs c₁)).mul hr

theorem eventually_packet_localization {s r₀ : ℕ → ℝ} (N : ℕ → ℕ)
    (g : Position → ℝ) (hgnorm : (∫ y, g y^2) = 1)
    (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ a b : ℝ}
    (hc : 0 < c₁) (ha : 0 < a) (hab : a < b)
    (hsp : ∀ᶠ n in atTop, 0 < s n) (hrp : ∀ᶠ n in atTop, 0 < r₀ n)
    (hs : Tendsto s atTop (𝓝 0))
    (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ x : Configuration (N n),
      packetMass g c₁ (r₀ n) (s n) (spatialAnnulus (a*s n) (b*s n)) x ≤
        rawCount (spatialAnnulus ((a/2)*s n) ((2*b)*s n)) x := by
  filter_upwards [hsp, hrp,
    (packet_relative_width_tendsto hs c₁).eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
    (packet_clamp_tendsto hs hr c₁).eventually_lt_const ha] with n hsn hrn hδ hcl
  intro x
  exact packetMass_annulus_localization g hgnorm hgsupp hc hrn hsn ha hab hδ
    ((div_lt_iff₀ hsn).mp hcl).le x

theorem eventually_packet_sandwich {s r₀ : ℕ → ℝ} (N : ℕ → ℕ)
    (g : Position → ℝ) (hgnorm : (∫ y, g y^2) = 1)
    (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ a b η : ℝ}
    (hc : 0 < c₁) (ha : 0 < a) (hab : a < b) (hη : 0 < η) (hηa : η < a)
    (hsp : ∀ᶠ n in atTop, 0 < s n) (hrp : ∀ᶠ n in atTop, 0 < r₀ n)
    (hs : Tendsto s atTop (𝓝 0))
    (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ x : Configuration (N n),
      packetMass g c₁ (r₀ n) (s n) (spatialAnnulus ((a+η)*s n) ((b-η)*s n)) x ≤
        rawCount (spatialAnnulus (a*s n) (b*s n)) x ∧
      rawCount (spatialAnnulus (a*s n) (b*s n)) x ≤
        packetMass g c₁ (r₀ n) (s n) (spatialAnnulus ((a-η)*s n) ((b+η)*s n)) x := by
  have hd : Tendsto (fun n => (c₁*s n^packetExponent)*b) atTop (𝓝 0) := by
    simpa using (packet_relative_width_tendsto hs c₁).mul_const b
  filter_upwards [hsp, hrp, hd.eventually_lt_const hη,
    (packet_clamp_tendsto hs hr c₁).eventually_lt_const (sub_pos.mpr hηa)]
    with n hsn hrn hδ hcl x
  exact packetMass_annulus_sandwich g hgnorm hgsupp hc hrn hsn ha hab hη hηa hδ
    ((div_lt_iff₀ hsn).mp hcl).le x

theorem nuclear_clamp_ratio {Z s ε : ℝ} (hZ : 0 < Z) (hs : 0 < s) :
    (ε * Z^(-(1/3:ℝ)))/s = ε * (Z*s^3)^(-(1/3:ℝ)) := by
  rw [Real.mul_rpow hZ.le (pow_nonneg hs.le 3),
    ← Real.rpow_natCast_mul hs.le 3 (-(1/3:ℝ))]
  norm_num [Real.rpow_neg_one]
  ring

theorem nuclear_clamp_tendsto {Z s : ℕ → ℝ} (hZ : ∀ᶠ n in atTop, 0 < Z n)
    (hs : ∀ᶠ n in atTop, 0 < s n)
    (hmass : Tendsto (fun n => Z n*s n^3) atTop atTop) (ε : ℝ) :
    Tendsto (fun n => (ε*(Z n)^(-(1/3:ℝ)))/s n) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).comp hmass).const_mul ε
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [hZ,hs] with n hzn hsn
  exact (nuclear_clamp_ratio hzn hsn).symm

theorem tendsto_of_parameter_sandwich {α β : Type*} {l : Filter α} {p : Filter β}
    [p.NeBot] {f : α → ℝ} {g h : β → α → ℝ} {a b : β → ℝ} {L : ℝ}
    (ha : Tendsto a p (𝓝 L)) (hb : Tendsto b p (𝓝 L))
    (hs : ∀ᶠ t in p,
      Tendsto (g t) l (𝓝 (a t)) ∧ Tendsto (h t) l (𝓝 (b t)) ∧
      ∀ᶠ n in l, g t n ≤ f n ∧ f n ≤ h t n) :
    Tendsto f l (𝓝 L) := by
  apply tendsto_order.mpr
  constructor
  · intro x hx
    obtain ⟨t,ht,hs'⟩ := (ha.eventually (lt_mem_nhds hx) |>.and hs).exists
    filter_upwards [hs'.1.eventually (lt_mem_nhds ht), hs'.2.2] with n hn hn'
    exact hn.trans_le hn'.1
  · intro x hx
    obtain ⟨t,ht,hs'⟩ := (hb.eventually (gt_mem_nhds hx) |>.and hs).exists
    filter_upwards [hs'.2.1.eventually (gt_mem_nhds ht), hs'.2.2] with n hn hn'
    exact hn'.2.trans_lt hn

theorem raw_annulus_tendsto_of_packet_sandwich
    {T : ℕ → ℝ → ℝ → ℝ} {N : ℕ → ℝ} {a b C : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hT : ∀ u v : ℝ, 0 < u → u < v →
      Tendsto (fun n => T n u v) atTop (𝓝 (C/u^3-C/v^3)))
    (hs : ∀ η : ℝ, 0 < η → η < min a ((b-a)/2) →
      ∀ᶠ n in atTop, T n (a+η) (b-η) ≤ N n ∧ N n ≤ T n (a-η) (b+η)) :
    Tendsto N atTop (𝓝 (C/a^3-C/b^3)) := by
  have hb : 0 < b := ha.trans hab
  apply tendsto_of_parameter_sandwich (p := 𝓝[>] (0 : ℝ))
    (g := fun η n => T n (a+η) (b-η)) (h := fun η n => T n (a-η) (b+η))
    (a := fun η => C/(a+η)^3-C/(b-η)^3)
    (b := fun η => C/(a-η)^3-C/(b+η)^3)
  · have hcont : ContinuousAt (fun η : ℝ => C/(a+η)^3-C/(b-η)^3) 0 := by
      fun_prop (disch := positivity)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · have hcont : ContinuousAt (fun η : ℝ => C/(a-η)^3-C/(b+η)^3) 0 := by
      fun_prop (disch := positivity)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  · have hm : 0 < min a ((b-a)/2) := lt_min ha (by linarith)
    filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds hm : ∀ᶠ η : ℝ in 𝓝 0, η < min a ((b-a)/2)).filter_mono nhdsWithin_le_nhds]
      with η hη hηm
    have hη0 : 0 < η := hη
    have hηa : η < a := hηm.trans_le (min_le_left _ _)
    have hηab : η < (b-a)/2 := hηm.trans_le (min_le_right _ _)
    exact ⟨hT _ _ (by linarith) (by linarith),
      hT _ _ (by linarith) (by linarith), hs η hη0 hηm⟩

theorem rawCount_memLp_measure {n : ℕ} (μ : Measure (Configuration n))
    [IsFiniteMeasure μ] {S : Set Position} (hS : MeasurableSet S) :
    MemLp (rawCount (n := n) S) 2 μ := by
  apply MemLp.of_bound (measurable_rawCount hS).aestronglyMeasurable (n : ℝ)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (rawCount_nonneg S x)] using rawCount_le_number S x

theorem expected_raw_annulus_of_packets {s r₀ : ℕ → ℝ} (N : ℕ → ℕ)
    (μ : ∀ n, Measure (Configuration (N n))) [∀ n, IsFiniteMeasure (μ n)]
    (g : Position → ℝ) (hg : Continuous g) (hgnorm : (∫ y, g y^2) = 1)
    (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ a b C : ℝ}
    (hc : 0 < c₁) (ha : 0 < a) (hab : a < b)
    (hsp : ∀ᶠ n in atTop, 0 < s n) (hrp : ∀ᶠ n in atTop, 0 < r₀ n)
    (hs : Tendsto s atTop (𝓝 0))
    (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0))
    (hpacket : ∀ u v : ℝ, 0 < u → u < v →
      Tendsto (fun n => s n^3 * ∫ x,
        packetMass g c₁ (r₀ n) (s n) (spatialAnnulus (u*s n) (v*s n)) x ∂μ n)
        atTop (𝓝 (C/u^3-C/v^3))) :
    Tendsto (fun n => s n^3 * ∫ x,
      rawCount (spatialAnnulus (a*s n) (b*s n)) x ∂μ n)
      atTop (𝓝 (C/a^3-C/b^3)) := by
  apply raw_annulus_tendsto_of_packet_sandwich ha hab hpacket
  intro η hη hηm
  have hηa := hηm.trans_le (min_le_left _ _)
  filter_upwards [hsp, hrp,
    eventually_packet_sandwich N g hgnorm hgsupp hc ha hab hη hηa hsp hrp hs hr]
    with n hsn hrn hsan
  have hraw := (rawCount_memLp_measure (μ n)
    (measurableSet_spatialAnnulus (a*s n) (b*s n))).integrable (by norm_num)
  have hlow := (packetMass_memLp hg hgnorm hc hrn hsn
    (spatialAnnulus ((a+η)*s n) ((b-η)*s n)) (μ n)).integrable (by norm_num)
  have hhigh := (packetMass_memLp hg hgnorm hc hrn hsn
    (spatialAnnulus ((a-η)*s n) ((b+η)*s n)) (μ n)).integrable (by norm_num)
  exact ⟨mul_le_mul_of_nonneg_left (integral_mono hlow hraw (fun x => (hsan x).1))
      (pow_nonneg hsn.le 3),
    mul_le_mul_of_nonneg_left (integral_mono hraw hhigh (fun x => (hsan x).2))
      (pow_nonneg hsn.le 3)⟩

theorem conditional_mass_l2 {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {X Y : Ω → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hX : MemLp X 2 μ) (hX0 : 0 ≤ᵐ[μ] X)
    (hY : AEStronglyMeasurable (m := m₀) Y μ) (hY0 : 0 ≤ᵐ[μ] Y)
    (hYX : Y ≤ᵐ[μ] c • μ[X | m]) :
    MemLp Y 2 μ ∧ Real.sqrt (∫ z, Y z ^ 2 ∂μ) ≤
      c * Real.sqrt (∫ z, X z ^ 2 ∂μ) := by
  have hcond := hX.condExp (m := m) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcond0 : 0 ≤ᵐ[μ] μ[X | m] := condExp_nonneg hX0
  have hdom : MemLp (c • μ[X | m]) 2 μ := hcond.const_smul c
  have hY2 : MemLp Y 2 μ := hdom.mono' hY (by
    filter_upwards [hY0, hYX] with z hz hzx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using hzx)
  refine ⟨hY2, ?_⟩
  have hsq : (∫ z, Y z ^ 2 ∂μ) ≤ c^2 * (∫ z, X z ^ 2 ∂μ) := by
    calc
      (∫ z, Y z ^ 2 ∂μ) ≤ ∫ z, (c * μ[X | m] z)^2 ∂μ := by
        apply integral_mono_ae hY2.integrable_sq hdom.integrable_sq
        filter_upwards [hY0, hYX, hcond0] with z hz hzx hx
        exact pow_le_pow_left₀ hz hzx 2
      _ = c^2 * (∫ z, μ[X | m] z ^ 2 ∂μ) := by
        simp_rw [mul_pow]
        rw [integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left (conditional_integral_square_le (m₀ := m₀) (m := m) μ hm hX)
        (sq_nonneg c)
  calc
    Real.sqrt (∫ z, Y z ^ 2 ∂μ) ≤ Real.sqrt (c^2 * (∫ z, X z^2 ∂μ)) :=
      Real.sqrt_le_sqrt hsq
    _ = c * Real.sqrt (∫ z, X z^2 ∂μ) := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem expectation_of_conditional_mass {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {X Y : Ω → ℝ} (_hX : Integrable X μ) {c : ℝ}
    (hY : Y =ᵐ[μ] c • μ[X | m]) :
    (∫ z, Y z ∂μ) = c * ∫ z, X z ∂μ := by
  rw [integral_congr_ae hY]
  change (∫ z, c * μ[X | m] z ∂μ) = _
  rw [integral_const_mul, integral_condExp hm]

theorem scaled_count_l2_bound {s D C X Y : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hYX : Y ≤ s^3 * X)
    (hX : X ≤ C*(max (s^3)⁻¹ 1 + Real.sqrt (D*s))) :
    Y ≤ C*(1+Real.sqrt D) := by
  have hs3 : 0 < s^3 := pow_pos hs 3
  have hs3le : s^3 ≤ 1 := pow_le_one₀ hs.le hs1
  have hi : 1 ≤ (s^3)⁻¹ := (one_le_inv₀ hs3).mpr hs3le
  have hsq : Real.sqrt (D*s) ≤ Real.sqrt D :=
    Real.sqrt_le_sqrt (mul_le_of_le_one_right hD hs1)
  have hsm : s^3 * Real.sqrt (D*s) ≤ Real.sqrt D := by
    calc
      s^3 * Real.sqrt (D*s) ≤ 1 * Real.sqrt (D*s) :=
        mul_le_mul_of_nonneg_right hs3le (Real.sqrt_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using hsq
  calc
    Y ≤ s^3 * (C*(max (s^3)⁻¹ 1 + Real.sqrt (D*s))) :=
      hYX.trans (mul_le_mul_of_nonneg_left hX hs3.le)
    _ = C * (1+s^3*Real.sqrt (D*s)) := by
      rw [max_eq_left hi]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl hsm) hC

theorem integral_comp_measurePreserving {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
    {X : Ω → Ξ} (hX : MeasurePreserving X μ ν) {f : Ξ → ℝ}
    (hf : AEStronglyMeasurable f ν) :
    (∫ z, f (X z) ∂μ) = ∫ x, f x ∂ν := by
  rw [← hX.map_eq] at hf ⊢
  exact (integral_map hX.aemeasurable hf).symm

theorem conditional_packet_memLp {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (_hm : m ≤ m₀) {n : ℕ} (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    (X : Ω → Configuration n) (hX : @MeasurePreserving Ω (Configuration n) m₀ inferInstance X μ ν)
    {g : Position → ℝ} (hg : Continuous g) (hgnorm : (∫ y, g y^2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S : Set Position) {Y : Ω → ℝ}
    (hY : Y =ᵐ[μ] (s^3) • μ[(fun z => packetMass g c₁ r₀ s S (X z)) | m]) :
    MemLp Y 2 μ := by
  let : MeasurableSpace Ω := m₀
  have hP := (packetMass_memLp hg hgnorm hc hr hs S ν).comp_measurePreserving hX
  exact (memLp_congr_ae hY).mpr
    ((hP.condExp (m := m) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_smul (s^3))

theorem conditional_packet_l2_bound {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {n : ℕ} (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    (X : Ω → Configuration n) (hX : @MeasurePreserving Ω (Configuration n) m₀ inferInstance X μ ν)
    {g : Position → ℝ} (hg : Continuous g) (hgnorm : (∫ y, g y^2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S T : Set Position) (hT : MeasurableSet T)
    (hloc : ∀ x : Configuration n, packetMass g c₁ r₀ s S x ≤ rawCount T x)
    {Y : Ω → ℝ}
    (hY : Y =ᵐ[μ] (s^3) • μ[(fun z => packetMass g c₁ r₀ s S (X z)) | m]) :
    MemLp Y 2 μ ∧ Real.sqrt (∫ z, Y z^2 ∂μ) ≤
      s^3 * Real.sqrt (∫ x, (rawCount T x)^2 ∂ν) := by
  let : MeasurableSpace Ω := m₀
  have hP₀ := packetMass_memLp hg hgnorm hc hr hs S ν
  have hP := hP₀.comp_measurePreserving hX
  have hN₀ := rawCount_memLp_measure ν hT
  have hN := hN₀.comp_measurePreserving hX
  have hY2 := conditional_packet_memLp μ hm ν X hX hg hgnorm hc hr hs S hY
  have hP0 : 0 ≤ᵐ[μ] (fun z => packetMass g c₁ r₀ s S (X z)) :=
    Eventually.of_forall fun z => packetMass_nonneg g hc hr hs S (X z)
  have hY0 : 0 ≤ᵐ[μ] Y := by
    filter_upwards [hY, condExp_nonneg (m := m) hP0] with z hz hpz
    rw [hz]
    exact mul_nonneg (pow_nonneg hs.le 3) hpz
  have hYN : Y ≤ᵐ[μ] (s^3) • μ[(fun z => rawCount T (X z)) | m] := by
    have hh := condExp_mono (m := m) (hP.integrable (by norm_num))
      (hN.integrable (by norm_num)) (Eventually.of_forall (fun z => hloc (X z)))
    filter_upwards [hY,hh] with z hz hhz
    rw [hz]
    exact mul_le_mul_of_nonneg_left hhz (pow_nonneg hs.le 3)
  have hh := conditional_mass_l2 (m₀ := m₀) (m := m) μ hm (pow_nonneg hs.le 3) hN
    (Eventually.of_forall fun z => rawCount_nonneg T (X z)) hY2.aestronglyMeasurable hY0 hYN
  have hi := integral_comp_measurePreserving hX hN₀.integrable_sq.aestronglyMeasurable
  exact ⟨hh.1, by simpa only [Function.comp_apply, hi] using hh.2⟩

theorem expected_conditional_packet {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {n : ℕ} (ν : Measure (Configuration n)) [IsFiniteMeasure ν]
    (X : Ω → Configuration n) (hX : @MeasurePreserving Ω (Configuration n) m₀ inferInstance X μ ν)
    {g : Position → ℝ} (hg : Continuous g) (hgnorm : (∫ y, g y^2) = 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    (S : Set Position) {Y : Ω → ℝ}
    (hY : Y =ᵐ[μ] (s^3) • μ[(fun z => packetMass g c₁ r₀ s S (X z)) | m]) :
    (∫ z, Y z ∂μ) = s^3 * ∫ x, packetMass g c₁ r₀ s S x ∂ν := by
  let : MeasurableSpace Ω := m₀
  have hP₀ := packetMass_memLp hg hgnorm hc hr hs S ν
  rw [expectation_of_conditional_mass μ hm
    ((hP₀.comp_measurePreserving hX).integrable (by norm_num)) hY]
  simp only [Function.comp_apply]
  rw [integral_comp_measurePreserving hX hP₀.aestronglyMeasurable]

theorem expected_packet_annulus_from_retained {Ω : ℕ → Type*}
    [m₀ : ∀ n, MeasurableSpace (Ω n)] (μ : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (μ n)] (m : ∀ n, MeasurableSpace (Ω n))
    (hm : ∀ n, m n ≤ m₀ n) (N : ℕ → ℕ)
    (ν : ∀ n, Measure (Configuration (N n))) [∀ n, IsFiniteMeasure (ν n)]
    (X : ∀ n, Ω n → Configuration (N n))
    (hX : ∀ n, @MeasurePreserving (Ω n) (Configuration (N n)) (m₀ n) inferInstance (X n) (μ n) (ν n))
    (s r₀ : ℕ → ℝ) (hsp : ∀ n, 0 < s n) (hrp : ∀ n, 0 < r₀ n)
    (hs : Tendsto s atTop (𝓝 0)) (hr : Tendsto (fun n => r₀ n/s n) atTop (𝓝 0))
    (g : Position → ℝ) (hg : Continuous g) (hgnorm : (∫ y, g y^2) = 1)
    (hgsupp : ∀ x, 1 < ‖x‖ → g x = 0) {c₁ D : ℝ} (hc : 0 < c₁) (hD : 0 ≤ D)
    {G : ∀ n, Set (Ω n)} (hG : ∀ n, MeasurableSet[m₀ n] (G n))
    (hbad : Tendsto (fun n => (μ n).real (G n)ᶜ) atTop (𝓝 0))
    (d : RetainedAnalyticFamily (fun n => G n))
    (σ : ∀ n, Ω n → Position → ℝ) (hσ : ∀ n (θ : G n), σ n θ = d.σ n θ)
    (hcond : ∀ n a b, 0 < a → a < b →
      (fun z => ∫ x in spatialAnnulus a b, σ n z x) =ᵐ[μ n]
        s n^3 • (μ n)[(fun z => packetMass g c₁ (r₀ n) (s n)
          (spatialAnnulus (a*s n) (b*s n)) (X n z)) | m n])
    (hcount : ∀ a b, 0 < a → a < b → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, Real.sqrt (∫ x,
        (rawCount (spatialAnnulus (a*s n) (b*s n)) x)^2 ∂ν n) ≤
          C*(max (s n^3)⁻¹ 1 + Real.sqrt (D*s n)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n => s n^3 * ∫ x, packetMass g c₁ (r₀ n) (s n)
      (spatialAnnulus (a*s n) (b*s n)) x ∂ν n)
      atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3)) := by
  let : ∀ n, MeasurableSpace (Ω n) := m₀
  let Y : ∀ n, Ω n → ℝ := fun n z => ∫ x in spatialAnnulus a b, σ n z x
  have hY : ∀ n, MemLp (Y n) 2 (μ n) := fun n =>
    conditional_packet_memLp (μ n) (hm n) (ν n) (X n) (hX n) hg hgnorm hc
      (hrp n) (hsp n) _ (hcond n a b ha hab)
  have hY0 : ∀ n, 0 ≤ᵐ[μ n] Y n := by
    intro n
    have hp : 0 ≤ᵐ[μ n] (fun z => packetMass g c₁ (r₀ n) (s n)
        (spatialAnnulus (a*s n) (b*s n)) (X n z)) := Eventually.of_forall fun z =>
          packetMass_nonneg g hc (hrp n) (hsp n) _ (X n z)
    filter_upwards [hcond n a b ha hab, condExp_nonneg (m := m n) hp] with z hz hpz
    change 0 ≤ Y n z
    change Y n z = _ at hz
    rw [hz]
    exact mul_nonneg (pow_nonneg (hsp n).le 3) hpz
  obtain ⟨C,hC,hcb⟩ := hcount (a/2) (2*b) (by linarith) (by linarith)
  have hL2 : ∀ᶠ n in atTop, Real.sqrt (∫ z, (Y n z)^2 ∂μ n) ≤ C*(1+Real.sqrt D) := by
    filter_upwards [hcb, hs.eventually_lt_const (by norm_num : (0:ℝ) < 1),
      eventually_packet_localization N g hgnorm hgsupp hc ha hab
        (Eventually.of_forall hsp) (Eventually.of_forall hrp) hs hr]
      with n hn hs1 hloc
    have hh := conditional_packet_l2_bound (μ n) (hm n) (ν n) (X n) (hX n)
      hg hgnorm hc (hrp n) (hsp n) _ _ (measurableSet_spatialAnnulus _ _) hloc
      (hcond n a b ha hab)
    exact scaled_count_l2_bound (hsp n) hs1.le hD hC hh.2 hn
  have hh := d.expected_annulus μ σ hσ ha hab hY hY0 hG hL2 hbad
  apply hh.congr'
  filter_upwards [] with n
  exact expected_conditional_packet (μ n) (hm n) (ν n) (X n) (hX n)
    hg hgnorm hc (hrp n) (hsp n) _ (hcond n a b ha hab)

end NeutralAtom
end

end

end OAI

import Mathlib

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber.Herglotz

section Density
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]


def densityMeasure (f : C(X, ℝ)) : FiniteMeasure X :=
  ⟨μ.withDensity (fun x => ENNReal.ofReal (f x)),
    isFiniteMeasure_withDensity
      (f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace f)).lintegral_lt_top.ne⟩

theorem integral_densityMeasure (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) (g : X → ℝ) :
    (∫ x, g x ∂(densityMeasure μ f : Measure X)) = ∫ x, f x * g x ∂μ := by
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (f x)) from
      ENNReal.measurable_ofReal.comp f.continuous.measurable)
    (by simp : ∀ᵐ x ∂μ, ENNReal.ofReal (f x) < ∞)]
  simp only [ENNReal.toReal_ofReal (hf _), smul_eq_mul]

theorem mass_densityMeasure (f : C(X, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ((densityMeasure μ f).mass : ℝ) = ∫ x, f x ∂μ := by
  have h := integral_densityMeasure μ f hf (fun _ => 1)
  simpa only [integral_const, smul_eq_mul, mul_one, FiniteMeasure.measureReal_eq_coe_coeFn,
    FiniteMeasure.mass] using h
end Density

section WeakIntegral
variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [CompactSpace X]

theorem tendsto_integral_varying {ι : Type*} {l : Filter ι}
    {μs : ι → FiniteMeasure X} {μ : FiniteMeasure X}
    {fs : ι → C(X, ℝ)} {f : C(X, ℝ)}
    (hμ : Tendsto μs l (𝓝 μ)) (hf : Tendsto fs l (𝓝 f)) :
    Tendsto (fun i => ∫ x, fs i x ∂(μs i : Measure X)) l
      (𝓝 (∫ x, f x ∂(μ : Measure X))) := by
  have hfixed := (FiniteMeasure.continuous_integral_continuousMap f).continuousAt.tendsto.comp hμ
  have hmass : Tendsto (fun i => ((μs i).mass : ℝ)) l (𝓝 (μ.mass : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      (FiniteMeasure.continuous_mass.continuousAt.tendsto.comp hμ)
  have hnorm : Tendsto (fun i => ‖fs i - f‖) l (𝓝 0) := by
    simpa using (hf.sub (tendsto_const_nhds (x := f))).norm
  have hdiff : Tendsto (fun i => ∫ x, (fs i - f) x ∂(μs i : Measure X)) l (𝓝 0) := by
    refine squeeze_zero_norm (fun i => ?_) (by simpa using hnorm.mul hmass)
    simpa only [FiniteMeasure.measureReal_eq_coe_coeFn, FiniteMeasure.mass] using
      (norm_integral_le_of_norm_le_const (μ := (μs i : Measure X))
        (Eventually.of_forall (fun x => (fs i - f).norm_coe_le_norm x)))
  have hi (i : ι) : (∫ x, (fs i - f) x ∂(μs i : Measure X)) =
      (∫ x, fs i x ∂(μs i : Measure X)) - ∫ x, f x ∂(μs i : Measure X) :=
    integral_sub
      ((fs i).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  simpa only [hi, Function.comp_apply, sub_add_cancel, zero_add] using hdiff.add hfixed

theorem continuous_integral_varying :
    Continuous (fun p : FiniteMeasure X × C(X, ℝ) => ∫ x, p.2 x ∂(p.1 : Measure X)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact tendsto_integral_varying continuous_fst.continuousAt continuous_snd.continuousAt
end WeakIntegral



abbrev Angle := Icc (0 : ℝ) (2 * Real.pi)

local instance : MeasureSpace Angle := Measure.Subtype.measureSpace

instance : IsFiniteMeasure (volume : Measure Angle) := by
  constructor
  rw [show (volume : Measure Angle) = Measure.comap Subtype.val volume from rfl,
    Measure.comap_apply _ Subtype.val_injective
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' _
      MeasurableSet.univ]
  simpa only [image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) (2 * Real.pi))).measure_lt_top

theorem integral_angle (F : ℝ → ℝ) :
    (∫ θ : Angle, F θ) = ∫ θ in (0 : ℝ)..2 * Real.pi, F θ := by
  rw [integral_subtype measurableSet_Icc F, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by positivity)]


def RadialDensity (v : ℂ → ℝ) (R : ℝ)
    (hv : ContinuousOn v (ball 0 1)) (hR : R ∈ Ioo 0 1) : C(Angle, ℝ) where
  toFun θ := (2 * Real.pi)⁻¹ * v (circleMap 0 R θ)
  continuous_toFun := by
    apply continuous_const.mul
    apply hv.comp_continuous ((continuous_circleMap 0 R).comp continuous_subtype_val)
    intro θ
    simp only [Function.comp_apply, mem_ball, dist_zero_right, norm_circleMap_zero,
      abs_of_pos hR.1]
    exact hR.2

theorem radialDensity_nonneg {v : ℂ → ℝ} {R : ℝ}
    (hv : ContinuousOn v (ball 0 1)) (hR : R ∈ Ioo 0 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) (θ : Angle) :
    0 ≤ RadialDensity v R hv hR θ := by
  apply mul_nonneg (by positivity)
  apply hn
  simp only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hR.1]
  exact hR.2

def radialMeasure (v : ℂ → ℝ) (R : ℝ)
    (hv : ContinuousOn v (ball 0 1)) (hR : R ∈ Ioo 0 1) : FiniteMeasure Angle :=
  densityMeasure volume (RadialDensity v R hv hR)

theorem integral_radialMeasure {v : ℂ → ℝ} {R : ℝ}
    (hv : ContinuousOn v (ball 0 1)) (hR : R ∈ Ioo 0 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) (F : ℝ → ℝ) :
    (∫ θ : Angle, F θ ∂(radialMeasure v R hv hR : Measure Angle)) =
      (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        v (circleMap 0 R θ) * F θ := by
  rw [radialMeasure, integral_densityMeasure _ _ (radialDensity_nonneg hv hR hn)]
  simp only [RadialDensity, ContinuousMap.coe_mk, mul_assoc]
  rw [integral_const_mul]
  exact congrArg ((2 * Real.pi)⁻¹ * ·)
    (integral_angle (fun θ => v (circleMap 0 R θ) * F θ))

theorem mass_radialMeasure {v : ℂ → ℝ} {R : ℝ}
    (hv : HarmonicOnNhd v (ball 0 1)) (hR : R ∈ Ioo 0 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) :
    ((radialMeasure v R hv.continuousOn hR).mass : ℝ) = v 0 := by
  have h := integral_radialMeasure hv.continuousOn hR hn (fun _ => 1)
  have hr : HarmonicOnNhd v (closedBall 0 |R|) := by
    rw [abs_of_pos hR.1]
    exact hv.mono (closedBall_subset_ball hR.2)
  have hr' := hr.circleAverage_eq
  rw [Real.circleAverage_def] at hr'
  simp only [smul_eq_mul] at hr'
  simpa only [integral_const, smul_eq_mul, mul_one, FiniteMeasure.measureReal_eq_coe_coeFn,
    FiniteMeasure.mass, hr'] using h


def radialKernel (w : ℂ) (R : ℝ) (hR : ‖w‖ < R) : C(Angle, ℝ) where
  toFun θ := (herglotzRieszKernel 0 w (circleMap 0 R θ)).re
  continuous_toFun := by
    have hn (θ : Angle) : circleMap 0 R θ - w ≠ 0 := by
      intro h
      have he := congrArg norm (sub_eq_zero.mp h)
      simp only [norm_circleMap_zero, abs_of_pos (lt_of_le_of_lt (norm_nonneg w) hR)] at he
      linarith
    simp only [herglotzRieszKernel, sub_zero]
    apply Complex.continuous_re.comp
    exact (continuous_circleMap 0 R |>.comp continuous_subtype_val |>.add continuous_const).div
      (continuous_circleMap 0 R |>.comp continuous_subtype_val |>.sub continuous_const) hn

theorem continuous_radialKernel (w : ℂ) :
    Continuous (fun R : Ioi ‖w‖ => radialKernel w R R.property) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hn (p : Ioi ‖w‖ × Angle) : circleMap 0 p.1 p.2 - w ≠ 0 := by
    intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    simp only [norm_circleMap_zero,
      abs_of_pos (lt_of_le_of_lt (norm_nonneg w) p.1.property)] at he
    exact (ne_of_gt p.1.property) he
  simp only [Function.uncurry_def, radialKernel, ContinuousMap.coe_mk,
    herglotzRieszKernel, sub_zero]
  apply Complex.continuous_re.comp
  apply Continuous.div _ _ hn <;> unfold circleMap <;> fun_prop

theorem integral_radialKernel {v : ℂ → ℝ} {R : ℝ}
    (hv : HarmonicOnNhd v (ball 0 1)) (hR : R ∈ Ioo 0 1)
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) {w : ℂ} (hw : ‖w‖ < R) :
    (∫ θ : Angle, radialKernel w R hw θ
      ∂(radialMeasure v R hv.continuousOn hR : Measure Angle)) = v w := by
  have hr : HarmonicOnNhd v (closedBall 0 R) :=
    hv.mono (closedBall_subset_ball hR.2)
  have hp := hr.circleAverage_re_herglotzRieszKernel_smul
    (by simpa only [mem_ball, dist_zero_right] using hw)
  rw [Real.circleAverage_def] at hp
  change (∫ θ : Angle, (herglotzRieszKernel 0 w (circleMap 0 R θ)).re
    ∂(radialMeasure v R hv.continuousOn hR : Measure Angle)) = _
  rw [integral_radialMeasure hv.continuousOn hR hn
    (fun θ => (herglotzRieszKernel 0 w (circleMap 0 R θ)).re)]
  simpa only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.mul_apply, mul_comm] using hp

def approachRadius (n : ℕ) : ℝ := 1 - ((n : ℝ) + 2)⁻¹

theorem approachRadius_mem (n : ℕ) : approachRadius n ∈ Ioo 0 1 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < (n : ℝ) + 2 := by linarith
  have hi := (inv_lt_one₀ hp).mpr (by linarith)
  have hi' := inv_pos.mpr hp
  exact ⟨by dsimp [approachRadius]; linarith, by dsimp [approachRadius]; linarith⟩

theorem approachRadius_tendsto : Tendsto approachRadius atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun _ => by linarith) tendsto_natCast_atTop_atTop
  change Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 1)
  simpa only [Function.comp_apply, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_inv_atTop_zero.comp hn)


def clippedRadius (w : ℂ) (hw : ‖w‖ < 1) (R : ℝ) : Ioi ‖w‖ :=
  ⟨max ((‖w‖ + 1) / 2) R,
    show ‖w‖ < max ((‖w‖ + 1) / 2) R from
      lt_of_lt_of_le (show ‖w‖ < (‖w‖ + 1) / 2 by linarith) (le_max_left _ _)⟩

def clippedKernel (w : ℂ) (hw : ‖w‖ < 1) (R : ℝ) : C(Angle, ℝ) :=
  radialKernel w (clippedRadius w hw R) (clippedRadius w hw R).property

theorem continuous_clippedKernel (w : ℂ) (hw : ‖w‖ < 1) :
    Continuous (clippedKernel w hw) := by
  exact (continuous_radialKernel w).comp
    (show Continuous (clippedRadius w hw) from
      (continuous_const.max continuous_id).subtype_mk _)

theorem clippedKernel_one (w : ℂ) (hw : ‖w‖ < 1) :
    clippedKernel w hw 1 = radialKernel w 1 hw := by
  have ha : (‖w‖ + 1) / 2 ≤ 1 := by linarith
  simp only [clippedKernel, clippedRadius, max_eq_right ha]

theorem clippedKernel_eq {w : ℂ} (hw : ‖w‖ < 1) {R : ℝ}
    (hR : (‖w‖ + 1) / 2 < R) :
    clippedKernel w hw R = radialKernel w R (by linarith) := by
  simp only [clippedKernel, clippedRadius, max_eq_right hR.le]

def radialSequence (v : ℂ → ℝ) (hv : HarmonicOnNhd v (ball 0 1))
    (n : ℕ) : FiniteMeasure Angle :=
  radialMeasure v (approachRadius n) hv.continuousOn (approachRadius_mem n)

theorem exists_radialSequence_cluster {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) :
    ∃ μ : FiniteMeasure Angle, (μ.mass : ℝ) = v 0 ∧
      MapClusterPt μ atTop (radialSequence v hv) := by
  let C : ℝ≥0 := ⟨v 0, hn 0 (by simp)⟩
  have hmass (n : ℕ) : (radialSequence v hv n).mass = C := by
    apply NNReal.coe_injective
    exact mass_radialMeasure hv (approachRadius_mem n) hn
  obtain ⟨μ, hμmass, hcluster⟩ :=
    (isCompact_setOfPred_finiteMeasure_eq_of_compactSpace Angle C).exists_mapClusterPt
      (u := radialSequence v hv) (f := atTop) (by
        rw [Filter.le_principal_iff]
        change ∀ᶠ n : ℕ in atTop, (radialSequence v hv n).mass = C
        exact Eventually.of_forall hmass)
  exact ⟨μ, congrArg ((↑) : ℝ≥0 → ℝ) hμmass, hcluster⟩

theorem eventually_integral_clippedKernel {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) {w : ℂ} (hw : ‖w‖ < 1) :
    ∀ᶠ n : ℕ in atTop,
      (∫ θ : Angle, clippedKernel w hw (approachRadius n) θ
        ∂(radialSequence v hv n : Measure Angle)) = v w := by
  have ha : (‖w‖ + 1) / 2 < 1 := by linarith
  filter_upwards [approachRadius_tendsto.eventually (Ioi_mem_nhds ha)] with n hn'
  have hwr : ‖w‖ < approachRadius n := by linarith
  rw [clippedKernel_eq hw hn']
  exact integral_radialKernel hv (approachRadius_mem n) hn hwr

theorem radialCluster_represents {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) {μ : FiniteMeasure Angle}
    (hcluster : MapClusterPt μ atTop (radialSequence v hv))
    {w : ℂ} (hw : ‖w‖ < 1) :
    (∫ θ : Angle, radialKernel w 1 hw θ ∂(μ : Measure Angle)) = v w := by
  let l := comap (radialSequence v hv) (𝓝 μ) ⊓ (atTop : Filter ℕ)
  have : l.NeBot := neBot_inf_comap_iff_map'.mpr hcluster
  have hμ : Tendsto (radialSequence v hv) l (𝓝 μ) := tendsto_comap.mono_left inf_le_left
  have hR : Tendsto approachRadius l (𝓝 1) := approachRadius_tendsto.mono_left inf_le_right
  have hk : Tendsto (fun n => clippedKernel w hw (approachRadius n)) l
      (𝓝 (radialKernel w 1 hw)) := by
    simpa only [clippedKernel_one, Function.comp_def] using
      (continuous_clippedKernel w hw).continuousAt.tendsto.comp hR
  have hi := tendsto_integral_varying hμ hk
  have heq : ∀ᶠ n : ℕ in l,
      (∫ θ : Angle, clippedKernel w hw (approachRadius n) θ
        ∂(radialSequence v hv n : Measure Angle)) = v w :=
    (show l ≤ atTop from inf_le_right) (eventually_integral_clippedKernel hv hn hw)
  exact tendsto_nhds_unique hi (tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq))




theorem positive_harmonic_disk_representation {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) :
    ∃ μ : FiniteMeasure Angle, (μ.mass : ℝ) = v 0 ∧
      ∀ w : ℂ, ‖w‖ < 1 →
        (∫ θ : Angle, (herglotzRieszKernel 0 w (circleMap 0 1 θ)).re
          ∂(μ : Measure Angle)) = v w := by
  obtain ⟨μ, hm, hc⟩ := exists_radialSequence_cluster hv hn
  exact ⟨μ, hm, fun _ hw => radialCluster_represents hv hn hc hw⟩


def diskKernel (w : ℂ) (hw : ‖w‖ < 1) : C(Angle, ℂ) where
  toFun θ := herglotzRieszKernel 0 w (circleMap 0 1 θ)
  continuous_toFun := by
    have hn (θ : Angle) : circleMap 0 1 θ - w ≠ 0 := by
      intro h
      have he := congrArg norm (sub_eq_zero.mp h)
      simp only [norm_circleMap_zero, abs_one] at he
      linarith
    simp only [herglotzRieszKernel, sub_zero]
    exact (continuous_circleMap 0 1 |>.comp continuous_subtype_val |>.add continuous_const).div
      (continuous_circleMap 0 1 |>.comp continuous_subtype_val |>.sub continuous_const) hn

def diskIntegral (μ : FiniteMeasure Angle) (w : ℂ) : ℂ :=
  ∫ θ : Angle, herglotzRieszKernel 0 w (circleMap 0 1 θ) ∂(μ : Measure Angle)

theorem diskKernel_integrable (μ : FiniteMeasure Angle) {w : ℂ} (hw : ‖w‖ < 1) :
    Integrable (fun θ : Angle => herglotzRieszKernel 0 w (circleMap 0 1 θ))
      (μ : Measure Angle) :=
  (diskKernel w hw).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem hasDerivAt_diskIntegral (μ : FiniteMeasure Angle) {w : ℂ} (hw : ‖w‖ < 1) :
    HasDerivAt (diskIntegral μ)
      (∫ θ : Angle, 2 * circleMap 0 1 θ / (circleMap 0 1 θ - w) ^ 2
        ∂(μ : Measure Angle)) w := by
  let d := (1 - ‖w‖) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hdist (x : ℂ) (hx : x ∈ ball w d) (θ : Angle) : d ≤ ‖circleMap 0 1 θ - x‖ := by
    have hnorm := norm_le_norm_sub_add x w
    have hx' : ‖x - w‖ < d := by simpa only [mem_ball, dist_eq_norm] using hx
    have he := norm_sub_norm_le (circleMap 0 1 θ) x
    simp only [norm_circleMap_zero, abs_one] at he
    dsimp [d] at *
    linarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x (θ : Angle) => herglotzRieszKernel 0 x (circleMap 0 1 θ))
    (F' := fun x (θ : Angle) => 2 * circleMap 0 1 θ / (circleMap 0 1 θ - x) ^ 2)
    (bound := fun _ => 2 * (d ^ 2)⁻¹) (μ := (μ : Measure Angle))
    (ball_mem_nhds w hd) ?_ (diskKernel_integrable μ hw) ?_ ?_ (integrable_const _) ?_).2
  · filter_upwards with x
    simp only [herglotzRieszKernel, sub_zero, circleMap]
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  · exact (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards with θ x hx
    rw [norm_div, norm_mul, norm_pow, norm_circleMap_zero, abs_one, mul_one,
      show ‖(2 : ℂ)‖ = 2 by norm_num, div_eq_mul_inv]
    gcongr
    exact hdist x hx θ
  · filter_upwards with θ x hx
    have hne : circleMap 0 1 θ - x ≠ 0 :=
      norm_pos_iff.mp (lt_of_lt_of_le hd (hdist x hx θ))
    have hh := ((hasDerivAt_id' x).const_add (circleMap 0 1 θ)).div
      ((hasDerivAt_id' x).const_sub (circleMap 0 1 θ)) hne
    simpa [herglotzRieszKernel_def, sub_zero, sub_sub, ← two_mul, Pi.div_def] using hh

theorem analyticOnNhd_diskIntegral (μ : FiniteMeasure Angle) :
    AnalyticOnNhd ℂ (diskIntegral μ) (ball 0 1) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro w hw
  exact (hasDerivAt_diskIntegral μ (by simpa only [mem_ball, dist_zero_right] using hw)).differentiableAt.differentiableWithinAt

theorem positive_real_disk_representation {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P (ball 0 1))
    (hn : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (P w).re) :
    ∃ (μ : FiniteMeasure Angle) (c : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1,
        P w = (c : ℂ) * I + diskIntegral μ w := by
  have hh : HarmonicOnNhd (fun w => (P w).re) (ball 0 1) :=
    fun w hw => (hP w hw).harmonicAt_re
  obtain ⟨μ, _, hμ⟩ := positive_harmonic_disk_representation hh hn
  have hre (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : (P w - diskIntegral μ w).re = 0 := by
    have hwn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    have hi := Complex.reCLM.integral_comp_comm (diskKernel_integrable μ hwn)
    change (∫ θ : Angle, (herglotzRieszKernel 0 w (circleMap 0 1 θ)).re
      ∂(μ : Measure Angle)) = (diskIntegral μ w).re at hi
    rw [Complex.sub_re, ← hi, hμ w hwn, sub_self]
  obtain ⟨c, hc⟩ := (hP.sub (analyticOnNhd_diskIntegral μ)).eq_re_add_const_mul_I_of_re_eq_const
    hre isOpen_ball (isConnected_ball (by norm_num))
  refine ⟨μ, c, fun w hw => ?_⟩
  have hh' := hc w hw
  simp only [Complex.ofReal_zero, zero_add] at hh'
  exact sub_eq_iff_eq_add.mp hh'


def toDisk (s : ℂ) : ℂ := (s - I) / (s + I)
def toHalfPlane (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

theorem add_I_ne_zero {s : ℂ} (hs : 0 < s.im) : s + I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at hi
  linarith

theorem one_sub_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have he : w = 1 := (sub_eq_zero.mp h).symm
  simp [he] at hw

theorem norm_toDisk_lt_one {s : ℂ} (hs : 0 < s.im) : ‖toDisk s‖ < 1 := by
  have hd := add_I_ne_zero hs
  rw [toDisk, norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.I_re, sub_zero,
    Complex.add_re, add_zero, Complex.sub_im, Complex.add_im, Complex.I_im]
  nlinarith

theorem im_toHalfPlane (w : ℂ) :
    (toHalfPlane w).im = (1 - ‖w‖ ^ 2) / Complex.normSq (1 - w) := by
  simp only [toHalfPlane, Complex.div_im, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
    zero_mul, one_mul, zero_add, zero_sub, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply]
  ring

theorem im_toHalfPlane_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (toHalfPlane w).im := by
  rw [im_toHalfPlane]
  apply div_pos _ (Complex.normSq_pos.mpr (one_sub_ne_zero hw))
  nlinarith [norm_nonneg w]

theorem toHalfPlane_toDisk {s : ℂ} (hs : 0 < s.im) : toHalfPlane (toDisk s) = s := by
  have hd := add_I_ne_zero hs
  have he := one_sub_ne_zero (norm_toDisk_lt_one hs)
  dsimp [toHalfPlane, toDisk] at *
  field_simp
  ring

theorem toDisk_toHalfPlane {w : ℂ} (hw : ‖w‖ < 1) : toDisk (toHalfPlane w) = w := by
  have hd := one_sub_ne_zero hw
  have he := add_I_ne_zero (im_toHalfPlane_pos hw)
  dsimp [toHalfPlane, toDisk] at *
  field_simp
  ring

theorem analyticAt_toHalfPlane {w : ℂ} (hw : ‖w‖ < 1) :
    AnalyticAt ℂ toHalfPlane w := by
  exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) (one_sub_ne_zero hw)

theorem analyticAt_toDisk {s : ℂ} (hs : 0 < s.im) : AnalyticAt ℂ toDisk s := by
  exact (analyticAt_id.sub analyticAt_const).div (analyticAt_id.add analyticAt_const)
    (add_I_ne_zero hs)



theorem upper_half_plane_representation {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → 0 ≤ (P s).im) :
    ∃ (μ : FiniteMeasure Angle) (a : ℝ),
      ∀ s : ℂ, 0 < s.im → P s = (a : ℂ) + I * diskIntegral μ (toDisk s) := by
  let Q : ℂ → ℂ := fun w => -I * P (toHalfPlane w)
  have hQ : AnalyticOnNhd ℂ Q (ball 0 1) := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    exact analyticAt_const.mul ((hP _ (im_toHalfPlane_pos hwn)).comp
      (analyticAt_toHalfPlane hwn))
  have hQn : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (Q w).re := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    simpa [Q, Complex.mul_re] using hn _ (im_toHalfPlane_pos hwn)
  obtain ⟨μ, c, hc⟩ := positive_real_disk_representation hQ hQn
  refine ⟨μ, -c, fun s hs => ?_⟩
  have he := hc (toDisk s) (by simpa only [mem_ball, dist_zero_right] using norm_toDisk_lt_one hs)
  dsimp [Q] at he
  rw [toHalfPlane_toDisk hs] at he
  have ht := congrArg (I * ·) he
  simpa [mul_add, mul_neg, ← mul_assoc, mul_comm I (c : ℂ),
    mul_assoc (c : ℂ) I I, Complex.I_sq] using ht

theorem continuous_weighted_radial {v : ℂ → ℝ}
    (hv : ContinuousOn v (ball 0 1)) (f : C(Angle, ℝ))
    (hc : ∀ θ ∈ tsupport f, ContinuousAt v (circleMap 0 1 θ)) :
    Continuous (fun p : Icc (0 : ℝ) 1 × Angle =>
      f p.2 * v (circleMap 0 p.1 p.2)) := by
  have hm : Continuous (fun p : Icc (0 : ℝ) 1 × Angle => circleMap 0 p.1 p.2) := by
    simp only [circleMap]
    fun_prop
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hf : p.2 ∈ tsupport f
  · apply (f.continuous.comp continuous_snd).continuousAt.mul
    apply ContinuousAt.comp _ hm.continuousAt
    rcases lt_or_eq_of_le p.1.property.2 with hr | hr
    · apply hv.continuousAt (isOpen_ball.mem_nhds _)
      simp only [mem_ball, dist_zero_right, norm_circleMap_zero,
        abs_of_nonneg p.1.property.1]
      exact hr
    · simpa only [hr] using hc p.2 hf
  · apply (continuousAt_const (y := (0 : ℝ))).congr
    have he := (notMem_tsupport_iff_eventuallyEq.mp hf).comp_tendsto
      (continuous_snd.continuousAt : ContinuousAt Prod.snd p)
    filter_upwards [he] with q hq
    simp only [Function.comp_apply, Pi.zero_apply] at hq
    simp [hq]

theorem tendsto_radial_test_zero {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) (f : C(Angle, ℝ))
    (hc : ∀ θ ∈ tsupport f, ContinuousAt v (circleMap 0 1 θ))
    (hz : ∀ θ ∈ tsupport f, v (circleMap 0 1 θ) = 0) :
    Tendsto (fun n => ∫ θ : Angle, f θ ∂(radialSequence v hv n : Measure Angle))
      atTop (𝓝 0) := by
  let R : ℕ → Icc (0 : ℝ) 1 := fun n =>
    ⟨approachRadius n, (approachRadius_mem n).1.le, (approachRadius_mem n).2.le⟩
  let R₁ : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hR : Tendsto R atTop (𝓝 R₁) := tendsto_subtype_rng.mpr approachRadius_tendsto
  have hj := continuous_weighted_radial hv.continuousOn f hc
  let F : Icc (0 : ℝ) 1 → C(Angle, ℝ) := fun r =>
    ⟨fun θ => f θ * v (circleMap 0 r θ), hj.comp (continuous_const.prodMk continuous_id)⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F hj
  have hF₁ : F R₁ = 0 := by
    ext θ
    change f θ * v (circleMap 0 1 θ) = 0
    by_cases he : f θ = 0
    · simp [he]
    · simp [hz θ (subset_closure he)]
  have ht : Tendsto (fun n => F (R n)) atTop (𝓝 0) := by
    simpa only [hF₁, Function.comp_def] using hF.continuousAt.tendsto.comp hR
  let μV : FiniteMeasure Angle := ⟨volume, inferInstance⟩
  have hi := tendsto_integral_varying (tendsto_const_nhds (x := μV)) ht
  change Tendsto (fun n => ∫ θ : Angle, F (R n) θ) atTop (𝓝 (∫ θ : Angle, (0 : C(Angle, ℝ)) θ)) at hi
  have he (n : ℕ) :
      (∫ θ : Angle, f θ ∂(radialSequence v hv n : Measure Angle)) =
        (2 * Real.pi)⁻¹ * ∫ θ : Angle, F (R n) θ := by
    change (∫ θ : Angle, f θ ∂(densityMeasure (volume : Measure Angle)
      (RadialDensity v (approachRadius n) hv.continuousOn (approachRadius_mem n)) : Measure Angle)) = _
    rw [integral_densityMeasure _ _
      (radialDensity_nonneg hv.continuousOn (approachRadius_mem n) hn)]
    simp only [RadialDensity, ContinuousMap.coe_mk, mul_assoc]
    rw [integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with θ
    change v (circleMap 0 (approachRadius n) θ) * f θ =
      f θ * v (circleMap 0 (approachRadius n) θ)
    ring
  simpa only [he, ContinuousMap.zero_apply, integral_zero, mul_zero] using
    hi.const_mul ((2 * Real.pi)⁻¹)

theorem radialCluster_integral_zero {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) {μ : FiniteMeasure Angle}
    (hcluster : MapClusterPt μ atTop (radialSequence v hv)) (f : C(Angle, ℝ))
    (hc : ∀ θ ∈ tsupport f, ContinuousAt v (circleMap 0 1 θ))
    (hz : ∀ θ ∈ tsupport f, v (circleMap 0 1 θ) = 0) :
    (∫ θ : Angle, f θ ∂(μ : Measure Angle)) = 0 := by
  let l := comap (radialSequence v hv) (𝓝 μ) ⊓ (atTop : Filter ℕ)
  have : l.NeBot := neBot_inf_comap_iff_map'.mpr hcluster
  have hμ : Tendsto (radialSequence v hv) l (𝓝 μ) := tendsto_comap.mono_left inf_le_left
  exact tendsto_nhds_unique
    ((FiniteMeasure.continuous_integral_continuousMap f).continuousAt.tendsto.comp hμ)
    ((tendsto_radial_test_zero hv hn f hc hz).mono_left inf_le_right)



theorem radialCluster_no_mass {v : ℂ → ℝ}
    (hv : HarmonicOnNhd v (ball 0 1))
    (hn : ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ v z) {μ : FiniteMeasure Angle}
    (hcluster : MapClusterPt μ atTop (radialSequence v hv))
    {U : Set Angle} (hU : IsOpen U)
    (hc : ∀ θ ∈ U, ContinuousAt v (circleMap 0 1 θ))
    (hz : ∀ θ ∈ U, v (circleMap 0 1 θ) = 0) : (μ : Measure Angle) U = 0 := by
  have hs : U ⊆ (μ : Measure Angle).supportᶜ := by
    intro θ hθ
    obtain ⟨f, hfU, hfθ, hfr⟩ := exists_tsupport_one_of_isOpen_isClosed hU
      isClosed_closure.isCompact isClosed_singleton (singleton_subset_iff.mpr hθ)
    have hzero : (∫ z : Angle, f z ∂(μ : Measure Angle)) = 0 :=
      radialCluster_integral_zero hv hn hcluster f
        (fun z hz' => hc z (hfU hz')) (fun z hz' => hz z (hfU hz'))
    have hae : f =ᵐ[(μ : Measure Angle)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun z => (hfr z).1)
        (f.continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))).mp hzero
    apply Measure.notMem_support_iff_exists.mpr
    refine ⟨{z | f z ≠ 0}, ?_, ?_⟩
    · exact f.continuous.continuousAt.eventually_ne (by simp [hfθ (mem_singleton θ)])
    · exact ae_iff.mp hae
  exact measure_mono_null hs (Measure.measure_compl_support (μ := (μ : Measure Angle)))

theorem positive_real_disk_representation_with_support {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P (ball 0 1))
    (hn : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (P w).re)
    {U : Set Angle} (hU : IsOpen U)
    (hc : ∀ θ ∈ U, ContinuousAt (fun w => (P w).re) (circleMap 0 1 θ))
    (hz : ∀ θ ∈ U, (P (circleMap 0 1 θ)).re = 0) :
    ∃ (μ : FiniteMeasure Angle) (c : ℝ), (μ : Measure Angle) U = 0 ∧
      ∀ w ∈ ball (0 : ℂ) 1,
        P w = (c : ℂ) * I + diskIntegral μ w := by
  have hh : HarmonicOnNhd (fun w => (P w).re) (ball 0 1) :=
    fun w hw => (hP w hw).harmonicAt_re
  obtain ⟨μ, _, hcluster⟩ := exists_radialSequence_cluster hh hn
  have hre (w : ℂ) (hw : w ∈ ball (0 : ℂ) 1) : (P w - diskIntegral μ w).re = 0 := by
    have hwn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    have hi := Complex.reCLM.integral_comp_comm (diskKernel_integrable μ hwn)
    change (∫ θ : Angle, (herglotzRieszKernel 0 w (circleMap 0 1 θ)).re
      ∂(μ : Measure Angle)) = (diskIntegral μ w).re at hi
    have hr := radialCluster_represents hh hn hcluster hwn
    change (∫ θ : Angle, (herglotzRieszKernel 0 w (circleMap 0 1 θ)).re
      ∂(μ : Measure Angle)) = (P w).re at hr
    rw [Complex.sub_re, ← hi, hr, sub_self]
  obtain ⟨c, hcc⟩ := (hP.sub (analyticOnNhd_diskIntegral μ)).eq_re_add_const_mul_I_of_re_eq_const
    hre isOpen_ball (isConnected_ball (by norm_num))
  refine ⟨μ, c, radialCluster_no_mass hh hn hcluster hU hc hz, fun w hw => ?_⟩
  have he := hcc w hw
  simp only [Complex.ofReal_zero, zero_add] at he
  exact sub_eq_iff_eq_add.mp he

theorem re_toHalfPlane (w : ℂ) :
    (toHalfPlane w).re = -2 * w.im / Complex.normSq (1 - w) := by
  simp only [toHalfPlane, Complex.div_re, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im,
    zero_mul, one_mul, zero_add, zero_sub]
  ring

theorem one_sub_ne_zero_of_im_neg {w : ℂ} (hw : w.im < 0) : 1 - w ≠ 0 := by
  intro h
  have hh := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.one_im, Complex.zero_im, zero_sub] at hh
  linarith

theorem boundary_toHalfPlane {w : ℂ} (hw : ‖w‖ = 1) (hi : w.im < 0) :
    (toHalfPlane w).im = 0 ∧ 0 < (toHalfPlane w).re := by
  constructor
  · simp [im_toHalfPlane, hw]
  · rw [re_toHalfPlane]
    exact div_pos (mul_pos_of_neg_of_neg (by norm_num) hi)
      (Complex.normSq_pos.mpr (one_sub_ne_zero_of_im_neg hi))

theorem analyticAt_toHalfPlane_of_ne {w : ℂ} (hw : 1 - w ≠ 0) :
    AnalyticAt ℂ toHalfPlane w := by
  exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
    (analyticAt_const.sub analyticAt_id) hw



theorem upper_half_plane_representation_with_support_of_continuous {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → 0 ≤ (P s).im)
    (hR : ∀ x : ℝ, 0 < x → ContinuousAt P (x : ℂ) ∧ (P (x : ℂ)).im = 0) :
    ∃ (μ : FiniteMeasure Angle) (a : ℝ),
      (∀ᵐ θ : Angle ∂(μ : Measure Angle), 0 ≤ (circleMap 0 1 θ).im) ∧
      ∀ s : ℂ, 0 < s.im → P s = (a : ℂ) + I * diskIntegral μ (toDisk s) := by
  let Q : ℂ → ℂ := fun w => -I * P (toHalfPlane w)
  have hQ : AnalyticOnNhd ℂ Q (ball 0 1) := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    exact analyticAt_const.mul ((hP _ (im_toHalfPlane_pos hwn)).comp
      (analyticAt_toHalfPlane hwn))
  have hQn : ∀ w ∈ ball (0 : ℂ) 1, 0 ≤ (Q w).re := by
    intro w hw
    have hwn : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
    simpa [Q, Complex.mul_re] using hn _ (im_toHalfPlane_pos hwn)
  let U : Set Angle := {θ | (circleMap 0 1 θ).im < 0}
  have hU : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hboundary (θ : Angle) (hθ : θ ∈ U) :
      ContinuousAt (fun w => (Q w).re) (circleMap 0 1 θ) ∧
        (Q (circleMap 0 1 θ)).re = 0 := by
    have hb := boundary_toHalfPlane (w := circleMap 0 1 θ)
      (by simp only [norm_circleMap_zero, abs_one]) hθ
    have he : ((toHalfPlane (circleMap 0 1 θ)).re : ℂ) = toHalfPlane (circleMap 0 1 θ) := by
      simpa only [hb.1, Complex.ofReal_zero, zero_mul, add_zero] using
        Complex.re_add_im (toHalfPlane (circleMap 0 1 θ))
    have hp := hR _ hb.2
    rw [he] at hp
    constructor
    · refine Complex.continuous_re.continuousAt.comp ?_
      change ContinuousAt Q (circleMap 0 1 θ)
      exact continuousAt_const.mul (hp.1.comp
        (analyticAt_toHalfPlane_of_ne (one_sub_ne_zero_of_im_neg hθ)).continuousAt)
    · simpa [Q, Complex.mul_re] using hp.2
  obtain ⟨μ, c, hm, hc⟩ := positive_real_disk_representation_with_support hQ hQn hU
    (fun θ hθ => (hboundary θ hθ).1) (fun θ hθ => (hboundary θ hθ).2)
  refine ⟨μ, -c, ?_, fun s hs => ?_⟩
  · have ha := measure_eq_zero_iff_ae_notMem.mp hm
    filter_upwards [ha] with θ hθ
    exact le_of_not_gt hθ
  · have he := hc (toDisk s) (by simpa only [mem_ball, dist_zero_right] using norm_toDisk_lt_one hs)
    dsimp [Q] at he
    rw [toHalfPlane_toDisk hs] at he
    have ht := congrArg (I * ·) he
    simpa [mul_add, mul_neg, ← mul_assoc, mul_comm I (c : ℂ),
      mul_assoc (c : ℂ) I I, Complex.I_sq] using ht





def boundaryParameter (θ : Angle) : ℝ :=
  (1 - (circleMap 0 1 θ).re + max 0 (circleMap 0 1 θ).im) /
    (2 * (1 + max 0 (circleMap 0 1 θ).im))

def boundaryWeight (θ : Angle) : ℝ :=
  (1 + max 0 (circleMap 0 1 θ).im)⁻¹

theorem boundaryParameter_mem (θ : Angle) : boundaryParameter θ ∈ Icc 0 1 := by
  have hr : |(circleMap 0 1 θ).re| ≤ 1 := by
    simpa only [norm_circleMap_zero, abs_one] using Complex.abs_re_le_norm (circleMap 0 1 θ)
  have hm : 0 ≤ max 0 (circleMap 0 1 θ).im := le_max_left _ _
  have hd : 0 < 2 * (1 + max 0 (circleMap 0 1 θ).im) := by positivity
  rw [abs_le] at hr
  constructor
  · exact div_nonneg (by linarith) hd.le
  · rw [boundaryParameter, div_le_one hd]
    linarith

theorem boundaryWeight_pos (θ : Angle) : 0 < boundaryWeight θ := by
  dsimp [boundaryWeight]
  positivity

theorem boundaryWeight_le_one (θ : Angle) : boundaryWeight θ ≤ 1 := by
  dsimp [boundaryWeight]
  exact inv_le_one_of_one_le₀ (by linarith [le_max_left 0 (circleMap 0 1 θ).im])

theorem continuous_boundaryParameter : Continuous boundaryParameter := by
  unfold boundaryParameter
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro θ
  positivity

theorem continuous_boundaryWeight : Continuous boundaryWeight := by
  unfold boundaryWeight
  apply Continuous.inv₀ (by fun_prop)
  intro θ
  positivity


def compactKernel (t w : ℝ) (s : ℂ) : ℂ := (w : ℂ) / (1 + (s - 1) * t)

theorem compactDen_ne_zero {t : ℝ} (ht : t ∈ Icc 0 1) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) : 1 + (s - 1) * (t : ℂ) ≠ 0 := by
  intro he
  rcases hs with hs | hs
  · have hi := congrArg Complex.im he
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.sub_im,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re, zero_add,
      Complex.zero_im] at hi
    have ht0 : t = 0 := (mul_eq_zero.mp hi).resolve_left hs.ne'
    simp [ht0] at he
  · have hr := congrArg Complex.re he
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.sub_re,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.ofReal_re, Complex.zero_re] at hr
    have ht0 : 0 < t := lt_of_le_of_ne ht.1 (by
      intro h
      simp [← h] at he)
    nlinarith [mul_pos hs ht0, ht.2]

theorem compactKernel_boundary {s ζ : ℂ} (hs : 0 < s.im)
    (hζ : ‖ζ‖ = 1) (hi : 0 ≤ ζ.im) :
    I * herglotzRieszKernel 0 (toDisk s) ζ =
      (1 - 2 * ((1 - ζ.re + ζ.im) / (2 * (1 + ζ.im)) : ℝ) : ℂ) +
      (s - 1) * compactKernel ((1 - ζ.re + ζ.im) / (2 * (1 + ζ.im)))
        (1 + ζ.im)⁻¹ s := by
  have hsi := add_I_ne_zero hs
  have hd : ζ - toDisk s ≠ 0 := by
    intro h
    have he : ζ = toDisk s := sub_eq_zero.mp h
    have := norm_toDisk_lt_one hs
    rw [← he, hζ] at this
    exact (lt_irrefl _ this).elim
  have hnorm : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, Complex.sq_norm, hζ, pow_two] using Complex.normSq_eq_norm_sq ζ
  have hp : 0 < 2 * (1 + ζ.im) := by positivity
  have hr : |ζ.re| ≤ 1 := hζ ▸ Complex.abs_re_le_norm ζ
  have ht : (1 - ζ.re + ζ.im) / (2 * (1 + ζ.im)) ∈ Icc (0 : ℝ) 1 := by
    rw [abs_le] at hr
    exact ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).mpr (by linarith)⟩
  have hden := compactDen_ne_zero ht (Or.inl hs)
  have hc : (2 * (1 + (ζ.im : ℂ))) ≠ 0 := by
    exact_mod_cast hp.ne'
  have hc' : 1 + (ζ.im : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 : ℝ) + ζ.im ≠ 0)
  simp only [herglotzRieszKernel_def, sub_zero, compactKernel, toDisk,
    Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_inv] at *
  have hd₂ : ζ * (s + I) - (s - I) ≠ 0 := by
    intro he
    apply hd
    apply sub_eq_zero.mpr
    apply (eq_div_iff hsi).mpr
    exact sub_eq_zero.mp he
  have hd₃ : 2 * (1 + (ζ.im : ℂ)) + (1 - ζ.re + ζ.im) * (s - 1) ≠ 0 := by
    intro he
    apply hden
    field_simp [hc', hc]
    linear_combination he
  field_simp [hsi, hd₂, hd₃, hc, hc']
  apply Complex.ext <;> norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.add_im, Complex.sub_im, Complex.mul_im]
  all_goals grind only


def compactIntegral (μ : FiniteMeasure Angle) (s : ℂ) : ℂ :=
  ∫ θ : Angle, compactKernel (boundaryParameter θ) (boundaryWeight θ) s ∂(μ : Measure Angle)

theorem compactKernel_integrable (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) :
    Integrable (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) s)
      (μ : Measure Angle) := by
  have hc : Continuous (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) s) := by
    exact (Complex.continuous_ofReal.comp continuous_boundaryWeight).div
      (continuous_const.add (continuous_const.mul
        (Complex.continuous_ofReal.comp continuous_boundaryParameter)))
      (fun θ => compactDen_ne_zero (boundaryParameter_mem θ) hs)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem compactKernel_norm_le_two {s : ℂ} (hs : ‖s - 1‖ < 1 / 2) (θ : Angle) :
    ‖compactKernel (boundaryParameter θ) (boundaryWeight θ) s‖ ≤ 2 := by
  have ht := boundaryParameter_mem θ
  have htw := boundaryWeight_le_one θ
  have htp := boundaryWeight_pos θ
  have ht' : ‖(boundaryParameter θ : ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  have hsmall : ‖(s - 1) * (boundaryParameter θ : ℂ)‖ < 1 / 2 := by
    rw [norm_mul]
    calc
      ‖s - 1‖ * ‖(boundaryParameter θ : ℂ)‖ ≤ ‖s - 1‖ * 1 := mul_le_mul_of_nonneg_left ht' (norm_nonneg _)
      _ < 1 / 2 := by simpa using hs
  have hden : 1 / 2 < ‖1 + (s - 1) * (boundaryParameter θ : ℂ)‖ := by
    have he := norm_sub_norm_le (1 : ℂ) (-((s - 1) * (boundaryParameter θ : ℂ)))
    simp only [norm_one, norm_neg, sub_neg_eq_add] at he
    linarith
  rw [compactKernel, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htp]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 + (s - 1) * (boundaryParameter θ : ℂ)‖)).mpr
  linarith

theorem continuousAt_compactIntegral_one (μ : FiniteMeasure Angle) :
    ContinuousAt (compactIntegral μ) 1 := by
  apply continuousAt_of_dominated (bound := fun _ => 2)
  · filter_upwards with s
    have hm : Measurable (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) s) := by
      unfold compactKernel
      exact (Complex.continuous_ofReal.comp continuous_boundaryWeight).measurable.div
        (continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_boundaryParameter))).measurable
    exact hm.aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with s hs
    filter_upwards with θ
    exact compactKernel_norm_le_two (by simpa only [mem_ball, dist_eq_norm] using hs) θ
  · exact integrable_const _
  · filter_upwards with θ
    apply ContinuousAt.div continuousAt_const
      (continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul continuousAt_const))
    simp



theorem pick_divided_difference_of_continuous {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → 0 ≤ (P s).im)
    (hR : ∀ x : ℝ, 0 < x → ContinuousAt P (x : ℂ) ∧ (P (x : ℂ)).im = 0) :
    ∃ μ : FiniteMeasure Angle, ∀ s : ℂ, 0 < s.im →
      P s - P 1 = (s - 1) * compactIntegral μ s := by
  obtain ⟨μ, a, hμ, hrep⟩ := upper_half_plane_representation_with_support_of_continuous hP hn hR
  let A : ℂ := (a : ℂ) + ∫ θ : Angle, (1 - 2 * (boundaryParameter θ : ℂ)) ∂(μ : Measure Angle)
  have hiA : Integrable (fun θ : Angle => (1 - 2 * (boundaryParameter θ : ℂ))) (μ : Measure Angle) :=
    (continuous_const.sub (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_boundaryParameter))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (s : ℂ) (hs : 0 < s.im) : P s = A + (s - 1) * compactIntegral μ s := by
    rw [hrep _ hs, diskIntegral, ← integral_const_mul]
    have heq : (fun θ : Angle => I * herglotzRieszKernel 0 (toDisk s) (circleMap 0 1 θ)) =ᵐ[(μ : Measure Angle)]
        (fun θ : Angle => (1 - 2 * (boundaryParameter θ : ℂ)) +
          (s - 1) * compactKernel (boundaryParameter θ) (boundaryWeight θ) s) := by
      filter_upwards [hμ] with θ hθ
      simpa only [boundaryParameter, boundaryWeight, max_eq_right hθ] using
        compactKernel_boundary hs (by simp only [norm_circleMap_zero, abs_one]) hθ
    rw [integral_congr_ae heq, integral_add hiA ((compactKernel_integrable μ (Or.inl hs)).const_mul _),
      integral_const_mul]
    exact (add_assoc _ _ _).symm
  have hlim : Tendsto (fun n : ℕ => (1 : ℂ) + ((1 - approachRadius n : ℝ) : ℂ) * I) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := (1 : ℝ))).sub approachRadius_tendsto)).mul_const I)
  have hseq (n : ℕ) : 0 < ((1 : ℂ) + ((1 - approachRadius n : ℝ) : ℂ) * I).im := by
    simpa using sub_pos.mpr (approachRadius_mem n).2
  have hA : P 1 = A := by
    have hleft := (hR 1 (by norm_num)).1.tendsto.comp hlim
    have hright := (tendsto_const_nhds (x := A)).add
      ((hlim.sub (tendsto_const_nhds (x := (1 : ℂ)))).mul ((continuousAt_compactIntegral_one μ).tendsto.comp hlim))
    simp only [sub_self, zero_mul, add_zero] at hright
    exact tendsto_nhds_unique hleft (hright.congr (fun n => (he _ (hseq n)).symm))
  exact ⟨μ, fun s hs => by rw [he s hs, hA]; ring⟩


theorem pick_divided_difference {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → 0 ≤ (P s).im)
    (hR : ∀ x : ℝ, 0 < x → AnalyticAt ℂ P (x : ℂ) ∧ (P (x : ℂ)).im = 0) :
    ∃ μ : FiniteMeasure Angle, ∀ s : ℂ, 0 < s.im →
      P s - P 1 = (s - 1) * compactIntegral μ s :=
  pick_divided_difference_of_continuous hP hn
    (fun x hx => ⟨(hR x hx).1.continuousAt, (hR x hx).2⟩)

theorem compactKernel_im (t w : ℝ) (s : ℂ) :
    (compactKernel t w s).im = -(w * t * s.im) / Complex.normSq (1 + (s - 1) * t) := by
  simp only [compactKernel, Complex.div_im, Complex.ofReal_im, zero_mul,
    Complex.ofReal_re, Complex.add_im, Complex.one_im, Complex.mul_im,
    Complex.sub_im, sub_zero, mul_zero, zero_add]
  ring

theorem mul_compactKernel_im (t w : ℝ) (s : ℂ) :
    (s * compactKernel t w s).im = w * (1 - t) * s.im / Complex.normSq (1 + (s - 1) * t) := by
  rw [compactKernel, ← mul_div_assoc, Complex.div_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.one_im, Complex.one_re, sub_zero, mul_zero, zero_add]
  ring

theorem complex_im_integral {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f : X → ℂ} (hf : Integrable f ν) : (∫ x, f x ∂ν).im = ∫ x, (f x).im ∂ν :=
  (Complex.imCLM.integral_comp_comm hf).symm

theorem compactIntegral_im_nonpos (μ : FiniteMeasure Angle) {s : ℂ} (hs : 0 < s.im) :
    (compactIntegral μ s).im ≤ 0 := by
  rw [compactIntegral, complex_im_integral (compactKernel_integrable μ (Or.inl hs))]
  apply integral_nonpos
  intro θ
  change (compactKernel _ _ _).im ≤ 0
  rw [compactKernel_im]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg
    (mul_nonneg (boundaryWeight_pos θ).le (boundaryParameter_mem θ).1) hs.le))
    (Complex.normSq_nonneg _)

theorem mul_compactIntegral_im_nonneg (μ : FiniteMeasure Angle) {s : ℂ} (hs : 0 < s.im) :
    0 ≤ (s * compactIntegral μ s).im := by
  rw [compactIntegral, ← integral_const_mul,
    complex_im_integral ((compactKernel_integrable μ (Or.inl hs)).const_mul s)]
  apply integral_nonneg
  intro θ
  change 0 ≤ (s * compactKernel _ _ _).im
  rw [mul_compactKernel_im]
  exact div_nonneg (mul_nonneg (mul_nonneg (boundaryWeight_pos θ).le
    (sub_nonneg.mpr (boundaryParameter_mem θ).2)) hs.le) (Complex.normSq_nonneg _)

theorem compactIntegral_ne_zero (μ : FiniteMeasure Angle)
    (hμ : (μ : Measure Angle) ≠ 0) {s : ℂ} (hs : 0 < s.im) : compactIntegral μ s ≠ 0 := by
  let F : Angle → ℝ := fun θ => (s * compactKernel (boundaryParameter θ) (boundaryWeight θ) s).im -
    (compactKernel (boundaryParameter θ) (boundaryWeight θ) s).im
  have hF (θ : Angle) : 0 < F θ := by
    dsimp [F]
    rw [mul_compactKernel_im, compactKernel_im]
    have he : boundaryWeight θ * (1 - boundaryParameter θ) * s.im - -(boundaryWeight θ * boundaryParameter θ * s.im) =
        boundaryWeight θ * s.im := by ring
    rw [← sub_div, he]
    exact div_pos (mul_pos (boundaryWeight_pos θ) hs)
      (Complex.normSq_pos.mpr (compactDen_ne_zero (boundaryParameter_mem θ) (Or.inl hs)))
  have hi := compactKernel_integrable μ (Or.inl hs)
  have hFi : Integrable F (μ : Measure Angle) :=
    (Complex.imCLM.integrable_comp (hi.const_mul s)).sub (Complex.imCLM.integrable_comp hi)
  have hp : 0 < ∫ θ, F θ ∂(μ : Measure Angle) := by
    rw [integral_pos_iff_support_of_nonneg (fun θ => (hF θ).le) hFi]
    have he : Function.support F = univ := by ext θ; simp [Function.mem_support, (hF θ).ne']
    rw [he]
    exact Measure.measure_univ_pos.mpr hμ
  have he : (∫ θ, F θ ∂(μ : Measure Angle)) =
      (s * compactIntegral μ s).im - (compactIntegral μ s).im := by
    have hi₁ : Integrable (fun θ => (s * compactKernel (boundaryParameter θ) (boundaryWeight θ) s).im)
        (μ : Measure Angle) := Complex.imCLM.integrable_comp (hi.const_mul s)
    have hi₂ : Integrable (fun θ => (compactKernel (boundaryParameter θ) (boundaryWeight θ) s).im)
        (μ : Measure Angle) := Complex.imCLM.integrable_comp hi
    dsimp [F]
    rw [integral_sub hi₁ hi₂, ← complex_im_integral (hi.const_mul s), ← complex_im_integral hi,
      integral_const_mul]
    rfl
  intro hz
  rw [he, hz, mul_zero, Complex.zero_im, sub_self] at hp
  exact lt_irrefl _ hp

theorem continuousAt_compactIntegral (μ : FiniteMeasure Angle) {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt (compactIntegral μ) s := by
  let d : ℝ := min 1 (s.re / 2)
  have hd : 0 < d := lt_min zero_lt_one (half_pos hs)
  apply continuousAt_of_dominated (bound := fun _ => 1 / d)
  · filter_upwards with z
    have hm : Measurable (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) z) :=
      (Complex.continuous_ofReal.comp continuous_boundaryWeight).measurable.div
        (continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_boundaryParameter))).measurable
    exact hm.aestronglyMeasurable
  · have he : ∀ᶠ z : ℂ in 𝓝 s, s.re / 2 < z.re :=
      (Complex.continuous_re.continuousAt.tendsto).eventually (Ioi_mem_nhds (by linarith))
    filter_upwards [he] with z hz
    filter_upwards with θ
    have ht := boundaryParameter_mem θ
    have hd1 : d ≤ 1 := min_le_left _ _
    have hdz : d ≤ z.re := (min_le_right _ _).trans hz.le
    have hdr : d ≤ (1 + (z - 1) * (boundaryParameter θ : ℂ)).re := by
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.sub_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      nlinarith [mul_nonneg (sub_nonneg.mpr hd1) (sub_nonneg.mpr ht.2),
        mul_nonneg (sub_nonneg.mpr hdz) ht.1]
    have hdn : d ≤ ‖1 + (z - 1) * (boundaryParameter θ : ℂ)‖ := hdr.trans (Complex.re_le_norm _)
    rw [compactKernel, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (boundaryWeight_pos θ)]
    exact div_le_div₀ zero_le_one (boundaryWeight_le_one θ) hd hdn
  · exact integrable_const _
  · filter_upwards with θ
    exact continuousAt_const.div
      (continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul continuousAt_const))
      (compactDen_ne_zero (boundaryParameter_mem θ) (Or.inr hs))



theorem upper_boundary_eq {F G : ℂ → ℂ} {x : ℝ}
    (hF : ContinuousAt F (x : ℂ)) (hG : ContinuousAt G (x : ℂ))
    (he : ∀ s : ℂ, 0 < s.im → F s = G s) : F (x : ℂ) = G (x : ℂ) := by
  let z : ℕ → ℂ := fun n => (x : ℂ) + ((1 - approachRadius n : ℝ) : ℂ) * I
  have hz : Tendsto z atTop (𝓝 (x : ℂ)) := by
    simpa [z] using (tendsto_const_nhds (x := (x : ℂ))).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := (1 : ℝ))).sub approachRadius_tendsto)).mul_const I)
  have hi (n : ℕ) : 0 < (z n).im := by
    simpa [z] using sub_pos.mpr (approachRadius_mem n).2
  exact tendsto_nhds_unique (hF.tendsto.comp hz)
    ((hG.tendsto.comp hz).congr (fun n => (he _ (hi n)).symm))

theorem analyticAt_dslope {P : ℂ → ℂ} {a : ℂ} (hP : AnalyticAt ℂ P a) :
    AnalyticAt ℂ (dslope P a) a := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [hP.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hza
    exact (differentiableAt_dslope_of_ne hza).mpr hz.differentiableAt
  · exact continuousAt_dslope_same.mpr hP.differentiableAt



theorem pick_dslope_representation {P : ℂ → ℂ}
    (hP : AnalyticOnNhd ℂ P {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → 0 ≤ (P s).im)
    (hR : ∀ x : ℝ, 0 < x → AnalyticAt ℂ P (x : ℂ) ∧ (P (x : ℂ)).im = 0) :
    ∃ μ : FiniteMeasure Angle,
      (∀ s : ℂ, 0 < s.im → dslope P 1 s = compactIntegral μ s) ∧
      (∀ x : ℝ, 0 < x → dslope P 1 (x : ℂ) = compactIntegral μ (x : ℂ)) := by
  obtain ⟨μ, hμ⟩ := pick_divided_difference hP hn hR
  have he (s : ℂ) (hs : 0 < s.im) : dslope P 1 s = compactIntegral μ s := by
    have hs' : s ≠ 1 := by intro h; simp [h] at hs
    rw [dslope_of_ne _ hs', slope, smul_eq_mul, vsub_eq_sub, hμ s hs]
    field_simp [sub_ne_zero.mpr hs']
  refine ⟨μ, he, ?_⟩
  intro x hx
  apply upper_boundary_eq _ (continuousAt_compactIntegral μ (by simpa using hx)) he
  rcases eq_or_ne (x : ℂ) 1 with h | h
  · rw [h]
    exact continuousAt_dslope_same.mpr (hR 1 (by norm_num)).1.differentiableAt
  · exact (continuousAt_dslope_of_ne h).mpr (hR x hx).1.continuousAt


theorem real_compactDen_pos {t : ℝ} (ht : t ∈ Icc 0 1) {x : ℝ} (hx : 0 < x) :
    0 < 1 + (x - 1) * t := by
  by_cases h : t = 0
  · simp [h]
  · have hp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    nlinarith [mul_pos hx hp, ht.2]

def realResolvent (x : ℝ) (hx : 0 < x) : C(Angle, ℝ) where
  toFun θ := (1 + (x - 1) * boundaryParameter θ)⁻¹
  continuous_toFun :=
    (continuous_const.add (continuous_const.mul continuous_boundaryParameter)).inv₀
      (fun θ => (real_compactDen_pos (boundaryParameter_mem θ) hx).ne')

def resolventDensity (A : ℝ) (hA : 0 < A) : C(Angle, ℝ) where
  toFun θ := A * boundaryWeight θ / (1 + A * boundaryParameter θ)
  continuous_toFun :=
    (continuous_const.mul continuous_boundaryWeight).div
      (continuous_const.add (continuous_const.mul continuous_boundaryParameter))
      (fun θ => by nlinarith [(boundaryParameter_mem θ).1])

theorem resolventDensity_nonneg {A : ℝ} (hA : 0 < A) (θ : Angle) :
    0 ≤ resolventDensity A hA θ := by
  dsimp [resolventDensity]
  exact div_nonneg (mul_nonneg hA.le (boundaryWeight_pos θ).le)
    (by nlinarith [(boundaryParameter_mem θ).1])

def resolventMeasure (μ : FiniteMeasure Angle) (A : ℝ) (hA : 0 < A) : FiniteMeasure Angle :=
  densityMeasure (μ : Measure Angle) (resolventDensity A hA)

theorem mass_resolventMeasure (μ : FiniteMeasure Angle) {A : ℝ} (hA : 0 < A) :
    ((resolventMeasure μ A hA).mass : ℝ) =
      A * ∫ θ : Angle, boundaryWeight θ / (1 + A * boundaryParameter θ) ∂(μ : Measure Angle) := by
  rw [resolventMeasure, mass_densityMeasure _ _ (resolventDensity_nonneg hA), ← integral_const_mul]
  congr 1
  ext θ
  simp only [resolventDensity, ContinuousMap.coe_mk, mul_div_assoc]

theorem integrable_realKernel (μ : FiniteMeasure Angle) {x : ℝ} (hx : 0 < x) :
    Integrable (fun θ => boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ)) (μ : Measure Angle) := by
  exact (continuous_boundaryWeight.div
    (continuous_const.add (continuous_const.mul continuous_boundaryParameter))
    (fun θ => (real_compactDen_pos (boundaryParameter_mem θ) hx).ne')).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem resolvent_algebra (μ : FiniteMeasure Angle) {A x : ℝ} (hA : 0 < A) (hx : 0 < x) :
    (x - 1) * (∫ θ : Angle, boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ) ∂(μ : Measure Angle)) =
      ((resolventMeasure μ A hA).mass : ℝ) -
        (1 - (x - 1) / A) * ∫ θ : Angle, realResolvent x hx θ ∂(resolventMeasure μ A hA : Measure Angle) := by
  rw [resolventMeasure, mass_densityMeasure _ _ (resolventDensity_nonneg hA),
    integral_densityMeasure _ _ (resolventDensity_nonneg hA), ← integral_const_mul,
    ← integral_const_mul, ← integral_sub]
  · apply integral_congr_ae
    filter_upwards with θ
    have hd := (real_compactDen_pos (boundaryParameter_mem θ) hx).ne'
    have hdA : 1 + A * boundaryParameter θ ≠ 0 := by
      nlinarith [(boundaryParameter_mem θ).1]
    dsimp [realResolvent, resolventDensity]
    field_simp [hd, hdA, hA.ne']
    have hdA' : 1 + boundaryParameter θ * A ≠ 0 := by simpa [mul_comm] using hdA
    field_simp [hdA']
    ring
  · exact (resolventDensity A hA).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (((resolventDensity A hA).continuous.mul (realResolvent x hx).continuous).const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)





theorem compact_stieltjes_of_difference {R : ℝ → ℝ} (μ : FiniteMeasure Angle)
    (hR : ∀ x : ℝ, 0 < x → 0 ≤ R x)
    (he : ∀ x : ℝ, 0 < x → R x = R 1 - (x - 1) *
      ∫ θ : Angle, boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ) ∂(μ : Measure Angle)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ν : FiniteMeasure Angle,
      ∀ x : ℝ, 0 < x → R x = c + ∫ θ : Angle, (1 + (x - 1) * boundaryParameter θ)⁻¹ ∂(ν : Measure Angle) := by
  let νs : ℕ → FiniteMeasure Angle := fun n => resolventMeasure μ ((n : ℝ) + 1) (by positivity)
  let C : ℝ≥0 := ⟨R 1, hR 1 (by norm_num)⟩
  have hm (n : ℕ) : (νs n).mass ≤ C := by
    change ((νs n).mass : ℝ) ≤ (C : ℝ)
    rw [show νs n = resolventMeasure μ ((n : ℝ) + 1) (by positivity) from rfl,
      mass_resolventMeasure]
    have hr := hR ((n : ℝ) + 2) (by positivity)
    rw [he _ (by positivity)] at hr
    dsimp [C]
    rw [show (n : ℝ) + 2 - 1 = (n : ℝ) + 1 by ring] at hr
    exact sub_nonneg.mp hr
  obtain ⟨ν, hν, hc⟩ :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace Angle C).exists_mapClusterPt
      (u := νs) (f := atTop) (by
        rw [Filter.le_principal_iff]
        change ∀ᶠ n : ℕ in atTop, (νs n).mass ≤ C
        exact Eventually.of_forall hm)
  let l : Filter ℕ := Filter.comap νs (𝓝 ν) ⊓ atTop
  have : NeBot l := neBot_inf_comap_iff_map'.mpr hc
  have hνs : Tendsto νs l (𝓝 ν) := tendsto_comap.mono_left inf_le_left
  have hmass : Tendsto (fun n => ((νs n).mass : ℝ)) l (𝓝 (ν.mass : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp
      (FiniteMeasure.continuous_mass.continuousAt.tendsto.comp hνs)
  refine ⟨R 1 - (ν.mass : ℝ), sub_nonneg.mpr (show (ν.mass : ℝ) ≤ R 1 from hν), ν, ?_⟩
  intro x hx
  have hi := (FiniteMeasure.continuous_integral_continuousMap (realResolvent x hx)).continuousAt.tendsto.comp hνs
  have hf : Tendsto (fun n : ℕ => 1 - (x - 1) / ((n : ℝ) + 1)) l (𝓝 1) := by
    have hd : Tendsto (fun n : ℕ => (x - 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat (x - 1)).comp (tendsto_add_atTop_nat 1)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hd.mono_left inf_le_right)
  have hlim := ((tendsto_const_nhds (x := R 1)).sub hmass).add (hf.mul hi)
  simp only [one_mul] at hlim
  apply tendsto_nhds_unique tendsto_const_nhds (hlim.congr (fun n => ?_))
  rw [he x hx, resolvent_algebra μ (by positivity : 0 < (n : ℝ) + 1) hx]
  change R 1 - ((νs n).mass : ℝ) + (1 - (x - 1) / ((n : ℝ) + 1)) * _ =
    R 1 - (((νs n).mass : ℝ) - (1 - (x - 1) / ((n : ℝ) + 1)) * _)
  dsimp only [Function.comp_apply, νs]
  ring


theorem compactIntegral_real (μ : FiniteMeasure Angle) (x : ℝ) :
    compactIntegral μ (x : ℂ) =
      ((∫ θ : Angle, boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ) ∂(μ : Measure Angle) : ℝ) : ℂ) := by
  rw [compactIntegral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with θ
  simp only [compactKernel, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one]



theorem compact_stieltjes_representation {R : ℂ → ℂ}
    (hR : AnalyticOnNhd ℂ R {s | 0 < s.im})
    (hn : ∀ s : ℂ, 0 < s.im → (R s).im ≤ 0)
    (hp : ∀ x : ℝ, 0 < x → AnalyticAt ℂ R (x : ℂ) ∧ (R (x : ℂ)).im = 0 ∧ 0 ≤ (R (x : ℂ)).re) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ν : FiniteMeasure Angle,
      ∀ x : ℝ, 0 < x → (R (x : ℂ)).re = c +
        ∫ θ : Angle, (1 + (x - 1) * boundaryParameter θ)⁻¹ ∂(ν : Measure Angle) := by
  obtain ⟨μ, hμ⟩ := pick_divided_difference (P := fun s => -R s)
    (fun s hs => (hR s hs).neg) (fun s hs => by simpa using hn s hs)
    (fun x hx => ⟨(hp x hx).1.neg, by simp [(hp x hx).2.1]⟩)
  have he (s : ℂ) (hs : 0 < s.im) : R s = R 1 - (s - 1) * compactIntegral μ s := by
    have := hμ s hs
    linear_combination -this
  have hb (x : ℝ) (hx : 0 < x) : R (x : ℂ) = R 1 - ((x : ℂ) - 1) * compactIntegral μ (x : ℂ) :=
    upper_boundary_eq (hp x hx).1.continuousAt
      (continuousAt_const.sub ((continuousAt_id.sub continuousAt_const).mul
        (continuousAt_compactIntegral μ (by simpa using hx)))) he
  apply compact_stieltjes_of_difference (R := fun x : ℝ => (R (x : ℂ)).re) μ
    (fun x hx => (hp x hx).2.2)
  intro x hx
  rw [hb x hx, compactIntegral_real]
  simp



theorem compactDen_loc_lower {s : ℂ} (hs : 0 < s.im ∨ 0 < s.re) :
    ∃ d : ℝ, 0 < d ∧ ∀ z ∈ ball s d, ∀ θ : Angle,
      d ≤ ‖1 + (z - 1) * (boundaryParameter θ : ℂ)‖ := by
  let D : ℂ → Angle → ℂ := fun z θ => 1 + (z - 1) * (boundaryParameter θ : ℂ)
  have hc : Continuous (fun θ : Angle => ‖D s θ‖) :=
    (continuous_const.add (continuous_const.mul
      (Complex.continuous_ofReal.comp continuous_boundaryParameter))).norm
  have hne : (univ : Set Angle).Nonempty := ⟨⟨0, le_rfl, by positivity⟩, mem_univ _⟩
  obtain ⟨θ₀, _, hmin⟩ := isCompact_univ.exists_isMinOn hne hc.continuousOn
  have hp : 0 < ‖D s θ₀‖ := norm_pos_iff.mpr (compactDen_ne_zero (boundaryParameter_mem θ₀) hs)
  refine ⟨‖D s θ₀‖ / 2, half_pos hp, ?_⟩
  intro z hz θ
  have hlow : ‖D s θ₀‖ ≤ ‖D s θ‖ := hmin (mem_univ θ)
  have ht : ‖(boundaryParameter θ : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (boundaryParameter_mem θ).1]
      using (boundaryParameter_mem θ).2
  have hdiff : ‖D s θ - D z θ‖ ≤ ‖s - z‖ := by
    have he : D s θ - D z θ = (s - z) * (boundaryParameter θ : ℂ) := by dsimp [D]; ring
    rw [he, norm_mul]
    exact (mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_one _)
  have hnorm := norm_sub_norm_le (D s θ) (D z θ)
  have hnear : ‖s - z‖ < ‖D s θ₀‖ / 2 := by
    simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hz
  change ‖D s θ₀‖ / 2 ≤ ‖D z θ‖
  linarith

theorem hasDerivAt_compactKernel {t w : ℝ} {z : ℂ}
    (hn : 1 + (z - 1) * (t : ℂ) ≠ 0) :
    HasDerivAt (compactKernel t w)
      (-((w : ℂ) * t) / (1 + (z - 1) * (t : ℂ)) ^ 2) z := by
  have hd : HasDerivAt (fun s : ℂ => 1 + (s - 1) * (t : ℂ)) (t : ℂ) z := by
    simpa only [id_eq, one_mul] using (((hasDerivAt_id z).sub_const 1).mul_const (t : ℂ)).const_add 1
  convert! (hasDerivAt_const z (w : ℂ)).div hd hn using 1
  simp only [zero_mul, zero_sub]

theorem differentiableAt_compactIntegral (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) : DifferentiableAt ℂ (compactIntegral μ) s := by
  obtain ⟨d, hd, hden⟩ := compactDen_loc_lower hs
  let F' : ℂ → Angle → ℂ := fun z θ =>
    -((boundaryWeight θ : ℂ) * boundaryParameter θ) /
      (1 + (z - 1) * (boundaryParameter θ : ℂ)) ^ 2
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable
      (fun θ => compactKernel (boundaryParameter θ) (boundaryWeight θ) z) (μ : Measure Angle) := by
    intro z
    have hm : Measurable (fun θ : Angle => compactKernel (boundaryParameter θ) (boundaryWeight θ) z) := by
      unfold compactKernel
      exact (Complex.continuous_ofReal.comp continuous_boundaryWeight).measurable.div
        (continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_boundaryParameter))).measurable
    exact hm.aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' s) (μ : Measure Angle) := by
    have hm : Measurable (F' s) := by
      dsimp [F']
      apply Measurable.div
      · exact ((Complex.continuous_ofReal.comp continuous_boundaryWeight).mul
          (Complex.continuous_ofReal.comp continuous_boundaryParameter)).neg.measurable
      · exact ((continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp continuous_boundaryParameter))).pow 2).measurable
    exact hm.aestronglyMeasurable
  have hbound : ∀ᵐ θ : Angle ∂(μ : Measure Angle), ∀ z ∈ ball s d, ‖F' z θ‖ ≤ 1 / d ^ 2 := by
    filter_upwards with θ z hz
    have ht := boundaryParameter_mem θ
    have hw := boundaryWeight_le_one θ
    have hp := boundaryWeight_pos θ
    have hnum : ‖(boundaryWeight θ : ℂ) * boundaryParameter θ‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ht.1, abs_of_pos hp]
      exact (mul_le_mul hw ht.2 ht.1 zero_le_one).trans_eq (one_mul 1)
    dsimp [F']
    rw [norm_div, norm_neg, norm_pow]
    exact div_le_div₀ zero_le_one hnum (sq_pos_of_pos hd)
      (sq_le_sq₀ hd.le (norm_nonneg _) |>.mpr (hden z hz θ))
  have hdiff : ∀ᵐ θ : Angle ∂(μ : Measure Angle), ∀ z ∈ ball s d,
      HasDerivAt (fun u => compactKernel (boundaryParameter θ) (boundaryWeight θ) u) (F' z θ) z := by
    filter_upwards with θ z hz
    apply hasDerivAt_compactKernel
    exact norm_pos_iff.mp (hd.trans_le (hden z hz θ))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds s hd)
    (Eventually.of_forall hmeas) (compactKernel_integrable μ hs) hmeas' hbound
      (integrable_const (1 / d ^ 2)) hdiff).2.differentiableAt

theorem analyticAt_compactIntegral (μ : FiniteMeasure Angle) {s : ℂ}
    (hs : 0 < s.im ∨ 0 < s.re) : AnalyticAt ℂ (compactIntegral μ) s := by
  have hopen : IsOpen {s : ℂ | 0 < s.im ∨ 0 < s.re} :=
    (isOpen_lt continuous_const Complex.continuous_im).union
      (isOpen_lt continuous_const Complex.continuous_re)
  exact (DifferentiableOn.analyticOnNhd
    (fun z hz => (differentiableAt_compactIntegral μ hz).differentiableWithinAt) hopen) s hs




theorem compactIntegral_real_pos (μ : FiniteMeasure Angle) (hμ : (μ : Measure Angle) ≠ 0)
    {x : ℝ} (hx : 0 < x) : 0 < (compactIntegral μ (x : ℂ)).re := by
  rw [compactIntegral_real, Complex.ofReal_re]
  have hp (θ : Angle) : 0 < boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ) :=
    div_pos (boundaryWeight_pos θ) (real_compactDen_pos (boundaryParameter_mem θ) hx)
  rw [integral_pos_iff_support_of_nonneg (fun θ => (hp θ).le) (integrable_realKernel μ hx)]
  have he : Function.support (fun θ : Angle => boundaryWeight θ / (1 + (x - 1) * boundaryParameter θ)) =
      univ := by
    ext θ
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp θ).ne'
  rw [he]
  exact Measure.measure_univ_pos.mpr hμ

end EntropyPhotonNumber.Herglotz

end

end

end OAI

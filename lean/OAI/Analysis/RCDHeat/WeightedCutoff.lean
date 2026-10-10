import Mathlib
import OAI.Analysis.RCDHeat.RelaxedSlope

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: WeightedCutoff, MeasurableGluing, PointwiseMinimal, BoundedMultiplier, VaryingMultiplier, DerivativeSlope. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
open Metric
section WeightedCutoff
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X)

omit μ [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
noncomputable def clipUnit (a : ℝ) : ℝ := min (max a 0) 1

omit μ [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
 theorem clipUnit_lipschitz : LipschitzWith 1 clipUnit :=
  (LipschitzWith.id.max_const 0).min_const 1

omit μ [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
 theorem clipUnit_bounds (a : ℝ) : 0 ≤ clipUnit a ∧ clipUnit a ≤ 1 :=
  ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩

omit μ [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
 theorem clipUnit_eq_self {a : ℝ} (h : 0 ≤ a ∧ a ≤ 1) : clipUnit a = a := by
  rw [clipUnit, max_eq_left h.1, min_eq_left h.2]

omit μ [MetricSpace X] [MeasurableSpace X] [BorelSpace X] in
 theorem clipUnit_zero : clipUnit 0 = 0 := clipUnit_eq_self ⟨le_rfl, zero_le_one⟩

omit [MetricSpace X] [BorelSpace X] in
 theorem eLpNorm_mul_eq_weight (u : Lp ℝ 2 μ) {a : X → ℝ} (ha : Measurable a) :
    eLpNorm (fun x => a x * u x) 2 μ =
      eLpNorm a 2 (μ.withDensity fun x => ‖u x‖ₑ ^ 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := fun point => a point * u point)
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      (ha.mul (Lp.stronglyMeasurable u).measurable).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ha.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  rw [lintegral_withDensity_eq_lintegral_mul μ ((Lp.stronglyMeasurable u).measurable.enorm.pow_const 2)
    (ha.enorm.pow_const 2)]
  congr 1
  apply lintegral_congr
  intro x
  simp only [enorm_mul, mul_pow, Pi.mul_apply, mul_comm]

variable [ProperSpace X]

 

 theorem exists_weighted_lipschitz_cutoff (u : Lp ℝ 2 μ) {η : X → ℝ}
    (hη : Measurable η) (hb : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ θ : X → ℝ, (∃ C : ℝ≥0, LipschitzWith C θ) ∧ HasCompactSupport θ ∧
      (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
      eLpNorm (fun x => (θ x - η x) * u x) 2 μ ≤ ε := by
  let ν : Measure X := μ.withDensity fun x => ‖u x‖ₑ ^ 2
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity (by
    rw [lintegral_enorm_sq_Lp]
    exact ENNReal.ofReal_ne_top)
  have hην : MemLp η 2 ν := MemLp.of_bound hη.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]; exact (hb x).2)
  obtain ⟨g, hg, ⟨C, hC⟩, _, hs⟩ :=
    MemLp.exists_lipschitz_hasCompactSupport_eLpNorm_sub_le ν hην hε
  let θ : X → ℝ := clipUnit ∘ g
  refine ⟨θ, ⟨C, by simpa using clipUnit_lipschitz.comp hC⟩, ?_,
    fun x => clipUnit_bounds (g x), ?_⟩
  · apply HasCompactSupport.intro hs
    intro x hx
    have hgx : g x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp only [θ, Function.comp_apply, hgx, clipUnit_zero]
  · rw [eLpNorm_mul_eq_weight μ u (a := fun x => θ x - η x)
      ((clipUnit_lipschitz.continuous.measurable.comp hC.continuous.measurable).sub hη)]
    apply (eLpNorm_mono (g := η - g)
      ((clipUnit_lipschitz.continuous.measurable.comp hC.continuous.measurable).sub
        hη).aestronglyMeasurable ?_).trans hg
    intro x
    have hh := clipUnit_lipschitz.dist_le_mul (g x) (η x)
    rw [clipUnit_eq_self (hb x)] at hh
    simpa only [θ, Function.comp_apply, Real.dist_eq, NNReal.coe_one, one_mul,
      Real.norm_eq_abs, Pi.sub_apply, abs_sub_comm] using hh

end WeightedCutoff

section MeasurableGluing
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

noncomputable def unitMultiplier (η : X → ℝ) (hη : Measurable η)
    (hb : ∀ x, 0 ≤ η x ∧ η x ≤ 1) : Lp ℝ ∞ μ :=
  (memLp_top_of_bound hη.aestronglyMeasurable 1
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]; exact (hb x).2)).toLp η

 theorem unitMultiplier_coe (η : X → ℝ) (hη : Measurable η)
    (hb : ∀ x, 0 ≤ η x ∧ η x ≤ 1) :
    ⇑(unitMultiplier μ η hη hb) =ᵐ[μ] η := MemLp.coeFn_toLp _

variable [MetricSpace X] [BorelSpace X] [ProperSpace X]

 

 theorem IsRelaxedSlope.measurable_blend {f G H : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) (hH : IsRelaxedSlope μ f H)
    {η : X → ℝ} (hη : Measurable η) (hb : ∀ x, 0 ≤ η x ∧ η x ≤ 1) :
    IsRelaxedSlope μ f (lpMultiplier μ (unitMultiplier μ η hη hb) (G - H) + H) := by
  have hex (i : ℕ) := exists_weighted_lipschitz_cutoff μ (G - H) hη hb
    ((ENNReal.ofReal_pos.mpr (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) i)).ne')
  choose θ hθ hs hbound herr using hex
  choose C hC using hθ
  let θlp (i : ℕ) := unitMultiplier μ (θ i) (hC i).continuous.measurable (hbound i)
  let ηlp := unitMultiplier μ η hη hb
  let Ws (i : ℕ) : Lp ℝ 2 μ := lpMultiplier μ (θlp i) (G - H) + H
  let W : Lp ℝ 2 μ := lpMultiplier μ ηlp (G - H) + H
  have hrel (i : ℕ) : IsRelaxedSlope μ f (Ws i) :=
    hG.cutoff_blend μ hH (hC i) (hs i) (hbound i) (θlp i) (unitMultiplier_coe ..)
  apply IsRelaxedSlope.of_tendsto μ hrel tendsto_const_nhds
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' ..).mpr
  have heq (i : ℕ) :
      eLpNorm (⇑(Ws i) - ⇑W) 2 μ =
        eLpNorm (fun x => (θ i x - η x) * (G - H) x) 2 μ := by
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_add (lpMultiplier μ (θlp i) (G - H)) H,
      Lp.coeFn_add (lpMultiplier μ ηlp (G - H)) H,
      lpMultiplier_coe μ (θlp i) (G - H), lpMultiplier_coe μ ηlp (G - H),
      unitMultiplier_coe μ (θ i) (hC i).continuous.measurable (hbound i),
      unitMultiplier_coe μ η hη hb] with x ha hb' hc hd he hf
    change (lpMultiplier μ (θlp i) (G - H) + H) x -
      (lpMultiplier μ ηlp (G - H) + H) x = _
    simp only [Pi.add_apply] at ha hb'
    rw [ha, hb', hc, hd]
    change θlp i x * (G - H) x + H x - (ηlp x * (G - H) x + H x) = _
    rw [show θlp i x = θ i x from he, show ηlp x = η x from hf]
    ring
  change Tendsto (fun i => eLpNorm (⇑(Ws i) - ⇑W) 2 μ) atTop (𝓝 0)
  simp_rw [heq]
  have hδ : Tendsto (fun i : ℕ => ENNReal.ofReal ((1 / 2 : ℝ)^i)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ
    (fun _ => bot_le) herr

 

 theorem IsRelaxedSlope.inf {f G H : Lp ℝ 2 μ}
    (hG : IsRelaxedSlope μ f G) (hH : IsRelaxedSlope μ f H) :
    IsRelaxedSlope μ f (G ⊓ H) := by
  let s : Set X := {x | G x ≤ H x}
  have hs : MeasurableSet s := measurableSet_le (Lp.stronglyMeasurable G).measurable
    (Lp.stronglyMeasurable H).measurable
  let η : X → ℝ := s.indicator (fun _ => 1)
  have hη : Measurable η := measurable_const.indicator hs
  have hb (x : X) : 0 ≤ η x ∧ η x ≤ 1 := by
    by_cases hx : x ∈ s <;> simp [η, hx]
  have heq : lpMultiplier μ (unitMultiplier μ η hη hb) (G - H) + H = G ⊓ H := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (lpMultiplier μ (unitMultiplier μ η hη hb) (G - H)) H,
      lpMultiplier_coe μ (unitMultiplier μ η hη hb) (G - H),
      unitMultiplier_coe μ η hη hb, Lp.coeFn_sub G H, Lp.coeFn_inf G H]
      with x ha hb' hc hd he
    simp only [Pi.add_apply, Pi.sub_apply, Pi.inf_apply] at *
    rw [ha, hb', hc, hd, he]
    by_cases hx : G x ≤ H x
    · simp [η, s, hx]
    · simp [η, s, hx, min_eq_right (le_of_not_ge hx)]
  rw [← heq]
  exact hG.measurable_blend μ hH hη hb

end MeasurableGluing

section PointwiseMinimal
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 

 theorem SobolevSpace.minimalSlope_le (f : SobolevSpace μ hQ) {H : Lp ℝ 2 μ}
    (hH : IsRelaxedSlope μ (SobolevSpace.toLp μ hQ f) H) :
    SobolevSpace.minimalSlope μ hQ f ≤ H := by
  let G := SobolevSpace.minimalSlope μ hQ f
  have hG : IsRelaxedSlope μ (SobolevSpace.toLp μ hQ f) G :=
    SobolevSpace.minimalSlope_isRelaxed μ hQ f
  have hmin := hG.inf μ hH
  have hn : ‖G ⊓ H‖ ≤ ‖G‖ := norm_le_norm_of_abs_le_abs (by
    rw [abs_of_nonneg (le_inf (IsRelaxedSlope.nonneg μ hG) (IsRelaxedSlope.nonneg μ hH)), abs_of_nonneg (IsRelaxedSlope.nonneg μ hG)]
    exact inf_le_left)
  have he := ENNReal.toReal_le_of_le_ofReal (by positivity) (hmin.energy_le μ)
  have hnG : ‖G‖ ^ 2 = 2 * (energyLp μ (SobolevSpace.toLp μ hQ f)).toReal :=
    SobolevSpace.minimalSlope_norm_sq μ hQ f
  have hnM : ‖G ⊓ H‖ ^ 2 = 2 * (energyLp μ (SobolevSpace.toLp μ hQ f)).toReal := by
    nlinarith [norm_nonneg G, norm_nonneg (G ⊓ H)]
  have hid : G = G ⊓ H := hG.unique_minimizer μ hmin hnG hnM
  exact hid.le.trans inf_le_right

omit [ProperSpace X] in
 theorem SobolevSpace.minimalSlope_nonneg (f : SobolevSpace μ hQ) :
    0 ≤ SobolevSpace.minimalSlope μ hQ f :=
  IsRelaxedSlope.nonneg μ (SobolevSpace.minimalSlope_isRelaxed μ hQ f)

 theorem SobolevSpace.minimalSlope_add_le (f g : SobolevSpace μ hQ) :
    SobolevSpace.minimalSlope μ hQ (f + g) ≤
      SobolevSpace.minimalSlope μ hQ f + SobolevSpace.minimalSlope μ hQ g := by
  apply SobolevSpace.minimalSlope_le μ hQ
  simpa only [map_add] using
    (SobolevSpace.minimalSlope_isRelaxed μ hQ f).add μ
      (SobolevSpace.minimalSlope_isRelaxed μ hQ g)

end PointwiseMinimal

section BoundedMultiplier
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

noncomputable def boundedMultiplier (η : X → ℝ) (hη : Measurable η)
    (B : ℝ≥0) (hb : ∀ x, |η x| ≤ B) : Lp ℝ ∞ μ :=
  (memLp_top_of_bound hη.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)).toLp η

 theorem boundedMultiplier_coe (η : X → ℝ) (hη : Measurable η)
    (B : ℝ≥0) (hb : ∀ x, |η x| ≤ B) :
    ⇑(boundedMultiplier μ η hη B hb) =ᵐ[μ] η := MemLp.coeFn_toLp _

 theorem boundedMultiplier_norm_le (η : X → ℝ) (hη : Measurable η)
    (B : ℝ≥0) (hb : ∀ x, |η x| ≤ B) :
    ‖boundedMultiplier μ η hη B hb‖ ≤ B := by
  rw [Lp.norm_def, eLpNorm_congr_ae (boundedMultiplier_coe μ η hη B hb),
    eLpNorm_exponent_top hη.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal B.coe_nonneg
    (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hb x))

 

 theorem lpMultiplier_tendsto_of_ae (u : Lp ℝ 2 μ)
    (ηs : ℕ → X → ℝ) (η : X → ℝ)
    (hs : ∀ i, Measurable (ηs i)) (hη : Measurable η)
    (B : ℝ≥0) (hb : ∀ i x, |ηs i x| ≤ B) (hbη : ∀ x, |η x| ≤ B)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun i => ηs i x) atTop (𝓝 (η x))) :
    Tendsto (fun i => lpMultiplier μ (boundedMultiplier μ (ηs i) (hs i) B (hb i)) u)
      atTop (𝓝 (lpMultiplier μ (boundedMultiplier μ η hη B hbη) u)) := by
  let ν := μ.withDensity fun x => ‖u x‖ₑ ^ 2
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity (by
    rw [lintegral_enorm_sq_Lp]; exact ENNReal.ofReal_ne_top)
  have hcn : ∀ᵐ x ∂ν, Tendsto (fun i => ηs i x) atTop (𝓝 (η x)) :=
    (withDensity_absolutelyContinuous μ _).ae_le hc
  have hd : Tendsto (fun i => ∫⁻ x, ‖ηs i x - η x‖ₑ ^ 2 ∂ν) atTop (𝓝 0) := by
    have hv := tendsto_lintegral_of_dominated_convergence (μ := ν)
      (fun _ : X => (ENNReal.ofReal (2 * (B : ℝ))) ^ 2)
      (fun i => ((hs i).sub hη).enorm.pow_const 2)
      (fun i => Eventually.of_forall fun x => by
        apply pow_le_pow_left'
        rw [← ofReal_norm]
        apply ENNReal.ofReal_le_ofReal
        calc
          ‖ηs i x - η x‖ ≤ |ηs i x| + |η x| := by
            simpa only [Real.norm_eq_abs] using norm_sub_le (ηs i x) (η x)
          _ ≤ 2 * (B : ℝ) := by linarith [hb i x, hbη x])
      (by
        rw [lintegral_const]
        exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          (measure_ne_top ν Set.univ))
      (f := fun _ => 0)
      (hcn.mono fun x hx => by
        simpa using ENNReal.Tendsto.pow (n := 2) (hx.sub_const (η x)).enorm)
    simpa only [lintegral_zero, Pi.sub_apply] using hv
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' ..).mpr
  have heq (i : ℕ) : eLpNorm
      (⇑(lpMultiplier μ (boundedMultiplier μ (ηs i) (hs i) B (hb i)) u) -
        ⇑(lpMultiplier μ (boundedMultiplier μ η hη B hbη) u)) 2 μ =
      (∫⁻ x, ‖ηs i x - η x‖ₑ ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    calc
      _ = eLpNorm (fun x => (ηs i x - η x) * u x) 2 μ := by
        apply eLpNorm_congr_ae
        filter_upwards [lpMultiplier_coe μ (boundedMultiplier μ (ηs i) (hs i) B (hb i)) u,
          lpMultiplier_coe μ (boundedMultiplier μ η hη B hbη) u,
          boundedMultiplier_coe μ (ηs i) (hs i) B (hb i),
          boundedMultiplier_coe μ η hη B hbη] with x h1 h2 h3 h4
        simp only [Pi.sub_apply, h1, h2, h3, h4, sub_mul]
      _ = eLpNorm (fun x => ηs i x - η x) 2 ν :=
        eLpNorm_mul_eq_weight μ u ((hs i).sub hη)
      _ = _ := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (f := fun point => ηs i point - η point)
          (by norm_num : (2 : ℝ≥0∞) ≠ 0)
          (by norm_num : (2 : ℝ≥0∞) ≠ ∞) ((hs i).sub hη).aestronglyMeasurable]
        norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two, one_div]
  simp_rw [heq]
  simpa only [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    Function.comp_def] using
    (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hd

end BoundedMultiplier

section VaryingMultiplier
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

 theorem lpMultiplier_tendsto_of_ae_of_tendsto
    {us : ℕ → Lp ℝ 2 μ} {u : Lp ℝ 2 μ} (hu : Tendsto us atTop (𝓝 u))
    (ηs : ℕ → X → ℝ) (η : X → ℝ)
    (hs : ∀ i, Measurable (ηs i)) (hη : Measurable η)
    (B : ℝ≥0) (hb : ∀ i x, |ηs i x| ≤ B) (hbη : ∀ x, |η x| ≤ B)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun i => ηs i x) atTop (𝓝 (η x))) :
    Tendsto (fun i => lpMultiplier μ (boundedMultiplier μ (ηs i) (hs i) B (hb i)) (us i))
      atTop (𝓝 (lpMultiplier μ (boundedMultiplier μ η hη B hbη) u)) := by
  let θs (i : ℕ) := boundedMultiplier μ (ηs i) (hs i) B (hb i)
  have hfixed := lpMultiplier_tendsto_of_ae μ u ηs η hs hη B hb hbη hc
  have hz : Tendsto (fun i => lpMultiplier μ (θs i) (us i - u)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hlim : Tendsto (fun i => (B : ℝ) * ‖us i - u‖) atTop (𝓝 0) := by
      simpa using (hu.sub_const u).norm.const_mul (B : ℝ)
    apply squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hlim
    exact (Lp.norm_smul_le (θs i) (us i - u)).trans
      (mul_le_mul_of_nonneg_right (boundedMultiplier_norm_le μ (ηs i) (hs i) B (hb i))
        (norm_nonneg _))
  have hid (i : ℕ) : lpMultiplier μ (θs i) u + lpMultiplier μ (θs i) (us i - u) =
      lpMultiplier μ (θs i) (us i) := by rw [map_sub]; abel
  change Tendsto (fun i => lpMultiplier μ (θs i) u) atTop
    (𝓝 (lpMultiplier μ (boundedMultiplier μ η hη B hbη) u)) at hfixed
  simpa only [hid, add_zero] using hfixed.add hz

end VaryingMultiplier

variable {X : Type u} [MetricSpace X]

 
 theorem localSlope_comp_hasDerivAt {φ : ℝ → ℝ} {f : X → ℝ} {x : X} {a : ℝ}
    (hφ : HasDerivAt φ a (f x)) (hf : ContinuousAt f x)
    (hfin : localSlope f x ≠ ∞) :
    localSlope (φ ∘ f) x ≤ ENNReal.ofReal |a| * localSlope f x := by
  have hε {ε : ℝ} (hε : 0 < ε) :
      localSlope (φ ∘ f) x ≤ ENNReal.ofReal (|a| + ε) * localSlope f x := by
    have he := hf.eventually (hφ.isLittleO.bound hε)
    obtain ⟨t, ht, hb⟩ := Metric.mem_nhds_iff.mp he
    rw [localSlope_eq_iInf_scale f x]
    simp only [ENNReal.mul_iInf (fun h => (ENNReal.ofReal_ne_top h).elim)]
    refine le_iInf fun j => ?_
    let r : ℝ := 1 / (j + 1 : ℝ)
    have hr : 0 < r := by positivity
    refine iInf_le_of_le (min t r) (iInf_le_of_le (lt_min ht hr) ?_)
    refine iSup_le fun y => iSup_le fun hy => iSup_le fun hyx => ?_
    have he' := hb (show y ∈ Metric.ball x t by
      rw [Metric.mem_ball, dist_comm]; exact hy.trans_le (min_le_left _ _))
    have hquot : |φ (f y) - φ (f x)| ≤ (|a| + ε) * |f y - f x| := by
      have hid : φ (f y) - φ (f x) =
          (φ (f y) - φ (f x) - (f y - f x) * a) + (f y - f x) * a := by ring
      rw [hid]
      apply (abs_add_le _ _).trans
      simp only [Set.mem_ofPred_eq, Real.norm_eq_abs, smul_eq_mul] at he'
      rw [abs_mul]
      nlinarith [abs_nonneg (f y - f x)]
    have hd := dist_pos.mpr (Ne.symm hyx)
    calc
      _ ≤ ENNReal.ofReal ((|a| + ε) * (|f y - f x| / dist x y)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right hquot hd.le
      _ = ENNReal.ofReal (|a| + ε) * ENNReal.ofReal (|f y - f x| / dist x y) :=
        ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := mul_le_mul' le_rfl (slopeAtScale_term_le f
        (hy.trans_le (min_le_right _ _)) hyx)
  have hlim : Tendsto (fun ε : ℝ => ENNReal.ofReal (|a| + ε) * localSlope f x)
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal |a| * localSlope f x)) := by
    have he : Tendsto (fun ε : ℝ => ENNReal.ofReal (|a| + ε))
        (𝓝[>] 0) (𝓝 (ENNReal.ofReal |a|)) := by
      have ht := (tendsto_const_nhds (x := |a|)).add
        (show Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds)
      simpa only [add_zero, Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    exact ENNReal.Tendsto.mul_const he (Or.inr hfin)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε'
  exact hε hε'

end RegularPointCoordinates

end OAI

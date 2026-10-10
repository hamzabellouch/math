import Mathlib
import OAI.Analysis.RCDHeat.Density

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: SlopeMeasurability, SlopeCalculus, MinimalRelaxedSlope, RelaxedSlopeRecovery. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
section SlopeMeasurability
variable {X : Type u} [MetricSpace X]

noncomputable def slopeAtScale (f : X → ℝ) (r : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist x y < r) (_ : y ≠ x),
    ENNReal.ofReal (|f y - f x| / dist x y)

 theorem slopeAtScale_mono (f : X → ℝ) (x : X) {r s : ℝ} (hrs : r ≤ s) :
    slopeAtScale f r x ≤ slopeAtScale f s x := by
  refine iSup_le fun y => iSup_le fun hy => iSup_le fun hyx => ?_
  exact le_iSup_of_le y (le_iSup_of_le (hy.trans_le hrs) (le_iSup_of_le hyx le_rfl))

 theorem slopeAtScale_lowerSemicontinuous {f : X → ℝ} (hf : Continuous f) (r : ℝ) :
    LowerSemicontinuous (slopeAtScale f r) := by
  intro x a ha
  simp only [slopeAtScale, lt_iSup_iff] at ha
  obtain ⟨y, hy, hyx, ha⟩ := ha
  have hd : dist x y ≠ 0 := dist_ne_zero.mpr (Ne.symm hyx)
  have hc : ContinuousAt (fun z => ENNReal.ofReal (|f y - f z| / dist z y)) x :=
    ENNReal.continuous_ofReal.continuousAt.comp
      (((continuous_const.sub hf).abs.continuousAt).div
        (continuous_id.dist continuous_const).continuousAt hd)
  have hr : ∀ᶠ z in 𝓝 x, dist z y < r :=
    (continuous_id.dist continuous_const).continuousAt.eventually (gt_mem_nhds hy)
  have hn : ∀ᶠ z in 𝓝 x, y ≠ z :=
    Filter.Eventually.mono
      (isClosed_singleton.isOpen_compl.mem_nhds (show x ∈ ({y} : Set X)ᶜ from Ne.symm hyx))
      (fun _ hz => Ne.symm hz)
  filter_upwards [hc.lowerSemicontinuousAt a ha, hr, hn] with z haz hzr hyz
  exact haz.trans_le (le_iSup_of_le y
    (le_iSup_of_le hzr (le_iSup_of_le hyz le_rfl)))

 theorem localSlope_eq_iInf_scale (f : X → ℝ) (x : X) :
    localSlope f x = ⨅ j : ℕ, slopeAtScale f (1 / (j + 1 : ℝ)) x := by
  apply le_antisymm
  · refine le_iInf fun j => ?_
    exact iInf_le_of_le (1 / (j + 1 : ℝ)) (iInf_le_of_le (by positivity) le_rfl)
  · refine le_iInf fun r => le_iInf fun hr => ?_
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt hr
    exact (iInf_le (fun j : ℕ => slopeAtScale f (1 / (j + 1 : ℝ)) x) j).trans
      (slopeAtScale_mono f x hj.le)

 theorem localSlope_measurable [MeasurableSpace X] [BorelSpace X]
    {f : X → ℝ} (hf : Continuous f) : Measurable (localSlope f) := by
  simp_rw [funext (localSlope_eq_iInf_scale f)]
  exact Measurable.iInf fun j => (slopeAtScale_lowerSemicontinuous hf (1 / (j + 1 : ℝ))).measurable

end SlopeMeasurability
section SlopeCalculus
variable {X : Type u} [MetricSpace X]

 theorem slopeAtScale_term_le (f : X → ℝ) {x y : X} {r : ℝ}
    (hy : dist x y < r) (hyx : y ≠ x) :
    ENNReal.ofReal (|f y - f x| / dist x y) ≤ slopeAtScale f r x := by
  exact le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le hyx le_rfl))

 theorem slopeAtScale_add_le (f g : X → ℝ) (x : X) (r : ℝ) :
    slopeAtScale (fun y => f y + g y) r x ≤ slopeAtScale f r x + slopeAtScale g r x := by
  refine iSup_le fun y => iSup_le fun hy => iSup_le fun hyx => ?_
  have hd := dist_pos.mpr (Ne.symm hyx)
  calc
    _ ≤ ENNReal.ofReal (|f y - f x| / dist x y + |g y - g x| / dist x y) := by
      apply ENNReal.ofReal_le_ofReal
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ hd.le
      simpa only [add_sub_add_comm] using abs_add_le (f y - f x) (g y - g x)
    _ = ENNReal.ofReal (|f y - f x| / dist x y) +
        ENNReal.ofReal (|g y - g x| / dist x y) :=
      ENNReal.ofReal_add (div_nonneg (abs_nonneg _) hd.le) (div_nonneg (abs_nonneg _) hd.le)
    _ ≤ _ := add_le_add (slopeAtScale_term_le f hy hyx) (slopeAtScale_term_le g hy hyx)

 theorem localSlope_add_le (f g : X → ℝ) (x : X) :
    localSlope (fun y => f y + g y) x ≤ localSlope f x + localSlope g x := by
  apply ENNReal.le_iInf₂_add_iInf₂
  intro r hr s hs
  calc
    _ ≤ slopeAtScale (fun y => f y + g y) (min r s) x :=
      iInf_le_of_le (min r s) (iInf_le_of_le (lt_min hr hs) le_rfl)
    _ ≤ slopeAtScale f (min r s) x + slopeAtScale g (min r s) x :=
      slopeAtScale_add_le f g x (min r s)
    _ ≤ _ := add_le_add (slopeAtScale_mono f x (min_le_left _ _))
      (slopeAtScale_mono g x (min_le_right _ _))

 theorem localSlope_congr_nhds {f g : X → ℝ} {x : X} (hfg : f =ᶠ[𝓝 x] g) :
    localSlope f x = localSlope g x := by
  have hbase : f x = g x := hfg.self_of_nhds
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hfg
  have hle : ∀ f g : X → ℝ, f x = g x →
      (∀ y ∈ Metric.ball x r, f y = g y) → localSlope f x ≤ localSlope g x := by
    intro f g hx heq
    refine le_iInf fun s => le_iInf fun hs => ?_
    refine iInf_le_of_le (min r s) (iInf_le_of_le (lt_min hr hs) ?_)
    refine iSup_le fun y => iSup_le fun hy => iSup_le fun hyx => ?_
    have hyr : y ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_comm]
      exact hy.trans_le (min_le_left _ _)
    rw [heq y hyr, hx]
    exact le_iSup_of_le y (le_iSup_of_le (hy.trans_le (min_le_right _ _))
      (le_iSup_of_le hyx le_rfl))
  exact le_antisymm (hle f g hbase hball) (hle g f hbase.symm (fun y hy => (hball hy).symm))

 theorem localSlope_mul_le_eps {f g : X → ℝ} {x : X} (hf : ContinuousAt f x)
    {ε : ℝ} (hε : 0 < ε) :
    localSlope (fun y => f y * g y) x ≤
      ENNReal.ofReal (|f x| + ε) * localSlope g x +
        ENNReal.ofReal |g x| * localSlope f x := by
  have hn : ∀ᶠ y in 𝓝 x, |f y| < |f x| + ε :=
    hf.abs.eventually (gt_mem_nhds (by linarith))
  obtain ⟨t, ht, hbound⟩ := Metric.mem_nhds_iff.mp hn
  rw [localSlope_eq_iInf_scale g x, localSlope_eq_iInf_scale f x]
  simp only [ENNReal.mul_iInf (fun h => (ENNReal.ofReal_ne_top h).elim)]
  apply ENNReal.le_iInf_add_iInf
  intro j k
  let r : ℝ := 1 / (j + 1 : ℝ)
  let s : ℝ := 1 / (k + 1 : ℝ)
  have hr : 0 < r := by positivity
  have hs : 0 < s := by positivity
  refine iInf_le_of_le (min t (min r s)) (iInf_le_of_le (lt_min ht (lt_min hr hs)) ?_)
  refine iSup_le fun y => iSup_le fun hy => iSup_le fun hyx => ?_
  have hd := dist_pos.mpr (Ne.symm hyx)
  have hfy : |f y| ≤ |f x| + ε := (hbound (by
    rw [Metric.mem_ball, dist_comm]
    exact hy.trans_le (min_le_left _ _))).le
  have hquot : |f y * g y - f x * g x| / dist x y ≤
      (|f x| + ε) * (|g y - g x| / dist x y) +
        |g x| * (|f y - f x| / dist x y) := by
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    apply div_le_div_of_nonneg_right _ hd.le
    calc
      _ = |f y * (g y - g x) + g x * (f y - f x)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul, abs_mul]; gcongr
  calc
    _ ≤ ENNReal.ofReal ((|f x| + ε) * (|g y - g x| / dist x y) +
          |g x| * (|f y - f x| / dist x y)) := ENNReal.ofReal_le_ofReal hquot
    _ = ENNReal.ofReal (|f x| + ε) * ENNReal.ofReal (|g y - g x| / dist x y) +
          ENNReal.ofReal |g x| * ENNReal.ofReal (|f y - f x| / dist x y) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (abs_nonneg _)]
    _ ≤ _ := by
      apply add_le_add
      · apply mul_le_mul_right
        exact le_iSup_of_le y (le_iSup_of_le
          (hy.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
          (le_iSup_of_le hyx le_rfl))
      · apply mul_le_mul_right
        exact le_iSup_of_le y (le_iSup_of_le
          (hy.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
          (le_iSup_of_le hyx le_rfl))

 theorem localSlope_mul_le {f g : X → ℝ} {x : X} (hf : ContinuousAt f x)
    (hg : localSlope g x ≠ ∞) :
    localSlope (fun y => f y * g y) x ≤
      ENNReal.ofReal |f x| * localSlope g x + ENNReal.ofReal |g x| * localSlope f x := by
  have hlim : Tendsto (fun ε : ℝ =>
      ENNReal.ofReal (|f x| + ε) * localSlope g x +
        ENNReal.ofReal |g x| * localSlope f x) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal |f x| * localSlope g x +
        ENNReal.ofReal |g x| * localSlope f x)) := by
    apply (Filter.Tendsto.add _ tendsto_const_nhds)
    have he : Tendsto (fun ε : ℝ => ENNReal.ofReal (|f x| + ε)) (𝓝[>] 0)
        (𝓝 (ENNReal.ofReal |f x|)) := by
      have ht : Tendsto (fun ε : ℝ => |f x| + ε) (𝓝[>] (0 : ℝ)) (𝓝 (|f x| + 0)) :=
        tendsto_const_nhds.add nhdsWithin_le_nhds
      simpa only [add_zero, Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
    exact ENNReal.Tendsto.mul_const he (Or.inr hg)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact localSlope_mul_le_eps hf hε

end SlopeCalculus
section MinimalRelaxedSlope
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)

 
theorem energyLp_lowerSemicontinuous : LowerSemicontinuous (energyLp μ) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro a
  apply IsSeqClosed.isClosed
  intro fs f hfs hc
  exact (energyLp_le_liminf μ hc).trans
    (liminf_le_of_frequently_le' (Eventually.of_forall hfs).frequently)

omit [MetricSpace X] in
 
theorem lintegral_enorm_sq_Lp (G : Lp ℝ 2 μ) :
    (∫⁻ x, ‖G x‖ₑ ^ 2 ∂μ) = ENNReal.ofReal (‖G‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := ⇑G)
    (p := (2 : ℝ≥0)) (by norm_num) (Lp.aestronglyMeasurable G)
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] at h
  rw [← h, ← Lp.enorm_def]
  simp [enorm_eq_nnnorm, ENNReal.ofReal_pow, norm_nonneg]

variable [BorelSpace X]

 
theorem localSlope_toReal_memLp {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (he : slopeEnergy μ g ≠ ∞) :
    MemLp (fun x => (localSlope g x).toReal) 2 μ := by
  have hfin (x : X) : localSlope g x ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hg x)
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num)
    (by norm_num) (localSlope_measurable hg.continuous).ennreal_toReal.aestronglyMeasurable]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  simp_rw [Real.enorm_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin _)]
  exact ENNReal.lt_top_of_mul_ne_top_right he (by norm_num)

noncomputable def lipschitzSlopeLp {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (he : slopeEnergy μ g ≠ ∞) : Lp ℝ 2 μ :=
  (localSlope_toReal_memLp μ hg he).toLp (fun x => (localSlope g x).toReal)

theorem lipschitzSlopeLp_nonneg {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (he : slopeEnergy μ g ≠ ∞) :
    ∀ᵐ x ∂μ, 0 ≤ lipschitzSlopeLp μ hg he x := by
  filter_upwards [(localSlope_toReal_memLp μ hg he).coeFn_toLp] with x hx
  rw [lipschitzSlopeLp, hx]
  exact ENNReal.toReal_nonneg

theorem lipschitzSlopeLp_enorm {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (he : slopeEnergy μ g ≠ ∞) :
    ∀ᵐ x ∂μ, ‖lipschitzSlopeLp μ hg he x‖ₑ = localSlope g x := by
  filter_upwards [(localSlope_toReal_memLp μ hg he).coeFn_toLp] with x hx
  simp only [lipschitzSlopeLp, hx, Real.enorm_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal
    (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hg x))

theorem lipschitzSlopeLp_energy {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (he : slopeEnergy μ g ≠ ∞) :
    slopeEnergy μ g = ENNReal.ofReal (‖lipschitzSlopeLp μ hg he‖ ^ 2 / 2) := by
  unfold slopeEnergy
  rw [lintegral_congr_ae ((lipschitzSlopeLp_enorm μ hg he).mono
    fun x hx => congrArg (fun z : ℝ≥0∞ => z ^ 2) hx.symm), lintegral_enorm_sq_Lp]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num [div_eq_mul_inv, mul_comm]

omit [BorelSpace X] in
 
theorem cheegerEnergy_le_of_slope_majorant {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (hm : MemLp g 2 μ) (G : Lp ℝ 2 μ)
    (hG : ∀ᵐ x ∂μ, localSlope g x ≤ ‖G x‖ₑ) :
    cheegerEnergy μ g ≤ ENNReal.ofReal (‖G‖ ^ 2 / 2) := by
  apply (cheegerEnergy_le_slopeEnergy μ hm hg).trans
  unfold slopeEnergy
  calc
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ∫⁻ x, ‖G x‖ₑ ^ 2 ∂μ :=
      mul_le_mul' le_rfl (lintegral_mono_ae (hG.mono fun x hx => pow_le_pow_left' hx 2))
    _ = _ := by
      rw [lintegral_enorm_sq_Lp, ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num [div_eq_mul_inv, mul_comm]

end MinimalRelaxedSlope

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)

omit μ [MeasurableSpace X] in
theorem lipschitzWith_const_mul_real {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (c : ℝ) :
    LipschitzWith (‖c‖₊ * C) (fun x => c * g x) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [Real.dist_eq, ← mul_sub, abs_mul, NNReal.coe_mul, coe_nnnorm,
    Real.norm_eq_abs]
  calc
    _ ≤ |c| * ((C : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (by simpa only [Real.dist_eq] using hg.dist_le_mul x y)
        (abs_nonneg c)
    _ = _ := (mul_assoc _ _ _).symm

 
def IsSlopeMajorant (g : X → ℝ) (G : Lp ℝ 2 μ) : Prop :=
  ∀ᵐ x ∂μ, 0 ≤ G x ∧ localSlope g x ≤ ENNReal.ofReal (G x)

 theorem IsSlopeMajorant.add {g h : X → ℝ} {G H : Lp ℝ 2 μ}
    (hG : IsSlopeMajorant μ g G) (hH : IsSlopeMajorant μ h H) :
    IsSlopeMajorant μ (fun x => g x + h x) (G + H) := by
  filter_upwards [hG, hH, Lp.coeFn_add G H] with x hx hy hxy
  simp only [Pi.add_apply] at hxy
  rw [hxy]
  refine ⟨add_nonneg hx.1 hy.1, ?_⟩
  exact (localSlope_add_le g h x).trans
    ((add_le_add hx.2 hy.2).trans_eq (ENNReal.ofReal_add hx.1 hy.1).symm)

 theorem IsSlopeMajorant.const_mul {g : X → ℝ} {G : Lp ℝ 2 μ}
    (hG : IsSlopeMajorant μ g G) {c : ℝ} (hc : 0 ≤ c) :
    IsSlopeMajorant μ (fun x => c * g x) (c • G) := by
  filter_upwards [hG, Lp.coeFn_smul c G] with x hx hcx
  simp only [Pi.smul_apply, smul_eq_mul] at hcx
  rw [hcx]
  refine ⟨mul_nonneg hc hx.1, ?_⟩
  rw [localSlope_const_mul, abs_of_nonneg hc, ENNReal.ofReal_mul hc]
  exact mul_le_mul' le_rfl hx.2

 theorem energyLp_le_of_lipschitz_majorant {u : Lp ℝ 2 μ}
    {g : X → ℝ} {C : ℝ≥0} (hg : LipschitzWith C g)
    (hu : ⇑u =ᵐ[μ] g) {G : Lp ℝ 2 μ} (hG : IsSlopeMajorant μ g G) :
    energyLp μ u ≤ ENNReal.ofReal (‖G‖ ^ 2 / 2) := by
  change cheegerEnergy μ u ≤ _
  rw [cheegerEnergy_congr_ae μ hu]
  apply cheegerEnergy_le_of_slope_majorant μ hg ((memLp_congr_ae hu).mp (Lp.memLp u))
  exact hG.mono fun x hx => by simpa only [Real.enorm_of_nonneg hx.1] using hx.2

 

theorem energyLp_local_lower_bound (f : Lp ℝ 2 μ) (hf : energyLp μ f ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : Lp ℝ 2 μ, dist g f < δ →
      ENNReal.ofReal ((energyLp μ f).toReal - ε) ≤ energyLp μ g := by
  by_cases h : (energyLp μ f).toReal - ε ≤ 0
  · exact ⟨1, zero_lt_one, fun g _ => by rw [ENNReal.ofReal_of_nonpos h]; exact bot_le⟩
  · have hh : ENNReal.ofReal ((energyLp μ f).toReal - ε) < energyLp μ f := by
      rw [ENNReal.ofReal_lt_iff_lt_toReal (le_of_not_ge h) hf]
      linarith
    have hev := energyLp_lowerSemicontinuous μ f _ hh
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp hev
    exact ⟨δ, hδ, fun g hg => (hd hg).le⟩

 

theorem slopeMajorants_cauchy_of_recovery (f : Lp ℝ 2 μ) (hf : energyLp μ f ≠ ∞)
    (us : ℕ → Lp ℝ 2 μ) (gs : ℕ → X → ℝ) (Gs : ℕ → Lp ℝ 2 μ)
    (hlip : ∀ i, ∃ C : ℝ≥0, LipschitzWith C (gs i))
    (hae : ∀ i, ⇑(us i) =ᵐ[μ] gs i)
    (hmaj : ∀ i, IsSlopeMajorant μ (gs i) (Gs i))
    (hu : Tendsto us atTop (𝓝 f))
    (hE : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      ‖Gs i‖ ^ 2 ≤ 2 * ((energyLp μ f).toReal + ε)) :
    CauchySeq Gs := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let η : ℝ := ε ^ 2 / 32
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hδE⟩ := energyLp_local_lower_bound μ f hf hη
  have huδ := (Metric.tendsto_nhds.mp hu) δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp (huδ.and (hE η hη))
  refine ⟨N, fun i hi j hj => ?_⟩
  have hui := (hN i hi).1
  have huj := (hN j hj).1
  let v : Lp ℝ 2 μ := (1 / 2 : ℝ) • (us i + us j)
  let H : Lp ℝ 2 μ := (1 / 2 : ℝ) • (Gs i + Gs j)
  have hv : dist v f < δ := by
    have heq : v - f = (1 / 2 : ℝ) • ((us i - f) + (us j - f)) := by
      dsimp [v]
      module
    rw [dist_eq_norm, heq, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [dist_eq_norm] at hui huj
    have hnorm := norm_add_le (us i - f) (us j - f)
    linarith
  have hH : IsSlopeMajorant μ (fun x => (1 / 2 : ℝ) * (gs i x + gs j x)) H :=
    (IsSlopeMajorant.add μ (hmaj i) (hmaj j)).const_mul μ (by norm_num)
  have hvae : ⇑v =ᵐ[μ] (fun x => (1 / 2 : ℝ) * (gs i x + gs j x)) := by
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (us i + us j),
      Lp.coeFn_add (us i) (us j), hae i, hae j] with x hc ha hi' hj'
    simpa only [v, Pi.smul_apply, smul_eq_mul, Pi.add_apply, ha, hi', hj'] using hc
  obtain ⟨Ci, hCi⟩ := hlip i
  obtain ⟨Cj, hCj⟩ := hlip j
  have hbound := energyLp_le_of_lipschitz_majorant μ
    (lipschitzWith_const_mul_real (hCi.add hCj) (1 / 2 : ℝ)) hvae hH
  have hlow : (energyLp μ f).toReal - η ≤ ‖H‖ ^ 2 / 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp ((hδE v hv).trans hbound)
  have hHnorm : ‖H‖ ^ 2 = (1 / 4 : ℝ) * ‖Gs i + Gs j‖ ^ 2 := by
    dsimp [H]
    rw [norm_smul]
    norm_num [mul_pow]
  have hpar := parallelogram_law_with_norm ℝ (Gs i) (Gs j)
  have hiE := (hN i hi).2
  have hjE := (hN j hj).2
  rw [dist_eq_norm]
  dsimp [η] at hlow hiE hjE
  nlinarith [norm_nonneg (Gs i - Gs j)]

end RegularPointCoordinates

end OAI

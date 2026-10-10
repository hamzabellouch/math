import Mathlib
import OAI.Analysis.RCDHeat.VariableHeatODE

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: VariableHeatQuadratic, GeometricAELimit, HeatTwoSidedRemainder, HeatGeometricTime, HeatTimeCurve, VariableGeometricIncrement. -/



namespace RegularPointCoordinates

section

 
open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.variable_heat_slope_quadratic_bound
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {r s : ℝ} (hs : 0 < s) (hr : 2*s*(L:ℝ) < r)
    (hH : (fun x => (slopeAtScale φ r x).toReal^2) =ᵐ[hausdorff n X] H)
    :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (N : ℝ), (n:ℝ) ≤ N → ∀ (u : ℝ), 0 < u →
    ∀ {t : ℝ}, 0 ≤ t → ∀ V W : X → ℝ, Continuous V → Continuous W →
    (heatAt (hausdorff n X) hX.quadratic (u^2*t) f : X → ℝ) =ᵐ[hausdorff n X] V →
    (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] W →
    ∀ᵐ x ∂hausdorff n X, ∀ y,
      V x-W y ≤ s/2*heatAt (hausdorff n X) hX.quadratic (u^2*t) H x+
        heatSpaceFactor K u 1 t*dist x y^2/(2*s)+heatTimePenalty K N u 1 t/(2*s) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro N hNdim u hu t ht V W hV hW heV heW
  have hψ := hopfLax_lipschitz hφ hX.geodesic hs
  have hm := hopfLax_compact_memLp μ hX.geodesic hφ p R hsupp hs
  let g : Lp ℝ 2 μ := hm.toLp (hopfLax φ s)
  have hg : hopfLax φ s =ᵐ[μ] g := hm.coeFn_toLp.symm
  let M := |φ p|+(L:ℝ)*max R 0
  have hM : ∀ x, |φ x| ≤ M := compact_lipschitz_abs_bound hφ p R hsupp
  have hN : ∀ x, |hopfLax φ s x| ≤ M+s*(L:ℝ)^2/2 := by
    intro x
    have hh := hopfLax_bounds hφ hs x
    have hhM := abs_le.mp (hM x)
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (L:ℝ)]
  obtain ⟨U,hU,heU⟩ := hX.heat_lipschitz K n hn g hψ hg _ hN (show 0 ≤ u^2*t by positivity)
  have hdual := hX.variable_heat_pointwise_quadratic_dual K n hn f g hφ.continuous.measurable
    hψ.continuous.measurable hf hg M _ hM hN (by positivity : 0 ≤ 1/(2*s))
      (fun x y => by
        have h := hopfLax_le_cost hφ hs x y
        simp only [div_eq_mul_inv,one_mul] at h ⊢
        nlinarith [h]) N hNdim u 1 hu zero_lt_one ht U W hU.continuous hW heU (by simpa only [one_pow,one_mul] using heW)
  have hle : f-g ≤ (s/2) • H := by
    apply (Lp.coeFn_le _ _).mp
    filter_upwards [hf,hg,hH,Lp.coeFn_sub f g,Lp.coeFn_smul (s/2) H] with x hf hg hH hfg hsH
    rw [hfg,hsH]
    change f x-g x ≤ s/2*H x
    rw [← hf,← hg,← hH]
    have h := hopfLax_gap_le_scale hφ hs hr x
    nlinarith [h]
  have hheat := heatAt_mono μ hX.quadratic (u^2*t) hle
  rw [map_sub,map_smul] at hheat
  filter_upwards [(Lp.coeFn_le _ _).mpr hheat,
    Lp.coeFn_sub (heatAt μ hX.quadratic (u^2*t) f) (heatAt μ hX.quadratic (u^2*t) g),
    Lp.coeFn_smul (s/2) (heatAt μ hX.quadratic (u^2*t) H),heU,heV] with x hh hfg hsH heU heV
  rw [hfg,hsH] at hh
  change heatAt μ hX.quadratic (u^2*t) f x-heatAt μ hX.quadratic (u^2*t) g x ≤
    s/2*heatAt μ hX.quadratic (u^2*t) H x at hh
  rw [heU,heV] at hh
  intro y
  have hd := hdual x y
  simp only [div_eq_mul_inv,one_mul] at hd ⊢
  nlinarith [hd]

end

 
section

 
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem ae_tendsto_of_summable_L2_norm (F : ℕ → Lp ℝ 2 μ)
    (hF : Summable (fun j => ‖F j‖)) :
    ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 0) := by
  have hh : ∀ᵐ x ∂μ, Summable (fun j => ‖F j x‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞) ≤ 2)
    simpa only [← Lp.enorm_def] using (tsum_enorm_ne_top_iff_summable_norm.mpr hF)
  filter_upwards [hh] with x hx
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hx.tendsto_atTop_zero

theorem ae_tendsto_of_geometric_L2_norm (F : ℕ → Lp ℝ 2 μ)
    {r C : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hF : ∀ j, ‖F j‖ ≤ C*r^j) :
    ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 0) := by
  apply ae_tendsto_of_summable_L2_norm F
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _) hF
    ((summable_geometric_of_lt_one hr0 hr).mul_left C)

theorem ae_tendsto_of_eventually_geometric_L2_norm (F : ℕ → Lp ℝ 2 μ)
    {r C : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hF : ∀ᶠ j in atTop, ‖F j‖ ≤ C*r^j) :
    ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 0) := by
  apply ae_tendsto_of_summable_L2_norm F
  exact Summable.of_norm_bounded_eventually
    ((summable_geometric_of_lt_one hr0 hr).mul_left C)
    (by simpa only [norm_norm,Nat.cofinite_eq_atTop] using hF)

end

 
section

 

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heatAt_twoSided_remainder (f : Lp ℝ 2 μ) {a t z : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (haz : a ≤ z) :
    ‖heatAt μ hQ z f-heatAt μ hQ t f+(z-t) • heatGeneratorAt μ hQ t f‖ ≤
      (2*(1+1/(a/2)))^2*‖f‖*|z-t|^2 := by
  let A := (2*(1+1/(a/2)))^2*‖f‖
  let G := heatGeneratorAt μ hQ t f
  let F : ℝ → Lp ℝ 2 μ := fun s => heatAt μ hQ s f+s • G
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have has (s : ℝ) (hs : s ∈ uIcc t z) : a ≤ s :=
    (le_min hat haz).trans hs.1
  have hdist (s : ℝ) (hs : s ∈ uIcc t z) : |s-t| ≤ |z-t| := by
    rcases le_total t z with htz|hzt
    · rw [uIcc_of_le htz] at hs
      rw [abs_of_nonneg (sub_nonneg.mpr hs.1),abs_of_nonneg (sub_nonneg.mpr htz)]
      linarith [hs.2]
    · rw [uIcc_of_ge hzt] at hs
      rw [abs_of_nonpos (sub_nonpos.mpr hs.2),abs_of_nonpos (sub_nonpos.mpr hzt)]
      linarith [hs.1]
  have hd (s : ℝ) (hs : s ∈ uIcc t z) : HasDerivAt F (-heatGeneratorAt μ hQ s f+G) s := by
    convert! (heatAt_hasDerivAt μ hQ s (ha.trans_le (has s hs)) f).add
      ((hasDerivAt_id s).smul_const G) using 1; simp
  have hb (s : ℝ) (hs : s ∈ uIcc t z) : ‖-heatGeneratorAt μ hQ s f+G‖ ≤ A*|z-t| := by
    rw [neg_add_eq_sub,norm_sub_rev]
    exact (heatGeneratorAt_norm_sub_le μ hQ f ha (has s hs) hat).trans
      (mul_le_mul_of_nonneg_left (hdist s hs) hA)
  have hh := (convex_uIcc t z).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt) hb (left_mem_uIcc) (right_mem_uIcc)
  have he : F z-F t = heatAt μ hQ z f-heatAt μ hQ t f+(z-t) • G := by
    dsimp [F]; module
  rw [he,Real.norm_eq_abs] at hh
  convert hh using 1; ring

theorem heatAt_time_norm_sub_le (f : Lp ℝ 2 μ) {a t z : ℝ}
    (ha : 0 < a) (hat : a ≤ t) (haz : a ≤ z) :
    ‖heatAt μ hQ z f-heatAt μ hQ t f‖ ≤ 2*(1+1/a)*‖f‖*|z-t| := by
  have hd (s : ℝ) (hs : s ∈ Ici a) := heatAt_hasDerivAt μ hQ s (ha.trans_le hs) f
  have hb (s : ℝ) (hs : s ∈ Ici a) : ‖-heatGeneratorAt μ hQ s f‖ ≤ 2*(1+1/a)*‖f‖ := by
    rw [norm_neg]
    exact (heatGeneratorAt μ hQ s).le_of_opNorm_le (heatGeneratorAt_norm_le_of_ge μ hQ a ha s hs) f
  have hh := (convex_Ici a).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt) hb hat haz
  simpa only [Real.norm_eq_abs] using hh


 
theorem heatAt_geometric_time_tendsto_ae (f : Lp ℝ 2 μ) {t r C D : ℝ}
    (ht : 0 < t) (hr0 : 0 < r) (hr1 : r < 1) (hC : 0 < C)
    (z : ℕ → ℝ) (hz : ∀ᶠ j in atTop, t/2 ≤ z j ∧ |z j-t| ≤ D*(C*r^j)) :
    ∀ᵐ x ∂μ, Tendsto (fun j => heatAt μ hQ (z j) f x) atTop (𝓝 (heatAt μ hQ t f x)) := by
  let E : ℕ → Lp ℝ 2 μ := fun j => heatAt μ hQ (z j) f-heatAt μ hQ t f
  have hb : ∀ᶠ j in atTop, ‖E j‖ ≤ (2*(1+1/(t/2))*‖f‖*D*C)*r^j := by
    filter_upwards [hz] with j hj
    have hh := heatAt_time_norm_sub_le μ hQ f (half_pos ht) (by linarith : t/2 ≤ t) hj.1
    have hscaled : |z j-t|/C ≤ D*r^j :=
      (div_le_iff₀ hC).mpr (by nlinarith [hj.2])
    calc
      _ ≤ 2*(1+1/(t/2))*‖f‖*|z j-t| := hh
      _ = (2*(1+1/(t/2))*‖f‖*C)*(|z j-t|/C) := by field_simp
      _ ≤ (2*(1+1/(t/2))*‖f‖*C)*(D*r^j) := mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ = _ := by ring
  have ha := ae_tendsto_of_eventually_geometric_L2_norm E hr0.le hr1 hb
  have he : ∀ᵐ x ∂μ, ∀ j, E j x = heatAt μ hQ (z j) f x-heatAt μ hQ t f x :=
    ae_all_iff.mpr (fun j => Lp.coeFn_sub _ _)
  filter_upwards [ha,he] with x hx hex
  have hh := hx.add_const (heatAt μ hQ t f x)
  simpa only [hex,sub_add_cancel,zero_add] using hh

theorem heatAt_geometric_secant_tendsto_ae (f : Lp ℝ 2 μ) {t r C D q : ℝ}
    (ht : 0 < t) (hr0 : 0 < r) (hr1 : r < 1) (hC : 0 < C)
    (hD : 0 ≤ D) (z : ℕ → ℝ)
    (hz : ∀ᶠ j in atTop, t/2 ≤ z j ∧ |z j-t| ≤ D*(C*r^j))
    (hq : Tendsto (fun j => (z j-t)/(C*r^j)) atTop (𝓝 q)) :
    ∀ᵐ x ∂μ, Tendsto (fun j => (heatAt μ hQ (z j) f x-heatAt μ hQ t f x)/(C*r^j))
      atTop (𝓝 (-q*heatGeneratorAt μ hQ t f x)) := by
  let s : ℕ → ℝ := fun j => C*r^j
  have hs (j) : 0 < s j := mul_pos hC (pow_pos hr0 j)
  let G := heatGeneratorAt μ hQ t f
  let E : ℕ → Lp ℝ 2 μ := fun j => (s j)⁻¹ •
    (heatAt μ hQ (z j) f-heatAt μ hQ t f+(z j-t) • G)
  let A := (2*(1+1/((t/2)/2)))^2*‖f‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb : ∀ᶠ j in atTop, ‖E j‖ ≤ (A*D^2*C)*r^j := by
    filter_upwards [hz] with j hj
    have hh := heatAt_twoSided_remainder μ hQ f (half_pos ht) (by linarith : t/2 ≤ t) hj.1
    have hpow := (sq_le_sq₀ (abs_nonneg (z j-t)) (mul_nonneg hD (hs j).le)).mpr hj.2
    rw [show ‖E j‖ = (s j)⁻¹*‖heatAt μ hQ (z j) f-heatAt μ hQ t f+(z j-t) • G‖ by
      dsimp only [E]; rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hs j))]]
    calc
      _ ≤ (s j)⁻¹*(A*|z j-t|^2) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (hs j).le)
      _ ≤ (s j)⁻¹*(A*(D*s j)^2) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hA) (inv_nonneg.mpr (hs j).le)
      _ = (A*D^2*C)*r^j := by dsimp [s]; field_simp
  have ha := ae_tendsto_of_eventually_geometric_L2_norm E hr0.le hr1 hb
  have he : ∀ᵐ x ∂μ, ∀ j, E j x =
      (heatAt μ hQ (z j) f x-heatAt μ hQ t f x)/(s j)+(z j-t)/(s j)*G x := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [Lp.coeFn_smul ((s j)⁻¹) (heatAt μ hQ (z j) f-heatAt μ hQ t f+(z j-t) • G),
      Lp.coeFn_add (heatAt μ hQ (z j) f-heatAt μ hQ t f) ((z j-t) • G),
      Lp.coeFn_sub (heatAt μ hQ (z j) f) (heatAt μ hQ t f),Lp.coeFn_smul (z j-t) G] with x h1 h2 h3 h4
    dsimp only [Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul] at h1 h2 h3 h4
    dsimp only [E]
    rw [h1,h2,h3,h4]
    change (s j)⁻¹*(heatAt μ hQ (z j) f x-heatAt μ hQ t f x+(z j-t)*G x) = _
    ring
  filter_upwards [ha,he] with x hx hex
  have hh := hx.sub (hq.mul_const (G x))
  simpa only [hex,s,G,add_sub_cancel_right,zero_sub,neg_mul] using hh

end

 
section

 
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

noncomputable def heatKernelIntegral (K u v t : ℝ) : ℝ :=
  ∫s in (0:ℝ)..t, Real.exp (-2*K*(u^2+u*v+v^2)/3*s)

theorem heatKernelIntegral_continuous (K v t : ℝ) :
    Continuous (fun u => heatKernelIntegral K u v t) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

theorem heatKernelIntegral_one (K t : ℝ) :
    heatKernelIntegral K 1 1 t = ∫s in (0:ℝ)..t, Real.exp (-2*K*s) := by
  unfold heatKernelIntegral
  congr 1; funext s; congr 1; ring

theorem geometric_square_time_limits (t q r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun j : ℕ => (1+q*r^j)^2*t) atTop (𝓝 t) ∧
    Tendsto (fun j : ℕ => ((1+q*r^j)^2*t-t)/r^j) atTop (𝓝 (2*q*t)) := by
  have hs := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  constructor
  · simpa using (((hs.const_mul q).const_add 1).pow 2).mul_const t
  · have hh : (fun j : ℕ => ((1+q*r^j)^2*t-t)/r^j) =
        (fun j : ℕ => (2*q+q^2*r^j)*t) := by
      funext j
      field_simp [(pow_pos hr0 j).ne']
      ring
    rw [hh]
    simpa using (((hs.const_mul (q^2)).const_add (2*q)).mul_const t)

theorem geometric_square_time_bound {t : ℝ} (ht : 0 < t) (q r : ℝ)
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∀ᶠ j : ℕ in atTop, t/2 ≤ (1+q*r^j)^2*t ∧
      |(1+q*r^j)^2*t-t| ≤ (|2*q*t|+1)*(1*r^j) := by
  obtain ⟨hz,hq⟩ := geometric_square_time_limits t q r hr0 hr1
  have hh := (hq.abs).eventually (Iio_mem_nhds (lt_add_one |2*q*t|))
  filter_upwards [hz.eventually (Ioi_mem_nhds (by linarith : t/2 < t)),hh] with j hj hk
  refine ⟨hj.le,?_⟩
  rw [abs_div,abs_of_pos (pow_pos hr0 j)] at hk
  have hk' := (div_lt_iff₀ (pow_pos hr0 j)).mp hk
  simpa only [one_mul] using hk'.le

theorem geometric_heat_factors_tendsto (K N t q r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun j : ℕ => heatSpaceFactor K (1+q*r^j) 1 t) atTop (𝓝 (Real.exp (-2*K*t))) ∧
    Tendsto (fun j : ℕ => heatTimePenalty K N (1+q*r^j) 1 t/(r^j)^2)
      atTop (𝓝 (2*N*q^2*heatKernelIntegral K 1 1 t)) := by
  have hs := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hu : Tendsto (fun j : ℕ => 1+q*r^j) atTop (𝓝 1) := by
    simpa using (hs.const_mul q).const_add 1
  constructor
  · have hc : Continuous (fun u => heatSpaceFactor K u 1 t) := by unfold heatSpaceFactor; fun_prop
    have hh := (hc.continuousAt (x := 1)).tendsto.comp hu
    convert hh using 1
    congr 2
    unfold heatSpaceFactor
    congr 1; ring_nf
  · have he (j : ℕ) : heatTimePenalty K N (1+q*r^j) 1 t/(r^j)^2 =
        2*N*q^2*heatKernelIntegral K (1+q*r^j) 1 t := by
      unfold heatTimePenalty heatKernelIntegral
      field_simp [(pow_pos hr0 j).ne']
      ring
    simp_rw [he]
    exact (((heatKernelIntegral_continuous K 1 t).continuousAt (x := 1)).tendsto.comp hu).const_mul (2*N*q^2)

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

private theorem geometric_increment_algebra (v w z A B P d s : ℝ) (hs : s ≠ 0)
    (h : z-w ≤ s/2*A+B*d^2/(2*s)+P/(2*s)) :
    v-w ≤ s*(A-2*(z-v)/s+P/s^2)/2+B*d^2/(2*s) := by
  have he : s*(A-2*(z-v)/s+P/s^2)/2 = s/2*A-(z-v)+P/(2*s) := by field_simp
  rw [he]; linarith

theorem NoncollapsedRCD.variable_geometric_increment
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ)
    (p : X) (R : ℝ) (hsupp : ∀ x, R < dist p x → φ x = 0)
    (f H : Lp ℝ 2 (hausdorff n X)) (hf : φ =ᵐ[hausdorff n X] f)
    {l : ℝ} (hl : 0 < l)
    (hH : (fun x => (slopeAtScale φ l x).toReal^2) =ᵐ[hausdorff n X] H)
    (N : ℝ) (hN : (n:ℝ) ≤ N) {t : ℝ} (ht : 0 < t)
    (q r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ V : X → ℝ, Continuous V →
      (heatAt (hausdorff n X) hX.quadratic t f : X → ℝ) =ᵐ[hausdorff n X] V →
      ∀ᵐ x ∂hausdorff n X, ∃ a b : ℕ → ℝ,
        Tendsto a atTop (𝓝 (heatAt (hausdorff n X) hX.quadratic t H x+
          4*t*q*heatGeneratorAt (hausdorff n X) hX.quadratic t f x+2*N*q^2*heatKernelIntegral K 1 1 t)) ∧
        Tendsto b atTop (𝓝 (Real.exp (-2*K*t))) ∧
        ∀ᶠ j in atTop, ∀ y, V x-V y ≤ r^j*a j/2+b j*dist x y^2/(2*r^j) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro V hV heV
  let z : ℕ → ℝ := fun j => (1+q*r^j)^2*t
  let M := |φ p|+(L:ℝ)*max R 0
  have hM : ∀ x, |φ x| ≤ M := compact_lipschitz_abs_bound hφ p R hsupp
  have hrep (j : ℕ) := hX.heat_lipschitz K n hn f hφ hf M hM (show 0 ≤ z j by dsimp [z]; positivity)
  choose Vj hVj heVj using hrep
  have hh (j : ℕ) : ∀ᵐ x ∂μ, (0 < 1+q*r^j ∧ 2*r^j*(L:ℝ) < l) →
      ∀ y, Vj j x-V y ≤ r^j/2*heatAt μ hX.quadratic (z j) H x+
        heatSpaceFactor K (1+q*r^j) 1 t*dist x y^2/(2*r^j)+
        heatTimePenalty K N (1+q*r^j) 1 t/(2*r^j) := by
    by_cases hj : 0 < 1+q*r^j ∧ 2*r^j*(L:ℝ) < l
    · have hh := hX.variable_heat_slope_quadratic_bound K n hn hφ p R hsupp f H hf
        (pow_pos hr0 j) hj.2 hH N hN (1+q*r^j) hj.1 ht.le (Vj j) V
        (hVj j).continuous hV (heVj j) heV
      exact hh.mono (fun x hx _ => hx)
    · exact Eventually.of_forall (fun _ hx => False.elim (hj hx))
  have hs := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  have hu : Tendsto (fun j : ℕ => 1+q*r^j) atTop (𝓝 1) := by simpa using (hs.const_mul q).const_add 1
  have hl' : Tendsto (fun j : ℕ => 2*r^j*(L:ℝ)) atTop (𝓝 0) := by simpa using (hs.const_mul 2).mul_const (L:ℝ)
  have hgood : ∀ᶠ j : ℕ in atTop, 0 < 1+q*r^j ∧ 2*r^j*(L:ℝ) < l :=
    (hu.eventually (Ioi_mem_nhds zero_lt_one)).and (hl'.eventually (Iio_mem_nhds hl))
  have hz := geometric_square_time_bound ht q r hr0 hr1
  have hHt := heatAt_geometric_time_tendsto_ae μ hX.quadratic H ht hr0 hr1 zero_lt_one z hz
  have hft := heatAt_geometric_secant_tendsto_ae μ hX.quadratic f ht hr0 hr1 zero_lt_one
    (by positivity : 0 ≤ |2*q*t|+1) z hz (by simpa only [one_mul] using (geometric_square_time_limits t q r hr0 hr1).2)
  obtain ⟨hBt,hPt⟩ := geometric_heat_factors_tendsto K N t q r hr0 hr1
  filter_upwards [hHt,hft,ae_all_iff.mpr hh,ae_all_iff.mpr heVj,heV] with x hHt hft hxb hrepj hxV
  let a : ℕ → ℝ := fun j => heatAt μ hX.quadratic (z j) H x-
    2*(heatAt μ hX.quadratic (z j) f x-heatAt μ hX.quadratic t f x)/r^j+
    heatTimePenalty K N (1+q*r^j) 1 t/(r^j)^2
  refine ⟨a,(fun j => heatSpaceFactor K (1+q*r^j) 1 t),?_,hBt,?_⟩
  · have hh := (hHt.sub (hft.const_mul 2)).add hPt
    convert hh using 1
    · funext j; dsimp [a]; simp only [one_mul]; ring
    · congr 1; ring
  · filter_upwards [hgood] with j hj y
    have hb := hxb j hj y
    rw [←hrepj j] at hb
    dsimp only [a]
    rw [hxV]
    exact geometric_increment_algebra (V x) (V y) (heatAt μ hX.quadratic (z j) f x)
      (heatAt μ hX.quadratic (z j) H x) (heatSpaceFactor K (1+q*r^j) 1 t)
      (heatTimePenalty K N (1+q*r^j) 1 t) (dist x y) (r^j) (pow_pos hr0 j).ne' hb


end RegularPointCoordinates

end OAI

import Mathlib
import OAI.Analysis.RCDHeat.VolumeComparison2

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: WeightedHilbert, DaviesLower, ScalarGronwall, DaviesHeat, RadialWeight, WeightedIntegral, HeatExponential, VolumeExponential. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
section WeightedHilbert
omit [MeasurableSpace X] [BorelSpace X] [MetricSpace X]
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

 theorem lpMultiplier_inner_symm (V : Lp ℝ ∞ μ) (f g : Lp ℝ 2 μ) :
    inner ℝ f (lpMultiplier μ V g) = inner ℝ (lpMultiplier μ V f) g := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpMultiplier_coe μ V g, lpMultiplier_coe μ V f] with x hg hf
  simp only [Real.inner_apply, hg, hf]
  ring

 theorem lpMultiplier_inner_nonneg (V : Lp ℝ ∞ μ) (hV : ∀ᵐ x ∂μ, 0 ≤ V x)
    (f : Lp ℝ 2 μ) : 0 ≤ inner ℝ f (lpMultiplier μ V f) := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [lpMultiplier_coe μ V f, hV] with x he hn
  rw [Real.inner_apply, he]
  change 0 ≤ f x * (V x * f x)
  calc
    0 ≤ V x * (f x)^2 := mul_nonneg hn (sq_nonneg (f x))
    _ = f x * (V x*f x) := by ring

 theorem lpMultiplier_abs_inner (V : Lp ℝ ∞ μ) (f : Lp ℝ 2 μ) :
    inner ℝ (lpAbs μ f) (lpMultiplier μ V (lpAbs μ f)) = inner ℝ f (lpMultiplier μ V f) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpMultiplier_coe μ V (lpAbs μ f), lpMultiplier_coe μ V f,
    lpAbs_coe μ f] with x he he' ha
  simp only [Real.inner_apply, he, he', ha]
  calc
    _ = V x * |f x|^2 := by ring
    _ = V x * (f x)^2 := by rw [sq_abs]
    _ = _ := by ring

 theorem weighted_square_lower (V : Lp ℝ ∞ μ) (hV : ∀ᵐ x ∂μ, 0 ≤ V x)
    (f G : Lp ℝ 2 μ) (L : ℝ) :
    -(L^2/4) * inner ℝ f (lpMultiplier μ V f) ≤
      inner ℝ G (lpMultiplier μ V G-L • lpMultiplier μ V (lpAbs μ f)) := by
  have h := lpMultiplier_inner_nonneg μ V hV (G-(L/2) • lpAbs μ f)
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right] at h ⊢
  have hs : inner ℝ G (lpMultiplier μ V (lpAbs μ f)) =
      inner ℝ (lpAbs μ f) (lpMultiplier μ V G) := by
    rw [lpMultiplier_inner_symm μ V G (lpAbs μ f)]
    exact real_inner_comm _ _
  rw [hs] at h ⊢
  rw [lpMultiplier_abs_inner] at h
  nlinarith

end WeightedHilbert
section DaviesLower
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem energyForm_weight_lower (f g : SobolevSpace μ hQ)
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v)
    (hfg : SobolevSpace.toLp μ hQ g = lpMultiplier μ V (SobolevSpace.toLp μ hQ f))
    {L : ℝ} (hL : 0 ≤ L) (hvs : ∀ x, localSlope v x ≤ ENNReal.ofReal (L*v x)) :
    -(L^2/4) * inner ℝ (SobolevSpace.toLp μ hQ f)
      (lpMultiplier μ V (SobolevSpace.toLp μ hQ f)) ≤ energyForm μ hQ f g := by
  exact (weighted_square_lower μ V (hV.mono fun x hx => hx.symm ▸ hn x)
    (SobolevSpace.toLp μ hQ f) (SobolevSpace.minimalSlope μ hQ f) L).trans
    (energyForm_weight_lower_inner μ hQ f g hv c hs hb hn V hV hfg hL hvs)

end DaviesLower

section ScalarGronwall
 theorem growth_le_exp {A : ℝ → ℝ} {c : ℝ}
    (hc : ContinuousOn A (Ici 0))
    (hd : ∀ t, 0 < t → ∃ D, HasDerivAt A D t ∧ D ≤ c*A t)
    {t : ℝ} (ht : 0 ≤ t) : A t ≤ Real.exp (c*t)*A 0 := by
  have hAD (s : ℝ) (hs : 0 < s) : HasDerivAt A (deriv A s) s := by
    obtain ⟨D,hD,_⟩ := hd s hs
    rwa [hD.deriv]
  have hB (s : ℝ) (hs : 0 < s) : deriv A s ≤ c*A s := by
    obtain ⟨D,hD,hb⟩ := hd s hs
    rwa [hD.deriv]
  have ha : AntitoneOn (fun s => Real.exp (-c*s)*A s) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hc)
      (fun s hs => ((((hasDerivAt_id s).const_mul (-c)).exp).mul
        (hAD s (by simpa only [interior_Ici, mem_Ioi] using hs))).hasDerivWithinAt)
    intro s hs
    have hsp : 0 < s := by simpa only [interior_Ici, mem_Ioi] using hs
    have hb := mul_le_mul_of_nonneg_left (hB s hsp) (Real.exp_pos (-c*s)).le
    simp only [id_eq, mul_one]
    nlinarith
  have hh := ha (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
  dsimp only at hh
  simp only [mul_zero, Real.exp_zero, one_mul] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (c*t)).le
  have he : Real.exp (c*t)*Real.exp (-c*t) = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  simpa only [← mul_assoc, he, one_mul] using hm
end ScalarGronwall
section DaviesHeat
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem heatAt_weighted_hasDerivAt (f : Lp ℝ 2 μ) (V : Lp ℝ ∞ μ)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => inner ℝ (heatAt μ hQ s f) (lpMultiplier μ V (heatAt μ hQ s f)))
      (-2*inner ℝ (heatGenerator μ hQ t ht f) (lpMultiplier μ V (heatAt μ hQ t f))) t := by
  have hd := heatAt_hasDerivAt μ hQ t ht f
  have h := hd.inner ℝ ((lpMultiplier μ V).hasFDerivAt.comp_hasDerivAt t hd)
  rw [heatGeneratorAt_of_pos μ hQ t ht] at h
  simp only [map_neg, inner_neg_left, inner_neg_right] at h
  have hs : inner ℝ (heatAt μ hQ t f) (lpMultiplier μ V (heatGenerator μ hQ t ht f)) =
      inner ℝ (heatGenerator μ hQ t ht f) (lpMultiplier μ V (heatAt μ hQ t f)) := by
    rw [lpMultiplier_inner_symm]
    exact real_inner_comm _ _
  rw [hs] at h
  dsimp only [Function.comp_apply] at h
  convert! h using 1
  ring

 theorem heatAt_weighted_bound (f : Lp ℝ 2 μ)
    {v : X → ℝ} {C B : ℝ≥0} (hv : LipschitzWith C v)
    (c : ℝ) (hs : HasCompactSupport (fun x => v x-c))
    (hb : ∀ x, |v x| ≤ B) (hn : ∀ x, 0 ≤ v x)
    (V : Lp ℝ ∞ μ) (hV : ⇑V =ᵐ[μ] v)
    {L : ℝ} (hL : 0 ≤ L) (hvs : ∀ x, localSlope v x ≤ ENNReal.ofReal (L*v x))
    {t : ℝ} (ht : 0 ≤ t) :
    inner ℝ (heatAt μ hQ t f) (lpMultiplier μ V (heatAt μ hQ t f)) ≤
      Real.exp (L^2/2*t) * inner ℝ f (lpMultiplier μ V f) := by
  have hc : Continuous (fun s => inner ℝ (heatAt μ hQ s f)
      (lpMultiplier μ V (heatAt μ hQ s f))) := (heatAt_continuous μ hQ f).inner
    ((lpMultiplier μ V).continuous.comp (heatAt_continuous μ hQ f))
  have hD (s : ℝ) (hs' : 0 < s) : ∃ D, HasDerivAt
      (fun t => inner ℝ (heatAt μ hQ t f) (lpMultiplier μ V (heatAt μ hQ t f))) D s ∧
      D ≤ (L^2/2)*inner ℝ (heatAt μ hQ s f) (lpMultiplier μ V (heatAt μ hQ s f)) := by
    let u := heatSobolev μ hQ s hs' f
    let g := SobolevSpace.mulLipschitz μ hQ u hv c hs hb hn V hV
    have hgu : SobolevSpace.toLp μ hQ g = lpMultiplier μ V (SobolevSpace.toLp μ hQ u) := rfl
    have he := energyForm_weight_lower μ hQ u g hv c hs hb hn V hV hgu hL hvs
    change -(L^2/4)*inner ℝ (heatAt μ hQ s f) (lpMultiplier μ V (heatAt μ hQ s f)) ≤
      energyForm μ hQ (heatSobolev μ hQ s hs' f) g at he
    rw [heatGenerator_form, hgu, heatSobolev_toLp] at he
    refine ⟨_, heatAt_weighted_hasDerivAt μ hQ f V s hs', ?_⟩
    nlinarith
  have he := growth_le_exp hc.continuousOn hD ht
  simpa [heatAt_zero] using he

end DaviesHeat

section RadialWeight
variable {X : Type u} [MetricSpace X]
noncomputable def radialWeight (p : X) (a R : ℝ) (x : X) : ℝ :=
  Real.exp (a * min (dist p x) R)

 theorem radialWeight_nonneg (p : X) (a R : ℝ) (x : X) :
    0 ≤ radialWeight p a R x := (Real.exp_pos _).le

 theorem radialWeight_bound (p : X) {a : ℝ} (ha : 0 ≤ a) (R : ℝ) (x : X) :
    |radialWeight p a R x| ≤ Real.exp (a*R) := by
  rw [abs_of_nonneg (radialWeight_nonneg p a R x)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (min_le_right _ _) ha)

 theorem radialWeight_lipschitz (p : X) {a : ℝ} (ha : 0 ≤ a) (R : ℝ) :
    LipschitzWith ⟨a*Real.exp (a*R), mul_nonneg ha (Real.exp_pos _).le⟩ (radialWeight p a R) := by
  have hmin := (LipschitzWith.dist_right p).min_const R
  have hl := lipschitzWith_const_mul_real hmin a
  have hex : LipschitzOnWith ⟨Real.exp (a*R), (Real.exp_pos _).le⟩ Real.exp (Iic (a*R)) := by
    apply (convex_Iic (a*R)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    intro x hx
    change |Real.exp x| ≤ Real.exp (a*R)
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hx
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := hex.dist_le_mul (a*min (dist p x) R) (mul_le_mul_of_nonneg_left (min_le_right (dist p x) R) ha)
    (a*min (dist p y) R) (mul_le_mul_of_nonneg_left (min_le_right (dist p y) R) ha)
  have hv := mul_le_mul_of_nonneg_left (hl.dist_le_mul x y) (Real.exp_pos (a*R)).le
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg ha, mul_one] at hv
  exact h.trans (by change Real.exp (a*R)*dist (a*min (dist p x) R) (a*min (dist p y) R) ≤ a*Real.exp (a*R)*dist x y; nlinarith)

 theorem radialWeight_slope (p : X) {a : ℝ} (ha : 0 ≤ a) (R : ℝ) (x : X) :
    localSlope (radialWeight p a R) x ≤ ENNReal.ofReal (a*radialWeight p a R x) := by
  let u := fun x => a*min (dist p x) R
  have hu : LipschitzWith ⟨a,ha⟩ u := by
    have h := lipschitzWith_const_mul_real ((LipschitzWith.dist_right p).min_const R) a
    have he : ‖a‖₊*1 = (⟨a,ha⟩ : ℝ≥0) := by
      ext; simp only [coe_nnnorm, Real.norm_eq_abs, mul_one, abs_of_nonneg ha]; rfl
    rwa [he] at h
  have hs := localSlope_comp_hasDerivAt (Real.hasDerivAt_exp (u x)) hu.continuous.continuousAt
    (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hu x))
  change localSlope (radialWeight p a R) x ≤ _ at hs
  rw [abs_of_pos (Real.exp_pos _)] at hs
  apply hs.trans
  calc
    ENNReal.ofReal (Real.exp (u x))*localSlope u x ≤
        ENNReal.ofReal (radialWeight p a R x)*ENNReal.ofReal a :=
      mul_le_mul' le_rfl (by
        have he := ENNReal.ofReal_eq_coe_nnreal ha
        rw [he]
        exact localSlope_le_of_lipschitz hu x)
    _ = _ := by rw [← ENNReal.ofReal_mul (radialWeight_nonneg p a R x)]; congr 1; ring

variable [ProperSpace X]
 theorem radialWeight_constant_outside (p : X) (a R : ℝ) :
    HasCompactSupport (fun x => radialWeight p a R x-Real.exp (a*R)) := by
  apply HasCompactSupport.intro (isCompact_closedBall p R)
  intro x hx
  have hd : R ≤ dist p x := (not_le.mp (by simpa only [Metric.mem_closedBall, dist_comm] using hx)).le
  simp only [radialWeight, min_eq_right hd, sub_self]
end RadialWeight

section WeightedIntegral
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

 theorem lpMultiplier_integral_sq (V : Lp ℝ ∞ μ) (f : Lp ℝ 2 μ)
    {v : X → ℝ} (hV : ⇑V =ᵐ[μ] v) :
    Integrable (fun x => v x*f x^2) μ ∧
    inner ℝ f (lpMultiplier μ V f) = ∫ x, v x*f x^2 ∂μ := by
  have he : (fun x => f x*(lpMultiplier μ V f) x) =ᵐ[μ] (fun x => v x*f x^2) := by
    filter_upwards [lpMultiplier_coe μ V f, hV] with x hm hv
    rw [hm, hv]
    ring
  refine ⟨((Lp.memLp f).integrable_mul (Lp.memLp (lpMultiplier μ V f))).congr he, ?_⟩
  rw [L2.inner_def]
  exact integral_congr_ae (by simpa only [Real.inner_apply] using he)

end WeightedIntegral
section HeatExponential
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem heatAt_radialWeight_integral (f : Lp ℝ 2 μ) (p : X)
    {a : ℝ} (ha : 0 ≤ a) (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => radialWeight p a R x * heatAt μ hQ t f x ^ 2) μ ∧
    (∫ x, radialWeight p a R x * heatAt μ hQ t f x ^ 2 ∂μ) ≤
      Real.exp (a^2/2*t) * (∫ x, radialWeight p a R x * f x ^ 2 ∂μ) := by
  let v := radialWeight p a R
  have hv := radialWeight_lipschitz p ha R
  let B : ℝ≥0 := ⟨Real.exp (a*R), (Real.exp_pos _).le⟩
  have hb (x : X) : |v x| ≤ B := radialWeight_bound p ha R x
  let V := boundedMultiplier μ v hv.continuous.measurable B hb
  have hV : ⇑V =ᵐ[μ] v := boundedMultiplier_coe μ _ _ _ _
  have h := heatAt_weighted_bound μ hQ f hv (Real.exp (a*R))
    (radialWeight_constant_outside p a R) hb (radialWeight_nonneg p a R)
    V hV ha (radialWeight_slope p ha R) ht
  have hi := lpMultiplier_integral_sq μ V (heatAt μ hQ t f) hV
  have hi0 := lpMultiplier_integral_sq μ V f hV
  rw [hi.2, hi0.2] at h
  exact ⟨hi.1, h⟩

 theorem heatAt_radialWeight_integral_le (f : Lp ℝ 2 μ) (p : X)
    {r : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a : ℝ} (ha : 0 ≤ a) (R : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, radialWeight p a R x * heatAt μ hQ t f x ^ 2 ∂μ) ≤
      Real.exp (a^2/2*t+a*r) * ‖f‖^2 := by
  have hi := heatAt_radialWeight_integral μ hQ f p ha R ht
  have hi0 := (heatAt_radialWeight_integral μ hQ f p ha R (t := 0) le_rfl).1
  simp only [heatAt_zero, one_apply_eq_self] at hi0
  have hs : Integrable (fun x => f x^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hisq : (∫ x, f x^2 ∂μ) = ‖f‖^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    funext x
    simp only [Real.inner_apply, pow_two]
  have hb : (∫ x, radialWeight p a R x*f x^2 ∂μ) ≤ Real.exp (a*r)*‖f‖^2 := by
    rw [← hisq, ← integral_const_mul]
    apply integral_mono_ae hi0 (hs.const_mul _)
    filter_upwards [hf] with x hx
    by_cases hz : f x = 0
    · simp only [hz, sq, mul_zero, le_refl]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (hx hz)) ha)
  calc
    _ ≤ Real.exp (a^2/2*t) * (Real.exp (a*r)*‖f‖^2) :=
      hi.2.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)
    _ = _ := by rw [← mul_assoc, ← Real.exp_add]

 theorem heatAt_exponential_square_lintegral_le (f : Lp ℝ 2 μ) (p : X)
    {r : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (a*dist p x) * heatAt μ hQ t f x ^ 2) ∂μ) ≤
      ENNReal.ofReal (Real.exp (a^2/2*t+a*r) * ‖f‖^2) := by
  let u := heatAt μ hQ t f
  let F := fun (i : ℕ) x => ENNReal.ofReal (radialWeight p a i x*u x^2)
  have hmeas (i : ℕ) : AEMeasurable (F i) μ :=
    ((radialWeight_lipschitz p ha i).continuous.measurable.aemeasurable.mul
      ((Lp.aestronglyMeasurable u).aemeasurable.pow_const 2)).ennreal_ofReal
  have hmono : ∀ᵐ x ∂μ, Monotone (fun i => F i x) := Eventually.of_forall fun x i j hij => by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (min_le_min_left _ (Nat.cast_le.mpr hij)) ha)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (a*dist p x)*u x^2))) := Eventually.of_forall fun x => by
    have he : ∀ᶠ i : ℕ in atTop, dist p x ≤ (i : ℝ) :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_ge_atTop (dist p x))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with i hi
    simp only [F, radialWeight, min_eq_left hi]
  have hb (i : ℕ) : (∫⁻ x, F i x ∂μ) ≤
      ENNReal.ofReal (Real.exp (a^2/2*t+a*r)*‖f‖^2) := by
    have hi := heatAt_radialWeight_integral μ hQ f p ha i ht
    have hn : 0 ≤ᵐ[μ] (fun x => radialWeight p a i x*u x^2) :=
      Eventually.of_forall fun x => mul_nonneg (radialWeight_nonneg p a i x) (sq_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hi.1 hn]
    exact ENNReal.ofReal_le_ofReal (heatAt_radialWeight_integral_le μ hQ f p hf ha i ht)
  exact le_of_tendsto (lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim)
    (Eventually.of_forall hb)

end HeatExponential

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]

 theorem integrable_exp_neg_dist_of_volume (p : X) {A B a : ℝ}
    (_hA : 0 ≤ A) (hB : 0 ≤ B) (ha : B < a)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R)) :
    Integrable (fun x => Real.exp (-a*dist p x)) μ := by
  let s : ℕ → Set X := fun i => {x | (i:ℝ) ≤ dist p x ∧ dist p x ≤ i+1}
  have hclosed (i : ℕ) : IsClosed (s i) :=
    (isClosed_le continuous_const (continuous_const.dist continuous_id)).inter
      (isClosed_le (continuous_const.dist continuous_id) continuous_const)
  have hsub (i : ℕ) : s i ⊆ Metric.closedBall p (2*((i:ℝ)+1)) := by
    intro x hx
    simp only [Metric.mem_closedBall, dist_comm]
    have hi : 0 ≤ (i:ℝ) := Nat.cast_nonneg i
    exact hx.2.trans (by linarith)
  have hcompact (i : ℕ) : IsCompact (s i) :=
    (isCompact_closedBall p (2*((i:ℝ)+1))).of_isClosed_subset (hclosed i) (hsub i)
  have hi (i : ℕ) : IntegrableOn (fun x => Real.exp (-a*dist p x)) (s i) μ :=
    ContinuousOn.integrableOn_compact (hcompact i)
      (Real.continuous_exp.comp (continuous_const.mul (continuous_const.dist continuous_id))).continuousOn
  have hb (i : ℕ) : (∫ x in s i, ‖Real.exp (-a*dist p x)‖ ∂μ) ≤
      A*Real.exp B*(Real.exp (B-a))^i := by
    have hbound : (∫ x in s i, ‖Real.exp (-a*dist p x)‖ ∂μ) ≤
        μ.real (s i)*Real.exp (-a*(i:ℝ)) := by
      rw [← smul_eq_mul, ← setIntegral_const]
      apply integral_mono_ae (hi i).norm (integrableOn_const (hcompact i).measure_ne_top)
      filter_upwards [ae_restrict_mem (hclosed i).measurableSet] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hx.1 (by linarith))
    have hm : μ.real (s i) ≤ A*Real.exp (B*((i:ℝ)+1)) :=
      (measureReal_mono (hsub i) (isCompact_closedBall p _).measure_ne_top).trans
        (hvol _ (by linarith [Nat.cast_nonneg (α := ℝ) i]))
    calc
      _ ≤ (A*Real.exp (B*((i:ℝ)+1)))*Real.exp (-a*(i:ℝ)) :=
        hbound.trans (mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le)
      _ = _ := by
        rw [← Real.exp_nat_mul, mul_assoc A, mul_assoc A, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  have hsum : Summable (fun i : ℕ => ∫ x in s i, ‖Real.exp (-a*dist p x)‖ ∂μ) := by
    apply (summable_geometric_of_lt_one (Real.exp_pos (B-a)).le
      (Real.exp_lt_one_iff.mpr (by linarith))).mul_left (A*Real.exp B) |>.of_nonneg_of_le
        (fun _ => integral_nonneg fun _ => norm_nonneg _) hb
  have hs : (⋃ i, s i) = univ := by
    apply eq_univ_of_forall
    intro x
    apply mem_iUnion.mpr
    refine ⟨⌊dist p x⌋₊, ?_⟩
    exact ⟨Nat.floor_le (dist_nonneg), (Nat.lt_floor_add_one (dist p x)).le⟩
  simpa only [hs, integrableOn_univ] using integrableOn_iUnion_of_summable_integral_norm hi hsum

 theorem integrable_dist_pow_mul_exp (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (k : ℕ) :
    Integrable (fun x => dist p x^k * Real.exp (-(B+(k:ℝ)+1)*dist p x)) μ := by
  have hi := integrable_exp_neg_dist_of_volume μ p hA hB (by linarith : B < B+1) hvol
  apply hi.mono' (((continuous_const.dist continuous_id).pow k).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.dist continuous_id)))).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖dist p x^k * Real.exp (-(B+(k:ℝ)+1)*dist p x)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg dist_nonneg _) (Real.exp_pos _).le)]
  have hd : dist p x ≤ Real.exp (dist p x) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    dist p x^k * Real.exp (-(B+(k:ℝ)+1)*dist p x) ≤
        (Real.exp (dist p x))^k * Real.exp (-(B+(k:ℝ)+1)*dist p x) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ dist_nonneg hd k) (Real.exp_pos _).le
    _ = Real.exp (-(B+1)*dist p x) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
end RegularPointCoordinates

end OAI

import Mathlib
import OAI.Analysis.RCDHeat.HeatFisher

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HeatTest, RadialEnergy, MassError, MassConservation, MassExtension. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
open Metric
section HeatTest
 theorem abs_sub_le_potential_drop {A P E I : ℝ → ℝ} {d B : ℝ}
    (hAc : ContinuousOn A (Ici 0)) (hPc : ContinuousOn P (Ici 0))
    (hAd : ∀ s, 0 < s → HasDerivAt A (-E s) s)
    (hPd : ∀ s, 0 < s → HasDerivAt P (-I s) s)
    (hEI : ∀ s, 0 < s → |E s| ≤ d * I s + B) {t : ℝ} (ht : 0 ≤ t) :
    |A t - A 0| ≤ d * (P 0-P t) + B*t := by
  have hm (c : ℝ) (hc : |c| ≤ 1) :
      AntitoneOn (fun s => c*A s+d*P s-B*s) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (((continuousOn_const.mul hAc).add (continuousOn_const.mul hPc)).sub
        (continuousOn_const.mul continuousOn_id))
      (fun s hs => (((hAd s (by simpa only [interior_Ici, mem_Ioi] using hs)).const_mul c).add
        ((hPd s (by simpa only [interior_Ici, mem_Ioi] using hs)).const_mul d) |>.sub
          ((hasDerivAt_id s).const_mul B)).hasDerivWithinAt)
    intro s hs
    have hh := hEI s (by simpa only [interior_Ici, mem_Ioi] using hs)
    have he : c*(-E s) ≤ |E s| := by
      calc
        _ ≤ |c*(-E s)| := le_abs_self _
        _ = |c| * |E s| := by rw [abs_mul, abs_neg]
        _ ≤ 1*|E s| := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
        _ = _ := one_mul _
    linarith
  have hp := hm 1 (by norm_num) (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
  have hn := hm (-1) (by norm_num) (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
  dsimp only at hp hn
  apply abs_le.mpr
  constructor <;> linarith

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] [SigmaFinite μ] (hQ : QuadraticCheegerEnergy μ)

omit [ProperSpace X] [μ.Regular] [SigmaFinite μ] in
 theorem weightedSlope_le_mass (F : Lp ℝ 2 μ) (g : SobolevSpace μ hQ)
    (hF : 0 ≤ F) (hFi : Integrable F μ) {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ g x ≤ L) :
    (∫ x, |F x| * SobolevSpace.minimalSlope μ hQ g x ^ 2 ∂μ) ≤
      (∫ x, F x ∂μ)*L^2 := by
  have ha := (Lp.coeFn_nonneg _).mpr hF
  have hgn := (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ g)
  have hb : ∀ᵐ x ∂μ, |F x| * SobolevSpace.minimalSlope μ hQ g x ^ 2 ≤ F x*L^2 := by
    filter_upwards [ha, hg, hgn] with x hFx hgx hgnx
    rw [abs_of_nonneg hFx]
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ hgnx hL).mpr hgx) hFx
  have hi : Integrable (fun x => |F x| * SobolevSpace.minimalSlope μ hQ g x ^ 2) μ := by
    apply (hFi.mul_const (L^2)).mono'
      ((continuous_abs.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)).mul
        ((Lp.aestronglyMeasurable _).pow 2))
    filter_upwards [hb] with x hx
    change |(|F x| * SobolevSpace.minimalSlope μ hQ g x ^ 2)| ≤ F x*L^2
    rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))]
    exact hx
  rw [← integral_mul_const]
  exact integral_mono_ae hi (hFi.mul_const _) hb

omit [SigmaFinite μ] in
 theorem heatAt_inner_lp_hasDerivAt (f : Lp ℝ 2 μ) (g : SobolevSpace μ hQ)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => inner ℝ (heatAt μ hQ s f) (SobolevSpace.toLp μ hQ g))
      (-energyForm μ hQ (heatSobolev μ hQ t ht f) g) t := by
  have h := (heatAt_hasDerivAt μ hQ t ht f).inner ℝ
    (hasDerivAt_const t (SobolevSpace.toLp μ hQ g))
  simpa only [heatGeneratorAt_of_pos μ hQ t ht, inner_neg_left, inner_zero_right, zero_add,
    ← heatGenerator_form] using h

 theorem heatAt_inner_abs_sub_le (f : Lp ℝ 2 μ) (g : SobolevSpace μ hQ)
    (hf : 0 ≤ f) (hfi : Integrable f μ) (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, |f x| ≤ C)
    {L : ℝ} (hL : 0 ≤ L) (hg : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ g x ≤ L)
    {ε δ t : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (ht : 0 ≤ t) :
    |inner ℝ (heatAt μ hQ t f-f) (SobolevSpace.toLp μ hQ g)| ≤
      δ/2 * integralPotential μ (regularizedEntropy ε) f +
      t*((∫ x, f x ∂μ)*L^2/(2*δ) + ε*SobolevSpace.energy μ hQ g/δ) := by
  let A := fun s => inner ℝ (heatAt μ hQ s f) (SobolevSpace.toLp μ hQ g)
  let P := fun s => integralPotential μ (regularizedEntropy ε) (heatAt μ hQ s f)
  let E := fun s => inner ℝ (heatGeneratorAt μ hQ s f) (SobolevSpace.toLp μ hQ g)
  let I := regularizedFisher μ hQ hε f
  let B := (∫ x, f x ∂μ)*L^2/(2*δ) + ε*SobolevSpace.energy μ hQ g/δ
  have hA : ContinuousOn A (Ici 0) := ((heatAt_continuous μ hQ f).inner continuous_const).continuousOn
  have hP : ContinuousOn P (Ici 0) := ((integralPotential_continuous μ
    (regularizedEntropy_hasDerivAt ε) (regularizedEntropy_zero ε)
    (regularizedLog_lipschitz hε) (regularizedLog_zero ε)).comp (heatAt_continuous μ hQ f)).continuousOn
  have hAd (s : ℝ) (hs : 0 < s) : HasDerivAt A (-E s) s := by
    simpa only [E, heatGeneratorAt_of_pos μ hQ s hs, ← heatGenerator_form] using
      heatAt_inner_lp_hasDerivAt μ hQ f g s hs
  have hPd (s : ℝ) (hs : 0 < s) : HasDerivAt P (-I s) s :=
    heatAt_integralPotential_deriv_form μ hQ (regularizedEntropy_hasDerivAt ε)
      (regularizedEntropy_zero ε) (regularizedLog_lipschitz hε) (regularizedLog_zero ε) f s hs
  have hEI (s : ℝ) (hs : 0 < s) : |E s| ≤ (δ/2)*I s+B := by
    have hsC := heatAt_abs_le_const μ hQ s C f hfC
    have hu := energyForm_weighted_young_scaled μ hQ (heatSobolev μ hQ s hs f) g hε hδ C
      (by simpa only [heatSobolev_toLp] using hsC)
    have hw := weightedSlope_le_mass μ hQ (heatAt μ hQ s f) g (heatAt_nonneg μ hQ s f hf)
      (heatAt_integrable_of_nonneg μ hQ s f hf hfi) hL hg
    have hmass := heatAt_integral_le_of_nonneg μ hQ s f hf hfi
    have hw' := hw.trans (mul_le_mul_of_nonneg_right hmass (sq_nonneg L))
    rw [heatSobolev_toLp, ← regularizedFisher_eq_integral μ hQ hε f s hs,
      heatGenerator_form] at hu
    have hd := div_le_div_of_nonneg_right hw' (show 0 ≤ 2*δ by positivity)
    dsimp only [E, I, B]
    rw [heatGeneratorAt_of_pos μ hQ s hs]
    linarith
  have hh := abs_sub_le_potential_drop hA hP hAd hPd hEI ht
  have hp : 0 ≤ P t := integral_nonneg fun x => regularizedEntropy_nonneg hε _
  dsimp only [A, P, B] at hh hp
  rw [heatAt_zero μ hQ] at hh
  rw [inner_sub_left]
  change |inner ℝ (heatAt μ hQ t f) (SobolevSpace.toLp μ hQ g) -
    inner ℝ f (SobolevSpace.toLp μ hQ g)| ≤ _
  change |inner ℝ (heatAt μ hQ t f) (SobolevSpace.toLp μ hQ g) - inner ℝ f (SobolevSpace.toLp μ hQ g)| ≤
    δ/2*(integralPotential μ (regularizedEntropy ε) f -
      integralPotential μ (regularizedEntropy ε) (heatAt μ hQ t f)) + _ at hh
  nlinarith
end HeatTest

section RadialEnergy
variable {X : Type u} [MetricSpace X]
 theorem radialCutoff_eventually_one (p x : X) :
    ∀ᶠ R : ℝ in atTop, radialCutoff p R x = 1 := by
  filter_upwards [eventually_ge_atTop (max 1 (dist p x))] with R hR
  exact radialCutoff_eq_one p (lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR))
    ((le_max_right _ _).trans hR)

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
 theorem integral_radialCutoff_tendsto (p : X) (f : X → ℝ) (hf : Integrable f μ) :
    Tendsto (fun R : ℝ => ∫ x, f x * radialCutoff p R x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact hf.aestronglyMeasurable.mul (radialCutoff_lipschitz p hR).continuous.aestronglyMeasurable
  · exact Eventually.of_forall fun R => Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_of_nonneg (radialCutoff_bounds p R x).1]
      exact mul_le_of_le_one_right (norm_nonneg _) (radialCutoff_bounds p R x).2
  · exact hf.norm
  · exact Eventually.of_forall fun x => (tendsto_const_nhds : Tendsto (fun _ : ℝ => f x) atTop (𝓝 (f x))).congr'
      ((radialCutoff_eventually_one p x).mono fun R hR => by change f x = f x * radialCutoff p R x; rw [hR, mul_one])

variable [ProperSpace X] [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)
 theorem radialSobolevCutoff_slope_bound (p : X) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (radialSobolevCutoff μ hQ p hR) x ≤ R⁻¹ := by
  filter_upwards [radialSobolevCutoff_slope_le μ hQ p hR] with x hx
  exact hx.trans (indicator_le_self' (fun _ _ => inv_nonneg.mpr hR.le) x)

 theorem radialSobolevCutoff_energy_le (p : X) {R : ℝ} (hR : 0 < R) :
    SobolevSpace.energy μ hQ (radialSobolevCutoff μ hQ p hR) ≤
      μ.real (Metric.closedBall p (2*R)) / (2*R^2) := by
  let g := radialSobolevCutoff μ hQ p hR
  let D := SobolevSpace.minimalSlope μ hQ g
  let s := Metric.closedBall p (2*R)
  have hs : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  have hμs : μ s ≠ ∞ := (isCompact_closedBall p (2*R)).measure_lt_top.ne
  have hi : Integrable (s.indicator (fun _ => R⁻¹^2)) μ :=
    (integrable_indicator_iff hs).mpr (integrableOn_const hμs)
  have hDi : Integrable (fun x => D x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using (Lp.memLp D).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hle : (∫ x, D x^2 ∂μ) ≤ ∫ x, s.indicator (fun _ => R⁻¹^2) x ∂μ := by
    apply integral_mono_ae hDi hi
    filter_upwards [radialSobolevCutoff_slope_le μ hQ p hR,
      (Lp.coeFn_nonneg D).mpr (SobolevSpace.minimalSlope_nonneg μ hQ g)] with x hx hn
    change D x ≤ s.indicator (fun _ => R⁻¹) x at hx
    by_cases hxs : x ∈ s
    · rw [indicator_of_mem hxs] at hx ⊢
      exact pow_le_pow_left₀ hn hx 2
    · rw [indicator_of_notMem hxs] at hx ⊢
      rw [le_antisymm hx hn, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  rw [integral_sq_Lp, SobolevSpace.minimalSlope_norm_sq, integral_indicator_const _ hs,
    smul_eq_mul] at hle
  change 2*SobolevSpace.energy μ hQ g ≤ μ.real s * R⁻¹^2 at hle
  have he : μ.real s / (2*R^2) = (μ.real s * R⁻¹^2)/2 := by field_simp
  rw [he]
  linarith

 theorem lp_inner_radialCutoff (p : X) {R : ℝ} (hR : 0 < R) (f : Lp ℝ 2 μ) :
    inner ℝ f (SobolevSpace.toLp μ hQ (radialSobolevCutoff μ hQ p hR)) =
      ∫ x, f x * radialCutoff p R x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [radialSobolevCutoff_coe μ hQ p hR] with x hx
  rw [Real.inner_apply, hx]
end RadialEnergy

section MassError
 theorem regularized_cutoff_error_le (M A B D t r : ℝ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hD : 0 ≤ D) (ht : 0 ≤ t) (hr : 1 ≤ r) :
    (r^3)⁻¹/2*(M*((B+1)*r^2+D)) +
      t*(M*((r^2)⁻¹)^2/(2*(r^3)⁻¹) +
        Real.exp (-((B+1)*r^2))*(A*Real.exp (B*r^2)/(2*(r^2)^2))/(r^3)⁻¹) ≤
      (M*(B+1+D)+t*(M+A))/(2*r) := by
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hsq : 1 ≤ r^2 := by nlinarith [sq_nonneg (r-1)]
  have hr3 : r ≤ r^3 := by nlinarith [mul_nonneg hrp.le (sub_nonneg.mpr hsq)]
  have hD' : M*D/(2*r^3) ≤ M*D/(2*r) :=
    div_le_div_of_nonneg_left (mul_nonneg hM hD) (by positivity) (by linarith)
  have he : Real.exp (-((B+1)*r^2))*Real.exp (B*r^2) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    nlinarith [sq_nonneg r]
  have he' : A*(Real.exp (-((B+1)*r^2))*Real.exp (B*r^2))/(2*r) ≤ A/(2*r) :=
    div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  calc
    _ = M*(B+1)/(2*r) + M*D/(2*r^3) +
        t*(M/(2*r) + A*(Real.exp (-((B+1)*r^2))*Real.exp (B*r^2))/(2*r)) := by
      field_simp
    _ ≤ M*(B+1)/(2*r) + M*D/(2*r) + t*(M/(2*r)+A/(2*r)) := by
      nlinarith
    _ = _ := by ring
end MassError

section MassConservation
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] [SigmaFinite μ]
  (hQ : QuadraticCheegerEnergy μ)

 theorem heatAt_cutoff_mass_bound (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (hfi : Integrable f μ)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) {t r : ℝ} (ht : 0 ≤ t) (hr : 1 ≤ r) :
    |(∫ x, (heatAt μ hQ t f x-f x)*radialCutoff p (r^2) x ∂μ)| ≤
      ((∫ x, f x ∂μ)*(B+1+Real.log (1+2*(C:ℝ))) + t*((∫ x, f x ∂μ)+A))/(2*r) := by
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hr2 : 0 < r^2 := sq_pos_of_pos hrp
  have hr21 : 1 ≤ r^2 := by nlinarith [sq_nonneg (r-1)]
  let g := radialSobolevCutoff μ hQ p hr2
  let ε := Real.exp (-((B+1)*r^2))
  let δ := (r^3)⁻¹
  let M := ∫ x, f x ∂μ
  let D := Real.log (1+2*(C:ℝ))
  have hM : 0 ≤ M := integral_nonneg_of_ae ((Lp.coeFn_nonneg _).mpr hf)
  have hD : 0 ≤ D := Real.log_nonneg (by linarith [C.coe_nonneg])
  have hε : 0 < ε := Real.exp_pos _
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hu := heatAt_inner_abs_sub_le μ hQ f g hf hfi C hfC
    (inv_nonneg.mpr hr2.le) (radialSobolevCutoff_slope_bound μ hQ p hr2) hε hδ ht
  have hp := regularizedPotential_exp_le μ f C.coe_nonneg
    (show 0 ≤ (B+1)*r^2 by positivity)
    (by filter_upwards [(Lp.coeFn_nonneg _).mpr hf, hfC] with x hx hCx
        exact ⟨hx, (le_abs_self _).trans hCx⟩) hfi
  have hg : SobolevSpace.energy μ hQ g ≤ A*Real.exp (B*r^2)/(2*(r^2)^2) :=
    (radialSobolevCutoff_energy_le μ hQ p hr2).trans
      (div_le_div_of_nonneg_right (hvol _ hr21) (by positivity))
  have hterm := mul_le_mul_of_nonneg_left hp (show 0 ≤ δ/2 by positivity)
  have heterm := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg hε.le) hδ.le) ht
  rw [lp_inner_radialCutoff μ hQ p hr2] at hu
  have hie : (∫ x, (heatAt μ hQ t f-f) x * radialCutoff p (r^2) x ∂μ) =
      ∫ x, (heatAt μ hQ t f x-f x)*radialCutoff p (r^2) x ∂μ :=
    integral_congr_ae ((Lp.coeFn_sub _ _).mono fun x hx => congrArg (fun a => a*radialCutoff p (r^2) x) hx)
  rw [hie] at hu
  have hbound := regularized_cutoff_error_le M A B D t r hM hA hD ht hr
  dsimp only [M, D, δ, ε] at hu hterm heterm hbound
  nlinarith

 theorem heatAt_integral_eq_of_exponential_volume_bounded (p : X) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (hfi : Integrable f μ)
    (C : ℝ≥0) (hfC : ∀ᵐ x ∂μ, |f x| ≤ C) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, heatAt μ hQ t f x ∂μ) = ∫ x, f x ∂μ := by
  have hti := heatAt_integrable_of_nonneg μ hQ t f hf hfi
  have hlim := (integral_radialCutoff_tendsto μ p (fun x => heatAt μ hQ t f x-f x)
    (hti.sub hfi)).comp (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0))
  let K := ((∫ x, f x ∂μ)*(B+1+Real.log (1+2*(C:ℝ)))+t*((∫ x, f x ∂μ)+A))/2
  have hzero : Tendsto (fun r : ℝ => K/r) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul K
  have hle : |∫ x, heatAt μ hQ t f x-f x ∂μ| ≤ 0 := by
    apply le_of_tendsto_of_tendsto hlim.abs hzero
    filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
    have he := heatAt_cutoff_mass_bound μ hQ p hA hB hvol f hf hfi C hfC ht hr
    change |∫ x, (heatAt μ hQ t f x-f x)*radialCutoff p (r^2) x ∂μ| ≤ K/r
    refine he.trans_eq ?_
    dsimp only [K]
    ring
  have he := abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  rw [integral_sub hti hfi] at he
  exact sub_eq_zero.mp he
end MassConservation

section MassExtension
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] [SigmaFinite μ]
  (hQ : QuadraticCheegerEnergy μ)

 theorem heatAt_integral_eq_of_exponential_volume (p : X) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf : 0 ≤ f) (hfi : Integrable f μ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, heatAt μ hQ t f x ∂μ) = ∫ x, f x ∂μ := by
  have hfn := (Lp.coeFn_nonneg f).mpr hf
  have hti := heatAt_integrable_of_nonneg μ hQ t f hf hfi
  apply le_antisymm (heatAt_integral_le_of_nonneg μ hQ t f hf hfi)
  have hlim : Tendsto (fun k : ℕ => ∫ x, min (f x) (k:ℝ) ∂μ) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |f x|)
    · intro k
      exact (Lp.aestronglyMeasurable f).inf aestronglyMeasurable_const
    · exact hfi.abs
    · intro k
      filter_upwards [hfn] with x hx
      rw [Real.norm_of_nonneg (le_min hx (Nat.cast_nonneg k)), abs_of_nonneg hx]
      exact min_le_left _ _
    · filter_upwards with x
      apply tendsto_const_nhds.congr'
      obtain ⟨k, hk⟩ := exists_nat_ge (f x)
      filter_upwards [eventually_ge_atTop k] with j hj
      exact (min_eq_left (hk.trans (by exact_mod_cast hj))).symm
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro k
  let φ : ℝ → ℝ := fun a => min a (k:ℝ)
  have hφ : LipschitzWith 1 φ := LipschitzWith.id.min_const _
  have hφ0 : φ 0 = 0 := min_eq_left (Nat.cast_nonneg k)
  let g := hφ.compLp hφ0 f
  have hge : ∀ᵐ x ∂μ, g x = min (f x) (k:ℝ) := hφ.coeFn_compLp hφ0 f
  have hgn : 0 ≤ g := (Lp.coeFn_nonneg g).mp (by
    filter_upwards [hge, hfn] with x he hx
    rw [he]
    exact le_min hx (Nat.cast_nonneg k))
  have hgf : g ≤ f := (Lp.coeFn_le g f).mp (by
    filter_upwards [hge] with x he
    rw [he]
    exact min_le_left _ _)
  have hgi : Integrable g μ := hfi.mono' (Lp.aestronglyMeasurable g) (by
    filter_upwards [hge, hfn] with x he hx
    rw [he, Real.norm_of_nonneg (le_min hx (Nat.cast_nonneg k))]
    exact min_le_left _ _)
  have hgC : ∀ᵐ x ∂μ, |g x| ≤ (k:ℝ≥0) := by
    filter_upwards [hge, hfn] with x he hx
    rw [he, abs_of_nonneg (le_min hx (Nat.cast_nonneg k))]
    exact min_le_right _ _
  calc
    (∫ x, min (f x) (k:ℝ) ∂μ) = ∫ x, g x ∂μ := integral_congr_ae (Filter.EventuallyEq.symm hge)
    _ = ∫ x, heatAt μ hQ t g x ∂μ :=
      (heatAt_integral_eq_of_exponential_volume_bounded μ hQ p hA hB hvol g hgn hgi k hgC ht).symm
    _ ≤ ∫ x, heatAt μ hQ t f x ∂μ := integral_mono_ae
      (heatAt_integrable_of_nonneg μ hQ t g hgn hgi) hti
      ((Lp.coeFn_le _ _).mpr (heatAt_mono μ hQ t hgf))
end MassExtension

 

theorem locallyFinite_of_finiteOnBounded
    {X : Type*} [MetricSpace X] [MeasurableSpace X] (μ : Measure X)
    (hμ : ∀ s : Set X, Bornology.IsBounded s → μ s < ∞) :
    IsLocallyFiniteMeasure μ := by
  constructor
  intro x
  exact ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num),
    hμ _ Metric.isBounded_ball⟩

 
noncomputable def uniformOn {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X) : Measure X := (μ s)⁻¹ • μ.restrict s

theorem uniformOn_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X) (hs0 : μ s ≠ 0) (hs_top : μ s ≠ ∞) :
    IsProbabilityMeasure (uniformOn μ s) := by
  constructor
  simp only [uniformOn, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hs0 hs_top

theorem uniformOn_absolutelyContinuous {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X) : (uniformOn μ s).AbsolutelyContinuous μ := by
  exact (Measure.absolutelyContinuous_restrict (μ := μ) (s := s)).smul_left _

theorem uniformOn_ae_mem {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    ∀ᵐ x ∂uniformOn μ s, x ∈ s := by
  exact ((Measure.AbsolutelyContinuous.rfl : μ.restrict s ≪ μ.restrict s).smul_left ((μ s)⁻¹)).ae_le (ae_restrict_mem hs)

 
theorem uniformOn_finiteSecondMoment {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (hs0 : μ s ≠ 0) (hs_top : μ s ≠ ∞)
    (o : X) (R : ℝ) (hR : ∀ x ∈ s, dist x o ≤ R) :
    FiniteSecondMoment (uniformOn μ s) := by
  let := uniformOn_probability μ s hs0 hs_top
  refine ⟨o, lt_of_le_of_lt (lintegral_mono_ae (g := fun _ => ENNReal.ofReal R ^ 2) ?_) ?_⟩
  · filter_upwards [uniformOn_ae_mem μ s hs] with x hx
    exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal (hR x hx)) 2
  · simp only [lintegral_const, measure_univ, mul_one]
    finiteness

 

theorem renyiIntegral_le_support_volume
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [SigmaFinite μ] [IsProbabilityMeasure ν]
    (s : Set X) (hs : MeasurableSet s) (hνs : ∀ᵐ x ∂ν, x ∈ s)
    (N : ℝ) (hN : 1 < N) :
    renyiIntegral μ ν N ≤ (μ s) ^ (1 / N) := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hα : 0 < 1 - 1 / N := by
    rw [sub_pos, div_lt_one hN0]
    exact hN
  have hconj : (1 / (1 - 1 / N)).HolderConjugate N := by
    rw [Real.holderConjugate_iff]
    constructor
    · rw [lt_div_iff₀ hα]
      have : 0 < 1 / N := one_div_pos.mpr hN0
      linarith
    · simp
  have hsupport : (fun x => (ν.rnDeriv μ x) ^ (1 - 1 / N)) =ᵐ[μ]
      s.indicator (fun x => (ν.rnDeriv μ x) ^ (1 - 1 / N)) := by
    filter_upwards [Measure.ae_rnDeriv_ne_zero_imp_of_ae μ hνs] with x hx
    by_cases hxs : x ∈ s
    · simp [hxs]
    · have hz : ν.rnDeriv μ x = 0 := by
        by_contra hn
        exact hxs (hx hn)
      rw [hz, ENNReal.zero_rpow_of_pos hα, Set.indicator_of_notMem hxs]
  have hmul : (1 - 1 / N) * (1 / (1 - 1 / N)) = 1 := by
    exact mul_one_div_cancel hα.ne'
  have hinv : 1 / (1 / (1 - 1 / N)) = 1 - 1 / N := by simp
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (μ.restrict s) hconj
    (((Measure.measurable_rnDeriv ν μ).pow_const (1 - 1 / N)).aemeasurable)
    (f := fun x => (ν.rnDeriv μ x) ^ (1 - 1 / N))
    (g := fun _ => (1 : ℝ≥0∞)) aemeasurable_const
  simp only [Pi.mul_apply, mul_one, ← ENNReal.rpow_mul, hmul, ENNReal.rpow_one,
    hinv, ENNReal.one_rpow, lintegral_const, one_mul, Measure.restrict_apply_univ] at hh
  have hmass : (∫⁻ x in s, ν.rnDeriv μ x ∂μ) ≤ 1 :=
    (Measure.setLIntegral_rnDeriv_le s).trans (prob_le_one (μ := ν))
  calc
    renyiIntegral μ ν N = ∫⁻ x in s, (ν.rnDeriv μ x) ^ (1 - 1 / N) ∂μ := by
      unfold renyiIntegral
      rw [lintegral_congr_ae hsupport, lintegral_indicator hs]
    _ ≤ (∫⁻ x in s, ν.rnDeriv μ x ∂μ) ^ (1 - 1 / N) * (μ s) ^ (1 / N) := hh
    _ ≤ 1 ^ (1 - 1 / N) * (μ s) ^ (1 / N) :=
      mul_le_mul_left (ENNReal.rpow_le_rpow hmass hα.le) _
    _ = _ := by simp

 

theorem uniformOn_rnDeriv {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (s : Set X) (hs : MeasurableSet s) :
    (uniformOn μ s).rnDeriv μ =ᵐ[μ] s.indicator (fun _ => (μ s)⁻¹) := by
  have heq : μ.withDensity (s.indicator (fun _ => (μ s)⁻¹)) = uniformOn μ s := by
    rw [withDensity_indicator hs, withDensity_const, uniformOn]
  rw [← heq]
  exact Measure.rnDeriv_withDensity μ (measurable_const.indicator hs)

theorem uniformOn_rnDeriv_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (s : Set X) (hs : MeasurableSet s) :
    ∀ᵐ x ∂uniformOn μ s, (uniformOn μ s).rnDeriv μ x = (μ s)⁻¹ := by
  have hrn := (uniformOn_absolutelyContinuous μ s).ae_le (uniformOn_rnDeriv μ s hs)
  filter_upwards [hrn, uniformOn_ae_mem μ s hs] with x hx hxs
  simpa only [Set.indicator_of_mem hxs] using hx

 

theorem uniformOn_rnDeriv_neg_power {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] (s : Set X) (hs : MeasurableSet s) (N : ℝ) :
    ∀ᵐ x ∂uniformOn μ s, ((uniformOn μ s).rnDeriv μ x) ^ (-(1 / N)) =
      (μ s) ^ (1 / N) := by
  filter_upwards [uniformOn_rnDeriv_ae μ s hs] with x hx
  rw [hx, ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
end RegularPointCoordinates

end OAI

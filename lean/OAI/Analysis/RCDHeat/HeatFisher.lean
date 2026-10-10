import Mathlib
import OAI.Analysis.RCDHeat.EnergyChain

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HeatFisher, HeatL1, EntropyBound, WeightedSlope, WeightedScaled, RadialCutoff. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
open Metric
section HeatFisher
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

noncomputable def regularizedFisher {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ) (t : ℝ) : ℝ :=
  heatDissipation μ hQ (regularizedLog_lipschitz hε) (regularizedLog_zero ε) f t

 theorem regularizedFisher_eq_integral {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ)
    (t : ℝ) (ht : 0 < t) : regularizedFisher μ hQ hε f t =
    ∫ x, regularizedReciprocal ε (heatAt μ hQ t f x) *
      SobolevSpace.minimalSlope μ hQ (heatSobolev μ hQ t ht f) x ^ 2 ∂μ :=
  heatDissipation_eq_integral μ hQ (regularizedLog_lipschitz hε) (regularizedLog_zero ε)
    (regularizedReciprocal_continuous ε) (regularizedLog_hasDerivAt ε)
    ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩ (regularizedReciprocal_bound hε) f t ht

 theorem regularizedFisher_nonneg {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ)
    (t : ℝ) (ht : 0 < t) : 0 ≤ regularizedFisher μ hQ hε f t := by
  rw [regularizedFisher_eq_integral μ hQ hε f t ht]
  exact integral_nonneg fun x => mul_nonneg (regularizedReciprocal_nonneg hε _) (sq_nonneg _)

 theorem heatAt_regularizedEntropy_antitoneOn {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ) :
    AntitoneOn (fun t => integralPotential μ (regularizedEntropy ε) (heatAt μ hQ t f)) (Ici 0) :=
  heatAt_integralPotential_antitoneOn μ hQ (regularizedEntropy_hasDerivAt ε)
    (regularizedEntropy_zero ε) (regularizedLog_lipschitz hε) (regularizedLog_zero ε)
    (regularizedReciprocal_continuous ε) (regularizedLog_hasDerivAt ε)
    ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩ (regularizedReciprocal_bound hε)
    (regularizedReciprocal_nonneg hε) f

 theorem heatAt_regularizedEntropy_dissipation {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, regularizedFisher μ hQ hε f s) =
      integralPotential μ (regularizedEntropy ε) (heatAt μ hQ a f) -
      integralPotential μ (regularizedEntropy ε) (heatAt μ hQ b f) :=
  heatAt_integralPotential_dissipation μ hQ (regularizedEntropy_hasDerivAt ε)
    (regularizedEntropy_zero ε) (regularizedLog_lipschitz hε) (regularizedLog_zero ε) f a b ha hab

 theorem regularizedFisher_integral_le {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, regularizedFisher μ hQ hε f s) ≤
      integralPotential μ (regularizedEntropy ε) f := by
  rw [heatAt_regularizedEntropy_dissipation μ hQ hε f a b ha hab]
  have hn : 0 ≤ integralPotential μ (regularizedEntropy ε) (heatAt μ hQ b f) :=
    integral_nonneg fun x => regularizedEntropy_nonneg hε _
  have ha' := heatAt_regularizedEntropy_antitoneOn μ hQ hε f (show (0 : ℝ) ∈ Ici 0 by simp)
    (show a ∈ Ici 0 from ha.le) ha.le
  dsimp only at ha'
  rw [heatAt_zero μ hQ] at ha'
  change integralPotential μ (regularizedEntropy ε) (heatAt μ hQ a f) ≤
    integralPotential μ (regularizedEntropy ε) f at ha'
  linarith

end HeatFisher

section HeatL1
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem heatAt_integralOn_le (t : ℝ) (f : Lp ℝ 2 μ) (hf : 0 ≤ f)
    (hfi : Integrable f μ) (s : Set X) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    (∫ x in s, heatAt μ hQ t f x ∂μ) ≤ ∫ x, f x ∂μ := by
  let g : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs 1
  have hg : ∀ᵐ x ∂μ, g x ≤ 1 := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x hx
    change g x = _ at hx
    rw [hx]
    by_cases hx : x ∈ s <;> simp [hx]
  have hgt := heatAt_le_const μ hQ t zero_le_one g hg
  rw [← L2.inner_indicatorConstLp_one hs hμs, ← heatAt_inner, L2.inner_def]
  apply integral_mono_ae (L2.integrable_inner _ _) hfi
  filter_upwards [hgt, (Lp.coeFn_nonneg f).mpr hf] with x hgx hfx
  rw [Real.inner_apply]
  change (heatAt μ hQ t g x) * f x ≤ f x
  change 0 ≤ f x at hfx
  nlinarith

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
 theorem lp_integrableOn_of_finite (f : Lp ℝ 2 μ) (s : Set X) (hμs : μ s ≠ ∞) :
    IntegrableOn f s μ := by
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa only [Measure.restrict_apply_univ] using hμs.lt_top⟩
  exact MemLp.integrable (by norm_num) ((Lp.memLp f).restrict s)

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
 theorem spanningSets_aecover [SigmaFinite μ] : AECover μ atTop (spanningSets μ) where
  measurableSet := measurableSet_spanningSets μ
  ae_eventually_mem := by
    filter_upwards with x
    filter_upwards [eventually_ge_atTop (spanningSetsIndex μ x)] with i hi
    exact monotone_spanningSets μ hi (mem_spanningSetsIndex μ x)

 theorem heatAt_integrable_of_nonneg [SigmaFinite μ] (t : ℝ) (f : Lp ℝ 2 μ)
    (hf : 0 ≤ f) (hfi : Integrable f μ) : Integrable (heatAt μ hQ t f) μ := by
  apply (spanningSets_aecover μ).integrable_of_integral_norm_bounded (∫ x, f x ∂μ)
    (fun i => lp_integrableOn_of_finite μ _ _ (measure_spanningSets_lt_top μ i).ne)
  apply Eventually.of_forall
  intro i
  have hp := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf)
  calc
    (∫ x in spanningSets μ i, ‖heatAt μ hQ t f x‖ ∂μ) =
        ∫ x in spanningSets μ i, heatAt μ hQ t f x ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hp] with x hx using Real.norm_of_nonneg hx
    _ ≤ ∫ x, f x ∂μ := heatAt_integralOn_le μ hQ t f hf hfi _
      (measurableSet_spanningSets μ i) (measure_spanningSets_lt_top μ i).ne

 theorem heatAt_integral_le_of_nonneg [SigmaFinite μ] (t : ℝ) (f : Lp ℝ 2 μ)
    (hf : 0 ≤ f) (hfi : Integrable f μ) :
    (∫ x, heatAt μ hQ t f x ∂μ) ≤ ∫ x, f x ∂μ := by
  apply le_of_tendsto ((spanningSets_aecover μ).integral_tendsto_of_countably_generated
    (heatAt_integrable_of_nonneg μ hQ t f hf hfi))
  exact Eventually.of_forall fun i => heatAt_integralOn_le μ hQ t f hf hfi _
    (measurableSet_spanningSets μ i) (measure_spanningSets_lt_top μ i).ne

 theorem heatAt_mono (t : ℝ) : Monotone (heatAt μ hQ t) := by
  intro f g hfg
  exact heatFlow_mono μ hQ _ _ hfg

 theorem heatAt_abs_le (t : ℝ) (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ, |heatAt μ hQ t f x| ≤ heatAt μ hQ t |f| x := by
  have hp := (Lp.coeFn_le _ _).mpr (heatAt_mono μ hQ t (le_abs_self f))
  have hm := heatAt_mono μ hQ t (neg_le_abs f)
  rw [map_neg] at hm
  filter_upwards [hp, (Lp.coeFn_le _ _).mpr hm, Lp.coeFn_neg (heatAt μ hQ t f)] with x hp hm he
  rw [he] at hm
  exact abs_le.mpr ⟨by simpa only [Pi.neg_apply, neg_le] using hm, hp⟩

 theorem heatAt_integrable [SigmaFinite μ] (t : ℝ) (f : Lp ℝ 2 μ)
    (hfi : Integrable f μ) : Integrable (heatAt μ hQ t f) μ := by
  have habs : Integrable (|f| : Lp ℝ 2 μ) μ := hfi.abs.congr (Lp.coeFn_abs f).symm
  exact (heatAt_integrable_of_nonneg μ hQ t |f| (abs_nonneg f) habs).mono'
    (Lp.aestronglyMeasurable _) (by simpa only [Real.norm_eq_abs] using heatAt_abs_le μ hQ t f)

 theorem heatAt_integral_abs_le [SigmaFinite μ] (t : ℝ) (f : Lp ℝ 2 μ)
    (hfi : Integrable f μ) :
    (∫ x, |heatAt μ hQ t f x| ∂μ) ≤ ∫ x, |f x| ∂μ := by
  have habs : Integrable (|f| : Lp ℝ 2 μ) μ := hfi.abs.congr (Lp.coeFn_abs f).symm
  calc
    (∫ x, |heatAt μ hQ t f x| ∂μ) ≤ ∫ x, heatAt μ hQ t |f| x ∂μ :=
      integral_mono_ae (heatAt_integrable μ hQ t f hfi).abs
        (heatAt_integrable_of_nonneg μ hQ t |f| (abs_nonneg f) habs) (heatAt_abs_le μ hQ t f)
    _ ≤ ∫ x, (|f| : Lp ℝ 2 μ) x ∂μ := heatAt_integral_le_of_nonneg μ hQ t |f| (abs_nonneg f) habs
    _ = ∫ x, |f x| ∂μ := integral_congr_ae (Lp.coeFn_abs f)

end HeatL1

section EntropyBound
 theorem regularizedEntropy_le {ε a C : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (haC : a ≤ C) :
    regularizedEntropy ε a ≤ a * regularizedLog ε C := by
  have h := intervalIntegral.integral_mono_on ha
    ((regularizedLog_continuous ε).intervalIntegrable 0 a)
    (continuous_const.intervalIntegrable (μ := volume) 0 a)
    (fun s (hs : s ∈ Icc (0:ℝ) a) =>
      Real.arsinh_le_arsinh.mpr (div_le_div_of_nonneg_right (hs.2.trans haC) hε.le))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, regularizedEntropy, regularizedLog] using h

 theorem regularizedLog_exp_bound {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R) :
    regularizedLog (Real.exp (-R)) C ≤ R + Real.log (1+2*C) := by
  have he : 1 ≤ Real.exp R := Real.one_le_exp_iff.mpr hR
  have hc : 0 ≤ C * Real.exp R := mul_nonneg hC (Real.exp_pos _).le
  have hs : Real.sqrt (1+(C*Real.exp R)^2) ≤ 1+C*Real.exp R :=
    (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
  have hp : 0 < C*Real.exp R + Real.sqrt (1+(C*Real.exp R)^2) := by
    have hsq : 0 < Real.sqrt (1+(C*Real.exp R)^2) := Real.sqrt_pos.mpr (by positivity)
    linarith
  unfold regularizedLog Real.arsinh
  rw [Real.exp_neg, div_inv_eq_mul]
  calc
    _ ≤ Real.log ((1+2*C)*Real.exp R) := Real.log_le_log hp (by nlinarith)
    _ = _ := by rw [Real.log_mul (by positivity) (Real.exp_pos R).ne', Real.log_exp]; ring

variable {X : Type u} [MeasurableSpace X] (μ : Measure X)
 theorem regularizedPotential_le_mass (f : Lp ℝ 2 μ) {ε C : ℝ} (hε : 0 < ε)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ C) (hfi : Integrable f μ) :
    integralPotential μ (regularizedEntropy ε) f ≤ (∫ x, f x ∂μ) * regularizedLog ε C := by
  unfold integralPotential
  rw [← integral_mul_const]
  apply integral_mono_ae (integralPotential_integrable μ (regularizedEntropy_hasDerivAt ε)
    (regularizedEntropy_zero ε) (regularizedLog_lipschitz hε) (regularizedLog_zero ε) f)
    (hfi.mul_const _)
  filter_upwards [hf] with x hx
  exact regularizedEntropy_le hε hx.1 hx.2

 theorem regularizedPotential_exp_le (f : Lp ℝ 2 μ) {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ C) (hfi : Integrable f μ) :
    integralPotential μ (regularizedEntropy (Real.exp (-R))) f ≤
      (∫ x, f x ∂μ) * (R + Real.log (1+2*C)) := by
  exact (regularizedPotential_le_mass μ f (Real.exp_pos _) hf hfi).trans
    (mul_le_mul_of_nonneg_left (regularizedLog_exp_bound hC hR)
      (integral_nonneg_of_ae (hf.mono fun _ hx => hx.1)))
end EntropyBound

section WeightedSlope

 theorem regularizedReciprocal_eq {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    regularizedReciprocal ε a = (Real.sqrt (ε^2+a^2))⁻¹ := by
  have hεne := ne_of_gt hε
  have he : 1+(a/ε)^2 = (ε^2+a^2)/ε^2 := by field_simp
  rw [regularizedReciprocal, he, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs,
    abs_of_pos hε, inv_div]
  field_simp

 theorem regularizedReciprocal_pos {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    0 < regularizedReciprocal ε a := by
  rw [regularizedReciprocal_eq hε]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg a]))

 theorem regularizedReciprocal_inv_le {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    (regularizedReciprocal ε a)⁻¹ ≤ ε+|a| := by
  rw [regularizedReciprocal_eq hε, inv_inv]
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, by
    nlinarith [sq_abs a, abs_nonneg a]⟩

 theorem weighted_young (w a b : ℝ) (hw : 0 < w) :
    a*b ≤ (w*a^2+w⁻¹*b^2)/2 := by
  have h := sq_nonneg (w*a-b)
  have hi : w*w⁻¹ = 1 := mul_inv_cancel₀ hw.ne'
  apply (mul_le_mul_iff_of_pos_left hw).mp
  nlinarith

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem energyForm_weighted_young (f g : SobolevSpace μ hQ) {ε : ℝ} (hε : 0 < ε)
    (C : ℝ≥0) (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C) :
    |energyForm μ hQ f g| ≤
      (∫ x, regularizedReciprocal ε (SobolevSpace.toLp μ hQ f x) *
        SobolevSpace.minimalSlope μ hQ f x ^ 2 ∂μ)/2 +
      (∫ x, |SobolevSpace.toLp μ hQ f x| * SobolevSpace.minimalSlope μ hQ g x ^ 2 ∂μ)/2 +
      ε * SobolevSpace.energy μ hQ g := by
  let F := SobolevSpace.toLp μ hQ f
  let Df := SobolevSpace.minimalSlope μ hQ f
  let Dg := SobolevSpace.minimalSlope μ hQ g
  have hs (v : Lp ℝ 2 μ) : Integrable (fun x => v x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Lp.memLp v).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have h1 : Integrable (fun x => regularizedReciprocal ε (F x)*Df x^2) μ := by
    apply ((hs Df).const_mul ε⁻¹).mono'
      (((regularizedReciprocal_continuous ε).comp_aestronglyMeasurable
        (Lp.aestronglyMeasurable F)).mul ((Lp.aestronglyMeasurable Df).pow 2))
    exact Eventually.of_forall fun x => by
      change |regularizedReciprocal ε (F x) * Df x^2| ≤ ε⁻¹ * Df x^2
      rw [abs_mul, abs_of_nonneg (sq_nonneg (Df x))]
      exact mul_le_mul_of_nonneg_right (regularizedReciprocal_bound hε _) (sq_nonneg _)
  have h2 : Integrable (fun x => |F x| *Dg x^2) μ := by
    apply ((hs Dg).const_mul (C : ℝ)).mono'
      ((continuous_abs.comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)).mul ((Lp.aestronglyMeasurable Dg).pow 2))
    filter_upwards [hf] with x hx
    change |(|F x| * Dg x^2)| ≤ (C : ℝ) * Dg x^2
    rw [abs_mul, abs_abs, abs_of_nonneg (sq_nonneg (Dg x))]
    exact mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  calc
    |energyForm μ hQ f g| ≤ inner ℝ Df Dg := energyForm_abs_le_slope_inner μ hQ f g
    _ = ∫ x, Df x*Dg x ∂μ := by simp only [L2.inner_def, Real.inner_apply]
    _ ≤ ∫ x, (regularizedReciprocal ε (F x)*Df x^2 + |F x| *Dg x^2 + ε*Dg x^2)/2 ∂μ := by
      apply integral_mono_ae ((Lp.memLp Df).integrable_mul (Lp.memLp Dg))
        (((h1.add h2).add ((hs Dg).const_mul ε)).div_const 2)
      exact Eventually.of_forall fun x => by
        change Df x * Dg x ≤ (regularizedReciprocal ε (F x) * Df x^2 + |F x| * Dg x^2 + ε * Dg x^2) / 2
        have hy := weighted_young (regularizedReciprocal ε (F x)) (Df x) (Dg x)
          (regularizedReciprocal_pos hε _)
        have hb := mul_le_mul_of_nonneg_right (regularizedReciprocal_inv_le hε (F x)) (sq_nonneg (Dg x))
        nlinarith
    _ = _ := by
      have h12 : Integrable (fun x => regularizedReciprocal ε (F x) * Df x^2 + |F x| * Dg x^2) μ := h1.add h2
      rw [integral_div, integral_add h12 ((hs Dg).const_mul ε),
        integral_add h1 h2, integral_const_mul]
      change _ = _
      rw [integral_sq_Lp, SobolevSpace.minimalSlope_norm_sq]
      dsimp only [F, Df]
      ring

end WeightedSlope

section WeightedScaled
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
 theorem energyForm_smul_right (c : ℝ) (f g : SobolevSpace μ hQ) :
    energyForm μ hQ f (c • g) = c * energyForm μ hQ f g := by
  rw [energyForm_comm, energyForm_smul_left, energyForm_comm μ hQ g f]

omit [ProperSpace X] in
 theorem weightedSlope_smul (w : X → ℝ) (g : SobolevSpace μ hQ) (c : ℝ) :
    (∫ x, w x * SobolevSpace.minimalSlope μ hQ (c • g) x ^ 2 ∂μ) =
      c^2 * (∫ x, w x * SobolevSpace.minimalSlope μ hQ g x ^ 2 ∂μ) := by
  rw [SobolevSpace.minimalSlope_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul |c| (SobolevSpace.minimalSlope μ hQ g)] with x hx
  rw [hx, Pi.smul_apply, smul_eq_mul, mul_pow, sq_abs]
  ring

 theorem energyForm_weighted_young_scaled (f g : SobolevSpace μ hQ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ f x| ≤ C) :
    |energyForm μ hQ f g| ≤
      δ * (∫ x, regularizedReciprocal ε (SobolevSpace.toLp μ hQ f x) *
        SobolevSpace.minimalSlope μ hQ f x ^ 2 ∂μ)/2 +
      (∫ x, |SobolevSpace.toLp μ hQ f x| * SobolevSpace.minimalSlope μ hQ g x ^ 2 ∂μ)/(2*δ) +
      ε * SobolevSpace.energy μ hQ g / δ := by
  have h := energyForm_weighted_young μ hQ f (δ⁻¹ • g) hε C hf
  rw [energyForm_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hδ),
    weightedSlope_smul, SobolevSpace.energy_smul] at h
  have hm := mul_le_mul_of_nonneg_left h hδ.le
  have he : δ * (δ⁻¹ * |energyForm μ hQ f g|) = |energyForm μ hQ f g| := by
    rw [← mul_assoc, mul_inv_cancel₀ hδ.ne', one_mul]
  rw [he] at hm
  refine hm.trans_eq ?_
  field_simp

end WeightedScaled

variable {X : Type u} [MetricSpace X]
noncomputable def radialCutoff (p : X) (R : ℝ) (x : X) : ℝ :=
  clipUnit (2 - dist p x / R)

 theorem radialCutoff_bounds (p : X) (R : ℝ) (x : X) :
    0 ≤ radialCutoff p R x ∧ radialCutoff p R x ≤ 1 := clipUnit_bounds _

 theorem radialCutoff_eq_one (p : X) {R : ℝ} (hR : 0 < R) {x : X} (hx : dist p x ≤ R) :
    radialCutoff p R x = 1 := by
  have hd : dist p x / R ≤ 1 := (div_le_one hR).mpr hx
  simp only [radialCutoff, clipUnit]
  rw [max_eq_left (by linarith), min_eq_right (by linarith)]

 theorem radialCutoff_eq_zero (p : X) {R : ℝ} (hR : 0 < R) {x : X} (hx : 2*R ≤ dist p x) :
    radialCutoff p R x = 0 := by
  have hd : 2 ≤ dist p x / R := (le_div_iff₀ hR).mpr hx
  simp only [radialCutoff, clipUnit]
  rw [max_eq_right (by linarith), min_eq_left zero_le_one]

 theorem radialCutoff_lipschitz (p : X) {R : ℝ} (hR : 0 < R) :
    LipschitzWith ⟨R⁻¹, inv_nonneg.mpr hR.le⟩ (radialCutoff p R) := by
  have h := clipUnit_lipschitz.comp
    ((lipschitzWith_const_mul_real (LipschitzWith.dist_right p) (-(R⁻¹))).add (LipschitzWith.const 2))
  have hc : (1 : ℝ≥0) * (‖-(R⁻¹)‖₊ * 1 + 0) =
      ⟨R⁻¹, inv_nonneg.mpr hR.le⟩ := by
    ext
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (inv_nonneg.mpr hR.le), mul_one, one_mul, add_zero]
    rfl
  rw [hc] at h
  convert h using 1
  funext x
  dsimp only [Function.comp_apply, radialCutoff]
  congr 1
  ring

variable [ProperSpace X]
 theorem radialCutoff_hasCompactSupport (p : X) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (radialCutoff p R) := by
  apply HasCompactSupport.intro (isCompact_closedBall p (2*R))
  intro x hx
  apply radialCutoff_eq_zero p hR
  exact (not_le.mp (by simpa only [Metric.mem_closedBall, dist_comm] using hx)).le

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (hQ : QuadraticCheegerEnergy μ)

noncomputable def SobolevSpace.ofLipschitzCompact {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (hs : HasCompactSupport g) : SobolevSpace μ hQ :=
  ⟨(hg.continuous.memLp_of_hasCompactSupport hs).toLp g, by
    change cheegerEnergy μ _ ≠ ∞
    rw [cheegerEnergy_congr_ae μ (hg.continuous.memLp_of_hasCompactSupport hs).coeFn_toLp]
    exact (cheegerEnergy_lt_top_of_lipschitz_hasCompactSupport μ hg hs).ne⟩

omit [ProperSpace X] in
 theorem SobolevSpace.ofLipschitzCompact_coe {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (hs : HasCompactSupport g) :
    ⇑(SobolevSpace.toLp μ hQ (SobolevSpace.ofLipschitzCompact μ hQ hg hs)) =ᵐ[μ] g :=
  (hg.continuous.memLp_of_hasCompactSupport hs).coeFn_toLp

 theorem SobolevSpace.ofLipschitzCompact_minimalSlope_le {g : X → ℝ} {C : ℝ≥0}
    (hg : LipschitzWith C g) (hs : HasCompactSupport g) {G : Lp ℝ 2 μ}
    (hG : IsSlopeMajorant μ g G) :
    SobolevSpace.minimalSlope μ hQ (SobolevSpace.ofLipschitzCompact μ hQ hg hs) ≤ G := by
  apply SobolevSpace.minimalSlope_le μ hQ
  exact ⟨fun _ => SobolevSpace.toLp μ hQ (SobolevSpace.ofLipschitzCompact μ hQ hg hs),
    fun _ => g, fun _ => G, fun _ => ⟨C, hg⟩,
    fun _ => SobolevSpace.ofLipschitzCompact_coe μ hQ hg hs, fun _ => hG,
    tendsto_const_nhds, tendsto_const_nhds⟩

noncomputable def radialSobolevCutoff (p : X) {R : ℝ} (hR : 0 < R) : SobolevSpace μ hQ :=
  SobolevSpace.ofLipschitzCompact μ hQ (radialCutoff_lipschitz p hR)
    (radialCutoff_hasCompactSupport p hR)

 theorem radialSobolevCutoff_coe (p : X) {R : ℝ} (hR : 0 < R) :
    ⇑(SobolevSpace.toLp μ hQ (radialSobolevCutoff μ hQ p hR)) =ᵐ[μ] radialCutoff p R :=
  SobolevSpace.ofLipschitzCompact_coe μ hQ _ _

 theorem radialSobolevCutoff_slope_le (p : X) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ (radialSobolevCutoff μ hQ p hR) x ≤
      (Metric.closedBall p (2*R)).indicator (fun _ => R⁻¹) x := by
  let s := Metric.closedBall p (2*R)
  have hs : MeasurableSet s := Metric.isClosed_closedBall.measurableSet
  have hμs : μ s ≠ ∞ := (isCompact_closedBall p (2*R)).measure_lt_top.ne
  let G := indicatorConstLp 2 hs hμs R⁻¹
  have hGc : ⇑G =ᵐ[μ] s.indicator (fun _ => R⁻¹) := indicatorConstLp_coeFn
  have hG : IsSlopeMajorant μ (radialCutoff p R) G := by
    filter_upwards [hGc] with x hx
    rw [hx]
    by_cases hxs : x ∈ s
    · rw [indicator_of_mem hxs]
      exact ⟨inv_nonneg.mpr hR.le, by
        let C : ℝ≥0 := ⟨R⁻¹, inv_nonneg.mpr hR.le⟩
        have he : ENNReal.ofReal (R⁻¹) = (C : ℝ≥0∞) :=
          @ENNReal.ofReal_coe_nnreal C
        rw [he]
        exact localSlope_le_of_lipschitz (radialCutoff_lipschitz p hR) x⟩
    · rw [indicator_of_notMem hxs]
      refine ⟨le_rfl, ?_⟩
      rw [localSlope_eq_zero_of_notMem_tsupport, ENNReal.ofReal_zero]
      intro hx'
      apply hxs
      apply closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall hx'
      by_contra hy'
      exact hy (radialCutoff_eq_zero p hR
        (not_le.mp (by simpa only [Metric.mem_closedBall, dist_comm] using hy')).le)
  have hle := SobolevSpace.ofLipschitzCompact_minimalSlope_le μ hQ
    (radialCutoff_lipschitz p hR) (radialCutoff_hasCompactSupport p hR) hG
  filter_upwards [(Lp.coeFn_le _ _).mpr hle, hGc] with x hx he
  exact hx.trans_eq he
end RegularPointCoordinates

end OAI

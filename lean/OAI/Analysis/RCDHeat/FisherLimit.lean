import Mathlib
import OAI.Analysis.RCDHeat.HeatMoments

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: FisherLimit, EntropyDissipation, RCDHeatDissipation, PositiveTail, ExponentialTail. -/



namespace RegularPointCoordinates

section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
universe u
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
section FisherLimit
omit [MeasurableSpace X] [BorelSpace X] [MetricSpace X]
noncomputable def entropyScale (k : ℕ) : ℝ := 1/((k:ℝ)+1)
 theorem entropyScale_pos (k : ℕ) : 0 < entropyScale k := by unfold entropyScale; positivity
 theorem entropyScale_antitone : Antitone entropyScale := by
  intro i j hij
  unfold entropyScale
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
 theorem entropyScale_tendsto : Tendsto entropyScale atTop (𝓝[>] (0:ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall entropyScale_pos⟩

 theorem regularizedReciprocal_antitone {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (r : ℝ) :
    regularizedReciprocal δ r ≤ regularizedReciprocal ε r := by
  rw [regularizedReciprocal_sqrt (hε.trans_le hεδ), regularizedReciprocal_sqrt hε]
  apply inv_anti₀ (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg r]))
  exact Real.sqrt_le_sqrt (by nlinarith)

 theorem regularizedReciprocal_sq_tendsto (r g : ℝ) :
    Tendsto (fun k => ENNReal.ofReal (regularizedReciprocal (entropyScale k) r*g^2))
      atTop (𝓝 (ENNReal.ofReal (g^2)/ENNReal.ofReal |r|)) := by
  have he : Tendsto entropyScale atTop (𝓝 (0:ℝ)) := entropyScale_tendsto.mono_right nhdsWithin_le_nhds
  have hs' : Tendsto (fun k => Real.sqrt (r^2+entropyScale k^2)) atTop (𝓝 (Real.sqrt (r^2))) := by
    simpa only [Function.comp_def, zero_pow (by norm_num : (2:ℕ) ≠ 0), add_zero] using
      (Real.continuous_sqrt.tendsto (r^2+(0:ℝ)^2)).comp
        (tendsto_const_nhds.add (he.pow 2))
  have hs : Tendsto (fun k => Real.sqrt (r^2+entropyScale k^2)) atTop (𝓝 |r|) := by
    rw [Real.sqrt_sq_eq_abs r] at hs'
    exact hs'
  have hh := ENNReal.Tendsto.const_div (a := ENNReal.ofReal (g^2))
    (ENNReal.tendsto_ofReal hs) (Or.inl ENNReal.ofReal_ne_top)
  convert hh using 1
  funext k
  rw [regularizedReciprocal_sqrt (entropyScale_pos k)]
  rw [show (Real.sqrt (r^2+entropyScale k^2))⁻¹*g^2 =
    g^2/Real.sqrt (r^2+entropyScale k^2) by ring]
  exact ENNReal.ofReal_div_of_pos (Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_pos (entropyScale_pos k), sq_nonneg r]))

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem regularizedFisher_integrable {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ)
    (t : ℝ) (ht : 0 < t) : Integrable (fun x => regularizedReciprocal ε (heatAt μ hQ t f x)*
      SobolevSpace.minimalSlope μ hQ (heatSobolev μ hQ t ht f) x^2) μ := by
  let u := heatAt μ hQ t f
  let D := SobolevSpace.minimalSlope μ hQ (heatSobolev μ hQ t ht f)
  have hs : Integrable (fun x => D x^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Lp.memLp D).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  apply (hs.const_mul ε⁻¹).mono'
    (((regularizedReciprocal_continuous ε).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)).mul
      ((Lp.aestronglyMeasurable D).pow 2))
  exact Eventually.of_forall fun x => by
    change |regularizedReciprocal ε (u x)*D x^2| ≤ ε⁻¹*D x^2
    rw [abs_mul, abs_of_nonneg (sq_nonneg (D x))]
    exact mul_le_mul_of_nonneg_right (regularizedReciprocal_bound hε _) (sq_nonneg _)

noncomputable def fisherInformation (f : Lp ℝ 2 μ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ k : ℕ, ENNReal.ofReal (regularizedFisher μ hQ (entropyScale_pos k) f t)

 theorem regularizedFisher_monotone (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    Monotone (fun k => regularizedFisher μ hQ (entropyScale_pos k) f t) := by
  intro i j hij
  change regularizedFisher μ hQ (entropyScale_pos i) f t ≤ regularizedFisher μ hQ (entropyScale_pos j) f t
  rw [regularizedFisher_eq_integral μ hQ (entropyScale_pos i) f t ht,
    regularizedFisher_eq_integral μ hQ (entropyScale_pos j) f t ht]
  apply integral_mono (regularizedFisher_integrable μ hQ (entropyScale_pos i) f t ht)
    (regularizedFisher_integrable μ hQ (entropyScale_pos j) f t ht)
  intro x
  exact mul_le_mul_of_nonneg_right
    (regularizedReciprocal_antitone (entropyScale_pos j) (entropyScale_antitone hij) _) (sq_nonneg _)

 theorem fisherInformation_eq_integral (f : Lp ℝ 2 μ) {t : ℝ} (ht : 0 < t) :
    fisherInformation μ hQ f t = ∫⁻ x, ENNReal.ofReal
      (SobolevSpace.minimalSlope μ hQ (heatSobolev μ hQ t ht f) x^2) /
        ENNReal.ofReal |heatAt μ hQ t f x| ∂μ := by
  let D := SobolevSpace.minimalSlope μ hQ (heatSobolev μ hQ t ht f)
  let u := heatAt μ hQ t f
  have he := lintegral_tendsto_of_tendsto_of_monotone
    (fun k => (regularizedFisher_integrable μ hQ (entropyScale_pos k) f t ht).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun x i j hij => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (regularizedReciprocal_antitone (entropyScale_pos j)
        (entropyScale_antitone hij) (u x)) (sq_nonneg (D x))))
    (Eventually.of_forall fun x => regularizedReciprocal_sq_tendsto (u x) (D x))
  have heq (k : ℕ) : (∫⁻ x, ENNReal.ofReal (regularizedReciprocal (entropyScale k) (u x)*D x^2) ∂μ) =
      ENNReal.ofReal (regularizedFisher μ hQ (entropyScale_pos k) f t) := by
    rw [regularizedFisher_eq_integral μ hQ (entropyScale_pos k) f t ht]
    exact (ofReal_integral_eq_lintegral_ofReal (regularizedFisher_integrable μ hQ (entropyScale_pos k) f t ht)
      (Eventually.of_forall fun x => mul_nonneg (regularizedReciprocal_nonneg (entropyScale_pos k) _) (sq_nonneg _))).symm
  change Tendsto (fun k => ∫⁻ x, ENNReal.ofReal (regularizedReciprocal (entropyScale k) (u x)*D x^2) ∂μ)
    atTop (𝓝 (∫⁻ x, ENNReal.ofReal (D x^2)/ENNReal.ofReal |u x| ∂μ)) at he
  simp_rw [heq] at he
  exact tendsto_nhds_unique (tendsto_atTop_iSup (fun i j hij =>
    ENNReal.ofReal_le_ofReal (regularizedFisher_monotone μ hQ f ht hij))) he
end FisherLimit

section EntropyDissipation
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem heatAt_entropy_mono_of_finite (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hAi : Integrable (heatAt μ hQ a f) μ) (hBi : Integrable (heatAt μ hQ b f) μ)
    (hAe : Integrable (fun x => heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x)) μ)
    (hBe : Integrable (fun x => heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x)) μ)
    (hm : (∫ x, heatAt μ hQ a f x ∂μ) = ∫ x, heatAt μ hQ b f x ∂μ) :
    (∫ x, heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x) ∂μ) ≤
      ∫ x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ := by
  have he := integral_normalizedEntropy_sub_tendsto μ (heatAt μ hQ a f) (heatAt μ hQ b f)
    (heatAt_nonneg μ hQ a f hf0) (heatAt_nonneg μ hQ b f hf0) hAi hBi hAe hBe hm
  have hnon : 0 ≤ (∫ x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ) -
      ∫ x, heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x) ∂μ := by
    apply ge_of_tendsto he
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact sub_nonneg.mpr (heatAt_regularizedEntropy_antitoneOn μ hQ hε f ha (ha.trans hab) hab)
  linarith

 theorem regularizedFisher_intervalIntegrable {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (regularizedFisher μ hQ hε f) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  apply (heatDissipation_continuousOn μ hQ (regularizedLog_lipschitz hε)
    (regularizedLog_zero ε) f).mono
  intro s hs
  exact ha.trans_le hs.1

 theorem heatAt_entropy_dissipation_of_finite (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hAi : Integrable (heatAt μ hQ a f) μ) (hBi : Integrable (heatAt μ hQ b f) μ)
    (hAe : Integrable (fun x => heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x)) μ)
    (hBe : Integrable (fun x => heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x)) μ)
    (hm : (∫ x, heatAt μ hQ a f x ∂μ) = ∫ x, heatAt μ hQ b f x ∂μ) :
    (∫⁻ s in Ioc a b, fisherInformation μ hQ f s) = ENNReal.ofReal
      ((∫ x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ)-
        ∫ x, heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x) ∂μ) := by
  have he := (integral_normalizedEntropy_sub_tendsto μ (heatAt μ hQ a f) (heatAt μ hQ b f)
    (heatAt_nonneg μ hQ a f hf0) (heatAt_nonneg μ hQ b f hf0) hAi hBi hAe hBe hm).comp entropyScale_tendsto
  have hmct := lintegral_tendsto_of_tendsto_of_monotone
    (μ := volume.restrict (Ioc a b))
    (fun k => (regularizedFisher_intervalIntegrable μ hQ (entropyScale_pos k) f ha hab).1.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    (show ∀ᵐ s ∂volume.restrict (Ioc a b), Monotone
      (fun k => ENNReal.ofReal (regularizedFisher μ hQ (entropyScale_pos k) f s)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact fun i j hij => ENNReal.ofReal_le_ofReal
        (regularizedFisher_monotone μ hQ f (ha.trans hs.1) hij))
    (show ∀ᵐ s ∂volume.restrict (Ioc a b), Tendsto
      (fun k => ENNReal.ofReal (regularizedFisher μ hQ (entropyScale_pos k) f s)) atTop
        (𝓝 (fisherInformation μ hQ f s)) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact tendsto_atTop_iSup (fun i j hij => ENNReal.ofReal_le_ofReal
        (regularizedFisher_monotone μ hQ f (ha.trans hs.1) hij)))
  have heq (k : ℕ) : (∫⁻ s in Ioc a b, ENNReal.ofReal (regularizedFisher μ hQ (entropyScale_pos k) f s)) =
      ENNReal.ofReal (integralPotential μ (regularizedEntropy (entropyScale k)) (heatAt μ hQ a f) -
        integralPotential μ (regularizedEntropy (entropyScale k)) (heatAt μ hQ b f)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (regularizedFisher_intervalIntegrable μ hQ (entropyScale_pos k) f ha hab).1
      (show ∀ᵐ s ∂volume.restrict (Ioc a b), 0 ≤ regularizedFisher μ hQ (entropyScale_pos k) f s from by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact regularizedFisher_nonneg μ hQ _ f s (ha.trans hs.1)),
      ← intervalIntegral.integral_of_le hab, heatAt_regularizedEntropy_dissipation μ hQ _ f a b ha hab]
  simp_rw [heq] at hmct
  exact tendsto_nhds_unique hmct (ENNReal.tendsto_ofReal he)
end EntropyDissipation

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem heatAt_entropy_dissipation (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ s in Ioc a b, fisherInformation μ hQ f s) = ENNReal.ofReal
      ((∫ x, heatAt μ hQ a f x*Real.log (heatAt μ hQ a f x) ∂μ)-
        ∫ x, heatAt μ hQ b f x*Real.log (heatAt μ hQ b f x) ∂μ) := by
  apply heatAt_entropy_dissipation_of_finite μ hQ f hf0 ha hab
    (heatAt_integrable_of_nonneg μ hQ a f hf0 hfi) (heatAt_integrable_of_nonneg μ hQ b f hf0 hfi)
    (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hf ha.le)
    (heatAt_entropy_integrable μ hQ p hA hB hvol f hf0 hf (ha.le.trans hab))
  rw [heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi ha.le,
    heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi (ha.le.trans hab)]

 theorem heatAt_fisher_time_finite (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ s in Ioc a b, fisherInformation μ hQ f s) < ∞ := by
  rw [heatAt_entropy_dissipation μ hQ p hA hB hvol f hf0 hfi hf ha hab]
  exact ENNReal.ofReal_lt_top

omit [ProperSpace X] μ hQ in
 theorem NoncollapsedRCD.heat_entropy_dissipation (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (f : Lp ℝ 2 (hausdorff n X)), 0 ≤ f →
      (∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r) →
      ∀ a b : ℝ, 0 < a → a ≤ b →
      (∫⁻ s in Ioc a b, fisherInformation (hausdorff n X) hX.quadratic f s) = ENNReal.ofReal
        ((∫ x, ((heatMeasure (hausdorff n X) hX.quadratic a f).rnDeriv (hausdorff n X) x).toReal *
          Real.log (((heatMeasure (hausdorff n X) hX.quadratic a f).rnDeriv (hausdorff n X) x).toReal)
          ∂hausdorff n X)-
        ∫ x, ((heatMeasure (hausdorff n X) hX.quadratic b f).rnDeriv (hausdorff n X) x).toReal *
          Real.log (((heatMeasure (hausdorff n X) hX.quadratic b f).rnDeriv (hausdorff n X) x).toReal)
          ∂hausdorff n X) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  intro f hf0 hfs a b ha hab
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hi := lp_integrable_of_bounded_support (hausdorff n X) f p hfr
  have h := heatAt_entropy_dissipation (hausdorff n X) hX.quadratic p hA hB hvol f hf0 hi hfr ha hab
  have he (t : ℝ) : (∫ x, ((heatMeasure (hausdorff n X) hX.quadratic t f).rnDeriv (hausdorff n X) x).toReal *
      Real.log (((heatMeasure (hausdorff n X) hX.quadratic t f).rnDeriv (hausdorff n X) x).toReal) ∂hausdorff n X) =
      ∫ x, heatAt (hausdorff n X) hX.quadratic t f x*Real.log (heatAt (hausdorff n X) hX.quadratic t f x) ∂hausdorff n X := by
    apply integral_congr_ae
    filter_upwards [heatMeasure_rnDeriv (hausdorff n X) hX.quadratic t f hf0] with x hx
    rw [hx]
  rw [he a, he b]
  exact h

end

 
section
open Set Metric Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X]
 
noncomputable def positiveTail (p : X) (a δ : ℝ) (f : X → ℝ) (x : X) : ℝ :=
  f x+δ*Real.exp (-a*dist p x)
 theorem positiveTail_pos (p : X) (a : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) (x : X) : 0 < positiveTail p a δ f x := by
  exact add_pos_of_nonneg_of_pos (hf x) (mul_pos hδ (Real.exp_pos _))
 theorem exp_neg_dist_lipschitz (p : X) {a : ℝ} (ha : 0 ≤ a) :
    LipschitzWith ⟨a,ha⟩ (fun x => Real.exp (-a*dist p x)) := by
  have he : LipschitzOnWith 1 Real.exp (Iic 0) := by
    apply (convex_Iic 0).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    intro x hx
    change |Real.exp x| ≤ 1
    rw [abs_of_pos (Real.exp_pos _)]
    simpa using Real.exp_le_exp.mpr hx
  have hl := lipschitzWith_const_mul_real (LipschitzWith.dist_right p) (-a)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hy : -a*dist p y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) dist_nonneg
  have hx : -a*dist p x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) dist_nonneg
  have h := he.dist_le_mul (-a*dist p x) hx (-a*dist p y) hy
  simp only [NNReal.coe_one,one_mul] at h
  apply h.trans
  change dist (-a*dist p x) (-a*dist p y) ≤ a*dist x y
  simpa only [NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,abs_neg,abs_of_nonneg ha,
    NNReal.coe_one,mul_one] using hl.dist_le_mul x y
 theorem positiveTail_lipschitz (p : X) {a : ℝ} (ha : 0 ≤ a) (δ : ℝ)
    {f : X → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    LipschitzWith (C+‖δ‖₊*⟨a,ha⟩) (positiveTail p a δ f) :=
  hf.add (lipschitzWith_const_mul_real (exp_neg_dist_lipschitz p ha) δ)
 theorem lipschitz_log_one_add {f : X → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (h0 : ∀ x, 0 ≤ f x) :
    LipschitzWith C (fun x => Real.log (1+f x)) := by
  have hl : LipschitzOnWith 1 Real.log (Ici 1) := by
    apply (convex_Ici 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hx))).hasDerivWithinAt)
    intro x hx
    change |x⁻¹| ≤ 1
    rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hx))]
    exact inv_le_one_of_one_le₀ hx
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : 1 ≤ 1+f x := le_add_of_nonneg_right (h0 x)
  have hy : 1 ≤ 1+f y := le_add_of_nonneg_right (h0 y)
  have h := hl.dist_le_mul (1+f x) hx (1+f y) hy
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,add_sub_add_left_eq_sub] at h
  exact h.trans (by simpa only [Real.dist_eq] using hf.dist_le_mul x y)

 

 theorem positiveTail_log_lipschitz (p : X) {a δ R : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ)
    {f : X → ℝ} {C M : ℝ≥0} (hf : LipschitzWith C f)
    (h0 : ∀ x, 0 ≤ f x) (hb : ∀ x, |f x| ≤ M)
    (hs : ∀ x, f x ≠ 0 → dist p x ≤ R) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x => Real.log (positiveTail p a δ f x)) := by
  let w := radialWeight p a R
  have hw := radialWeight_lipschitz p ha R
  have hm : ∀ x, |w x| ≤ (⟨Real.exp (a*R),(Real.exp_pos _).le⟩ : ℝ≥0) :=
    radialWeight_bound p ha R
  have hp := lipschitzWith_mul_of_support_bound hf hw hb (fun x _ => hm x)
  have hq := lipschitzWith_const_mul_real hp δ⁻¹
  have hq0 (x : X) : 0 ≤ δ⁻¹*(f x*w x) :=
    mul_nonneg (inv_nonneg.mpr hδ.le) (mul_nonneg (h0 x) (radialWeight_nonneg p a R x))
  have hg := lipschitz_log_one_add hq hq0
  have hd := lipschitzWith_const_mul_real (LipschitzWith.dist_right p) (-a)
  obtain ⟨L,hL⟩ : ∃ L : ℝ≥0, LipschitzWith L
      (fun x => Real.log (1+δ⁻¹*(f x*w x))+Real.log δ-a*dist p x) := by
    refine ⟨‖δ⁻¹‖₊*(M*⟨a*Real.exp (a*R),mul_nonneg ha (Real.exp_pos _).le⟩+
      ⟨Real.exp (a*R),(Real.exp_pos _).le⟩*C)+‖-a‖₊*1,?_⟩
    have hgc := hg.add (LipschitzWith.const (Real.log δ))
    simpa only [add_zero,Pi.add_apply,neg_mul,sub_eq_add_neg] using hgc.add hd
  refine ⟨L,?_⟩
  convert hL using 1
  funext x
  have hwx : f x*w x = f x*Real.exp (a*dist p x) := by
    by_cases hx : f x = 0
    · simp only [hx,zero_mul]
    · simp only [w,radialWeight,min_eq_left (hs x hx)]
  rw [hwx]
  have heq : positiveTail p a δ f x =
      (1+δ⁻¹*(f x*Real.exp (a*dist p x)))*(δ*Real.exp (-a*dist p x)) := by
    dsimp [positiveTail]
    rw [neg_mul,Real.exp_neg]
    field_simp
    ring
  have hfirst : 1+δ⁻¹*(f x*Real.exp (a*dist p x)) ≠ 0 := by
    exact ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (inv_nonneg.mpr hδ.le) (mul_nonneg (h0 x) (Real.exp_pos _).le)))
  rw [heq,Real.log_mul hfirst (mul_ne_zero hδ.ne' (Real.exp_ne_zero _)),Real.log_mul hδ.ne' (Real.exp_ne_zero _),Real.log_exp]
  ring
end

 
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
variable {X : Type*} [MetricSpace X]
 theorem localSlope_exp_neg_dist (p : X) {b : ℝ} (hb : 0 ≤ b) (x : X) :
    localSlope (fun y => Real.exp (-b*dist p y)) x ≤ ENNReal.ofReal (b*Real.exp (-b*dist p x)) := by
  have hl := lipschitzWith_const_mul_real (LipschitzWith.dist_right p) (-b)
  have hc := localSlope_comp_hasDerivAt (f := fun y : X => -b*dist p y) (x := x) (Real.hasDerivAt_exp (-b*dist p x))
    hl.continuous.continuousAt (ne_top_of_le_ne_top ENNReal.coe_ne_top (localSlope_le_of_lipschitz hl x))
  simp only [Function.comp_def,abs_of_pos (Real.exp_pos _)] at hc
  have hd : localSlope (fun y => -b*dist p y) x ≤ ENNReal.ofReal b := by
    have h := localSlope_le_of_lipschitz hl x
    simpa only [NNReal.coe_mul,ENNReal.coe_mul,ENNReal.coe_one,mul_one,← ENNReal.ofReal_coe_nnreal,
      coe_nnnorm,Real.norm_eq_abs,abs_neg,abs_of_nonneg hb] using h
  exact hc.trans ((mul_le_mul' le_rfl hd).trans_eq (by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,mul_comm]))

variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
 theorem exp_neg_dist_memLp_two (p : X) (b : ℝ)
    (hi : Integrable (fun x => Real.exp (-(2*b)*dist p x)) μ) :
    MemLp (fun x => Real.exp (-b*dist p x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.dist continuous_id))).aestronglyMeasurable)).mpr
  convert hi using 1
  funext x
  change Real.exp (-b*dist p x)^2 = Real.exp (-(2*b)*dist p x)
  rw [← Real.exp_nat_mul]
  congr 1
  ring
 theorem exp_neg_dist_slopeMajorant (p : X) {b : ℝ} (hb : 0 ≤ b)
    (hi : Integrable (fun x => Real.exp (-(2*b)*dist p x)) μ) :
    IsSlopeMajorant μ (fun x => Real.exp (-b*dist p x))
      (b • (exp_neg_dist_memLp_two μ p b hi).toLp _) := by
  filter_upwards [Lp.coeFn_smul b ((exp_neg_dist_memLp_two μ p b hi).toLp _),
    (exp_neg_dist_memLp_two μ p b hi).coeFn_toLp] with x hx he
  simp only [Pi.smul_apply,smul_eq_mul] at hx
  rw [hx,he]
  exact ⟨mul_nonneg hb (Real.exp_pos _).le,localSlope_exp_neg_dist p hb x⟩

variable [ProperSpace X] [IsFiniteMeasureOnCompacts μ]
 theorem integrable_dist_pow_mul_exp_of_le (p : X) {A B b : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (k : ℕ) (hb : B+(k:ℝ)+1 ≤ b) :
    Integrable (fun x => dist p x^k*Real.exp (-b*dist p x)) μ := by
  apply (integrable_dist_pow_mul_exp μ p hA hB hvol k).mono'
    ((((continuous_const.dist continuous_id).pow k).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_const.dist continuous_id)))).aestronglyMeasurable)
  filter_upwards with x
  change ‖dist p x^k*Real.exp (-b*dist p x)‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg dist_nonneg _) (Real.exp_pos _).le)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg dist_nonneg _)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hb) dist_nonneg

end RegularPointCoordinates

end OAI

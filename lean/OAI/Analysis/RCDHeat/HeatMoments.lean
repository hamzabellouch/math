import Mathlib
import OAI.Analysis.RCDHeat.WeightedHilbert

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: HeatMoments, HeatEntropy, HeatLaw, EntropyNormalization, EntropyLimit. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology NNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
section HeatMoments
omit [MeasurableSpace X] [BorelSpace X] [MetricSpace X]
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular]
  (hQ : QuadraticCheegerEnergy μ)

 theorem heatAt_exponential_square_integrable (f : Lp ℝ 2 μ) (p : X)
    {r : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    {a : ℝ} (ha : 0 ≤ a) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => Real.exp (a*dist p x)*heatAt μ hQ t f x^2) μ := by
  have hs : AEStronglyMeasurable (fun x => Real.exp (a*dist p x)*heatAt μ hQ t f x^2) μ :=
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.dist continuous_id))).aestronglyMeasurable).mul
      ((Lp.aestronglyMeasurable _).pow 2)
  apply (lintegral_ofReal_ne_top_iff_integrable hs
    (Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))).mp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (heatAt_exponential_square_lintegral_le μ hQ f p hf ha ht)

 theorem exponential_moment_young (a d z : ℝ) (k : ℕ) :
    |d^k*z| ≤ Real.exp (a*d)*z^2 + d^(2*k)*Real.exp (-a*d) := by
  have he : Real.exp (a*d/2)*Real.exp (-a*d/2) = 1 := by
    rw [← Real.exp_add, show a*d/2 + -a*d/2 = 0 by ring, Real.exp_zero]
  have he1 : (Real.exp (a*d/2))^2 = Real.exp (a*d) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have he2 : (Real.exp (-a*d/2))^2 = Real.exp (-a*d) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have hs := sq_nonneg (Real.exp (a*d/2)*|z| - Real.exp (-a*d/2)*|d^k|)
  have he3 : (d^k)^2 = d^(2*k) := by rw [← pow_mul]; congr 1; omega
  rw [sub_sq, mul_pow, mul_pow, he1, he2, sq_abs, sq_abs, he3] at hs
  have he4 : Real.exp (a*d/2)*|z| *(Real.exp (-a*d/2)*|d^k|) = |d^k*z| := by
    rw [abs_mul]
    calc
      _ = (Real.exp (a*d/2)*Real.exp (-a*d/2))*(|z| *|d^k|) := by ring
      _ = _ := by rw [he, one_mul, mul_comm]
  have he5 : 2*(Real.exp (a*d/2)*|z|)*(Real.exp (-a*d/2)*|d^k|) = 2*|d^k*z| := by
    rw [mul_assoc, he4]
  rw [he5] at hs
  nlinarith [abs_nonneg (d^k*z)]

 theorem heatAt_dist_pow_integrable (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) {r : ℝ} (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r)
    (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => dist p x^k*heatAt μ hQ t f x) μ := by
  let a := B+(2*k:ℕ)+1
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hi := (heatAt_exponential_square_integrable μ hQ f p hf ha ht).add
    (integrable_dist_pow_mul_exp μ p hA hB hvol (2*k))
  apply hi.mono' (((continuous_const.dist continuous_id).pow k).aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable _))
  exact Eventually.of_forall fun x => exponential_moment_young a (dist p x) (heatAt μ hQ t f x) k

 theorem heatAt_finiteSecondMoment (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    FiniteSecondMoment (μ.withDensity (fun x => ENNReal.ofReal (heatAt μ hQ t f x))) := by
  refine ⟨p, ?_⟩
  have hmd : Measurable (fun x : X => ENNReal.ofReal (dist x p)^2) :=
    (continuous_id.dist continuous_const).measurable.ennreal_ofReal.pow_const 2
  rw [lintegral_withDensity_eq_lintegral_mul₀
    (Lp.aestronglyMeasurable (heatAt μ hQ t f)).aemeasurable.ennreal_ofReal
    hmd.aemeasurable]
  have hi := heatAt_dist_pow_integrable μ hQ p hA hB hvol f hf 2 ht
  have hn := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0)
  have hnn : 0 ≤ᵐ[μ] (fun x => dist p x^2*heatAt μ hQ t f x) :=
    hn.mono fun x hx => mul_nonneg (sq_nonneg _) hx
  have he : (fun x => ENNReal.ofReal (heatAt μ hQ t f x)*ENNReal.ofReal (dist x p)^2) =ᵐ[μ]
      (fun x => ENNReal.ofReal (dist p x^2*heatAt μ hQ t f x)) := by
    filter_upwards with x
    rw [mul_comm, dist_comm, ← ENNReal.ofReal_pow dist_nonneg, ← ENNReal.ofReal_mul (sq_nonneg _)]
  change (∫⁻ x, ENNReal.ofReal (heatAt μ hQ t f x) * ENNReal.ofReal (dist x p)^2 ∂μ) < ∞
  rw [lintegral_congr_ae he]
  exact lt_top_iff_ne_top.mpr ((lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable hnn).mpr hi)
end HeatMoments

section HeatEntropy
 theorem entropy_radial_lower {r : ℝ} (hr : 0 ≤ r) (b : ℝ) :
    -Real.exp (-b)-b*r ≤ r*Real.log r := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp only [mul_zero, zero_mul, sub_zero]
    exact neg_nonpos.mpr (Real.exp_pos _).le
  have h := mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (mul_nonneg hr.le (Real.exp_pos b).le)) (Real.exp_pos (-b)).le
  rw [Real.log_mul hr.ne' (Real.exp_pos b).ne', Real.log_exp] at h
  have he : Real.exp (-b)*Real.exp b = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have he1 : Real.exp (-b)*(r*Real.exp b-1) = r-Real.exp (-b) := by
    calc
      _ = r*(Real.exp (-b)*Real.exp b)-Real.exp (-b) := by ring
      _ = _ := by rw [he, mul_one]
  have he2 : Real.exp (-b)*(r*Real.exp b*(Real.log r+b)) = r*(Real.log r+b) := by
    calc
      _ = (Real.exp (-b)*Real.exp b)*(r*(Real.log r+b)) := by ring
      _ = _ := by rw [he, one_mul]
  rw [he1, he2] at h
  nlinarith

 theorem entropy_radial_abs_bound {r b : ℝ} (hr : 0 ≤ r) (hb : 0 ≤ b) :
    |r*Real.log r| ≤ r^2+b*r+Real.exp (-b) := by
  have hl := entropy_radial_lower hr b
  have hu := mul_le_mul_of_nonneg_left (Real.log_le_self hr) hr
  apply abs_le.mpr
  constructor
  · nlinarith [sq_nonneg r]
  · nlinarith [mul_nonneg hb hr, (Real.exp_pos (-b)).le]

variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem heatAt_entropy_integrable (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x => heatAt μ hQ t f x*Real.log (heatAt μ hQ t f x)) μ := by
  let u := heatAt μ hQ t f
  have hs : Integrable (fun x => u x^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Lp.memLp u).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hm := (heatAt_dist_pow_integrable μ hQ p hA hB hvol f hf 1 ht).const_mul (B+1)
  have he := integrable_exp_neg_dist_of_volume μ p hA hB (by linarith : B < B+1) hvol
  have hmeas : AEStronglyMeasurable (fun x => u x*Real.log (u x)) μ :=
    Real.continuous_mul_log.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)
  apply ((hs.add hm).add he).mono' hmeas
  filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0)] with x hx
  have hbound := entropy_radial_abs_bound hx (mul_nonneg (by linarith : 0 ≤ B+1) (dist_nonneg (x := p) (y := x)))
  simpa only [Real.norm_eq_abs, pow_one, mul_assoc, neg_mul, Pi.add_apply, u] using hbound

noncomputable def heatMeasure (t : ℝ) (f : Lp ℝ 2 μ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (heatAt μ hQ t f x))

 theorem heatMeasure_absolutelyContinuous (t : ℝ) (f : Lp ℝ 2 μ) :
    heatMeasure μ hQ t f ≪ μ := withDensity_absolutelyContinuous _ _

variable [SigmaFinite μ]
 theorem heatMeasure_probability (p : X) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvol : ∀ R : ℝ, 1 ≤ R → μ.real (Metric.closedBall p (2*R)) ≤ A*Real.exp (B*R))
    (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hfi : Integrable f μ)
    (hfm : ∫ x, f x ∂μ = 1) {t : ℝ} (ht : 0 ≤ t) :
    IsProbabilityMeasure (heatMeasure μ hQ t f) := by
  constructor
  rw [heatMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (heatAt_integrable_of_nonneg μ hQ t f hf0 hfi)
      ((Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0)),
    heatAt_integral_eq_of_exponential_volume μ hQ p hA hB hvol f hf0 hfi ht, hfm, ENNReal.ofReal_one]

 theorem heatMeasure_rnDeriv (t : ℝ) (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f) :
    (fun x => ((heatMeasure μ hQ t f).rnDeriv μ x).toReal) =ᵐ[μ] heatAt μ hQ t f := by
  have he := Measure.rnDeriv_withDensity₀ μ (Lp.aestronglyMeasurable (heatAt μ hQ t f)).aemeasurable.ennreal_ofReal
  filter_upwards [he, (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ t f hf0)] with x hx hn
  change ((μ.withDensity _).rnDeriv μ x).toReal = _
  rw [hx, ENNReal.toReal_ofReal hn]

end HeatEntropy

section HeatLaw
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [BorelSpace X] in
 theorem lp_integrable_of_bounded_support [ProperSpace X] (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] (f : Lp ℝ 2 μ) (p : X) {r : ℝ}
    (hf : ∀ᵐ x ∂μ, f x ≠ 0 → dist p x ≤ r) : Integrable f μ := by
  apply IntegrableOn.integrable_of_ae_notMem_eq_zero
    (lp_integrableOn_of_finite μ f (Metric.closedBall p r) (isCompact_closedBall p r).measure_ne_top)
  filter_upwards [hf] with x hx hn
  by_contra hz
  apply hn
  simpa only [Metric.mem_closedBall, dist_comm] using hx hz

 theorem NoncollapsedRCD.heat_law (K : ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (p : X) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) :=
      locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ (f : Lp ℝ 2 (hausdorff n X)), 0 ≤ f →
      (∃ r : ℝ, ∀ᵐ x ∂hausdorff n X, f x ≠ 0 → dist p x ≤ r) →
      (∫ x, f x ∂hausdorff n X) = 1 → ∀ t : ℝ, 0 ≤ t →
      IsProbabilityMeasure (heatMeasure (hausdorff n X) hX.quadratic t f) ∧
      (heatMeasure (hausdorff n X) hX.quadratic t f ≪ hausdorff n X) ∧
      FiniteSecondMoment (heatMeasure (hausdorff n X) hX.quadratic t f) ∧
      Integrable (fun x => ((heatMeasure (hausdorff n X) hX.quadratic t f).rnDeriv
        (hausdorff n X) x).toReal * Real.log (((heatMeasure (hausdorff n X) hX.quadratic t f).rnDeriv
        (hausdorff n X) x).toReal)) (hausdorff n X) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure (hausdorff n X) :=
    locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
  intro f hf0 hfs hfm t ht
  obtain ⟨r,hfr⟩ := hfs
  obtain ⟨A,B,hA,hB,hvol⟩ := hX.exponential_volume K n hn p
  have hi := lp_integrable_of_bounded_support (hausdorff n X) f p hfr
  refine ⟨heatMeasure_probability _ hX.quadratic p hA hB hvol f hf0 hi hfm ht,
    heatMeasure_absolutelyContinuous _ hX.quadratic t f,
    heatAt_finiteSecondMoment _ hX.quadratic p hA hB hvol f hf0 hfr ht, ?_⟩
  apply (heatAt_entropy_integrable _ hX.quadratic p hA hB hvol f hf0 hfr ht).congr
  filter_upwards [heatMeasure_rnDeriv _ hX.quadratic t f hf0] with x hx
  rw [hx]
end HeatLaw

section EntropyNormalization

 theorem regularizedReciprocal_sqrt {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    regularizedReciprocal ε r = (Real.sqrt (r^2+ε^2))⁻¹ := by
  have he : 1+(r/ε)^2 = (r^2+ε^2)/ε^2 := by field_simp; ring
  rw [regularizedReciprocal, he, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs,
    abs_of_pos hε, inv_div, div_eq_mul_inv]
  field_simp

 theorem regularizedEntropy_formula {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    regularizedEntropy ε r = r*regularizedLog ε r - Real.sqrt (r^2+ε^2)+ε := by
  let F := fun r : ℝ => r*regularizedLog ε r-Real.sqrt (r^2+ε^2)+ε
  have hD (r : ℝ) : HasDerivAt F (regularizedLog ε r) r := by
    have hp : r^2+ε^2 ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg r) (sq_pos_of_pos hε)).ne'
    have hs : Real.sqrt (r^2+ε^2) ≠ 0 := (Real.sqrt_pos.mpr (lt_of_le_of_ne
      (add_nonneg (sq_nonneg r) (sq_nonneg ε)) hp.symm)).ne'
    have h := (((hasDerivAt_id r).mul (regularizedLog_hasDerivAt ε r)).sub
      ((((hasDerivAt_id r).pow 2).add_const (ε^2)).sqrt hp)).add_const ε
    rw [regularizedReciprocal_sqrt hε] at h
    convert! h using 1
    simp only [id_eq, Pi.pow_apply, Nat.reduceSub, pow_one, mul_one, one_mul]
    field_simp
    ring
  have he' := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := r) (fun s (_ : s ∈ uIcc 0 r) => hD s)
    ((regularizedLog_continuous ε).intervalIntegrable 0 r)
  simpa only [regularizedEntropy, F, zero_mul, zero_pow (by norm_num : (2:ℕ) ≠ 0),
    zero_add, Real.sqrt_sq_eq_abs, abs_of_pos hε, zero_sub, neg_add_cancel, sub_zero] using he'

noncomputable def normalizedEntropy (ε r : ℝ) : ℝ :=
  regularizedEntropy ε r - r*Real.log (2/ε)+r

 theorem normalizedEntropy_zero (ε : ℝ) : normalizedEntropy ε 0 = 0 := by
  rw [normalizedEntropy, regularizedEntropy_zero, zero_mul, sub_zero, add_zero]

 theorem normalizedEntropy_formula {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 ≤ r) :
    normalizedEntropy ε r = r*Real.log ((r+Real.sqrt (r^2+ε^2))/2) -
      Real.sqrt (r^2+ε^2)+ε+r := by
  have hp : 0 < r^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg r) (sq_pos_of_pos hε)
  have hs : 0 < r+Real.sqrt (r^2+ε^2) := add_pos_of_nonneg_of_pos hr (Real.sqrt_pos.mpr hp)
  have hsq : Real.sqrt (1+(r/ε)^2) = Real.sqrt (r^2+ε^2)/ε := by
    rw [show 1+(r/ε)^2 = (r^2+ε^2)/ε^2 by field_simp; ring,
      Real.sqrt_div hp.le, Real.sqrt_sq_eq_abs, abs_of_pos hε]
  rw [normalizedEntropy, regularizedEntropy_formula hε, regularizedLog, Real.arsinh,
    hsq, ← add_div, Real.log_div hs.ne' hε.ne', Real.log_div (by norm_num : (2:ℝ) ≠ 0) hε.ne',
    Real.log_div hs.ne' (by norm_num : (2:ℝ) ≠ 0)]
  ring

 theorem entropy_le_normalizedEntropy {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) :
    r*Real.log r ≤ normalizedEntropy ε r := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp only [normalizedEntropy_zero, zero_mul, le_refl]
  have hs : r ≤ Real.sqrt (r^2+ε^2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ε])
  have hu : Real.sqrt (r^2+ε^2) ≤ r+ε :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hh : r ≤ (r+Real.sqrt (r^2+ε^2))/2 := by linarith
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_log hr hh) hr.le
  rw [normalizedEntropy_formula hε hr.le]
  linarith

 theorem normalizedEntropy_le_sq_add {ε r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : 0 ≤ r) : normalizedEntropy ε r ≤ r^2+r := by
  have hs : ε ≤ Real.sqrt (r^2+ε^2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])
  have hu : Real.sqrt (r^2+ε^2) ≤ r+ε :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hp : 0 < (r+Real.sqrt (r^2+ε^2))/2 := by linarith
  have hh : (r+Real.sqrt (r^2+ε^2))/2 ≤ r+1 := by linarith
  have hlog : Real.log (r+1) ≤ r := by
    simpa only [add_sub_cancel_right] using (Real.log_le_sub_one_of_pos (by positivity : 0 < r+1))
  have hl := (Real.log_le_log hp hh).trans hlog
  have hm := mul_le_mul_of_nonneg_left hl hr
  rw [normalizedEntropy_formula hε hr]
  nlinarith

 theorem normalizedEntropy_abs_bound {ε r : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hr : 0 ≤ r) : |normalizedEntropy ε r| ≤ |r*Real.log r|+r^2+r := by
  have hl := entropy_le_normalizedEntropy hε hr
  have hu := normalizedEntropy_le_sq_add hε hε1 hr
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (r*Real.log r), sq_nonneg r]
  · linarith [abs_nonneg (r*Real.log r)]

 theorem normalizedEntropy_tendsto {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun ε => normalizedEntropy ε r) (𝓝[>] (0:ℝ)) (𝓝 (r*Real.log r)) := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp only [normalizedEntropy_zero, zero_mul]
    exact tendsto_const_nhds
  have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hs' := (Real.continuous_sqrt.tendsto (r^2+(0:ℝ)^2)).comp
    (tendsto_const_nhds.add (hi.pow 2))
  have hs : Tendsto (fun ε : ℝ => Real.sqrt (r^2+ε^2)) (𝓝[>] 0) (𝓝 r) := by
    simpa only [Function.comp_def, zero_pow (by norm_num : (2:ℕ) ≠ 0), add_zero,
      Real.sqrt_sq hr.le] using hs'
  have hb : Tendsto (fun ε : ℝ => (r+Real.sqrt (r^2+ε^2))/2) (𝓝[>] 0) (𝓝 r) := by
    convert (tendsto_const_nhds.add hs).div_const 2 using 1; ring_nf
  have hl := ((Real.continuousAt_log hr.ne').tendsto.comp hb).const_mul r
  have h := ((hl.sub hs).add hi).add_const r
  apply Tendsto.congr' _ (show Tendsto (fun ε : ℝ =>
    r*Real.log ((r+Real.sqrt (r^2+ε^2))/2)-Real.sqrt (r^2+ε^2)+ε+r)
      (𝓝[>] 0) (𝓝 (r*Real.log r)) from by simpa only [Function.comp_def, add_zero, sub_add_cancel] using h)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (normalizedEntropy_formula hε hr.le).symm

end EntropyNormalization

 theorem normalizedEntropy_continuous (ε : ℝ) : Continuous (normalizedEntropy ε) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  exact ((regularizedEntropy_hasDerivAt ε r).continuousAt.sub
    (continuousAt_id.mul continuousAt_const)).add continuousAt_id

variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

 theorem normalizedEntropy_integrable {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ)
    (hfi : Integrable f μ) : Integrable (fun x => normalizedEntropy ε (f x)) μ := by
  exact ((integralPotential_integrable μ (regularizedEntropy_hasDerivAt ε)
    (regularizedEntropy_zero ε) (regularizedLog_lipschitz hε) (regularizedLog_zero ε) f).sub
    (hfi.mul_const (Real.log (2/ε)))).add hfi

 theorem integral_normalizedEntropy {ε : ℝ} (hε : 0 < ε) (f : Lp ℝ 2 μ)
    (hfi : Integrable f μ) :
    (∫ x, normalizedEntropy ε (f x) ∂μ) = integralPotential μ (regularizedEntropy ε) f -
      (∫ x, f x ∂μ)*Real.log (2/ε) + ∫ x, f x ∂μ := by
  have hi := integralPotential_integrable μ (regularizedEntropy_hasDerivAt ε)
    (regularizedEntropy_zero ε) (regularizedLog_lipschitz hε) (regularizedLog_zero ε) f
  have hsub : Integrable (fun x => regularizedEntropy ε (f x)-f x*Real.log (2/ε)) μ :=
    hi.sub (hfi.mul_const _)
  rw [show (fun x => normalizedEntropy ε (f x)) =
    (fun x => regularizedEntropy ε (f x)-f x*Real.log (2/ε)+f x) from rfl,
    integral_add hsub hfi, integral_sub hi (hfi.mul_const (Real.log (2/ε))),
    integral_mul_const]
  rfl

 theorem integral_normalizedEntropy_tendsto (f : Lp ℝ 2 μ) (hf0 : 0 ≤ f)
    (hfi : Integrable f μ) (hfe : Integrable (fun x => f x*Real.log (f x)) μ) :
    Tendsto (fun ε => ∫ x, normalizedEntropy ε (f x) ∂μ) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x, f x*Real.log (f x) ∂μ)) := by
  have hs : Integrable (fun x => f x^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => |f x*Real.log (f x)|+f x^2+f x)
    (Eventually.of_forall fun ε => (normalizedEntropy_continuous ε).comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable f)) ?_ ((hfe.abs.add hs).add hfi) ?_
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))] with ε hε hε1
    filter_upwards [(Lp.coeFn_nonneg _).mpr hf0] with x hx
    exact normalizedEntropy_abs_bound hε (le_of_lt hε1) hx
  · filter_upwards [(Lp.coeFn_nonneg _).mpr hf0] with x hx
    exact normalizedEntropy_tendsto hx

 theorem integral_normalizedEntropy_sub_tendsto (f g : Lp ℝ 2 μ) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfe : Integrable (fun x => f x*Real.log (f x)) μ)
    (hge : Integrable (fun x => g x*Real.log (g x)) μ)
    (hm : ∫ x, f x ∂μ = ∫ x, g x ∂μ) :
    Tendsto (fun ε => integralPotential μ (regularizedEntropy ε) f -
      integralPotential μ (regularizedEntropy ε) g) (𝓝[>] (0:ℝ))
      (𝓝 ((∫ x, f x*Real.log (f x) ∂μ)-(∫ x, g x*Real.log (g x) ∂μ))) := by
  apply Tendsto.congr' _ ((integral_normalizedEntropy_tendsto μ f hf0 hfi hfe).sub
    (integral_normalizedEntropy_tendsto μ g hg0 hgi hge))
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [integral_normalizedEntropy μ hε f hfi, integral_normalizedEntropy μ hε g hgi, hm]
  ring
end RegularPointCoordinates

end OAI

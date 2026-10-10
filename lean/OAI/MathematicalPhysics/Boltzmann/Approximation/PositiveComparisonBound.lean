import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedEntropyProduction
import OAI.MathematicalPhysics.Boltzmann.Branching.LinearCharacteristicBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongPairMoment
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace OAI

section

/-! # Exact entropy dissipation for positive bounded cutoff densities -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

def positiveCutoffProduction (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : ℝ :=
  (1/4:ℝ)*collisionJump (fun p => Real.log (f p/maxwellian p.2)) z*
    (truncatedPostRate b f z-truncatedPreRate b f z)

omit [MeasurableSpace X] in
theorem positiveCutoffProduction_nonneg (b : ℝ) (f : X × Velocity → ℝ)
    (hf : ∀ p, 0 < f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ positiveCutoffProduction b f z := by
  have h := mul_nonneg (by norm_num : (0:ℝ) ≤ 1/4) (relative_entropy_production_nonneg b f hf z)
  simpa only [positiveCutoffProduction,mul_assoc] using h

theorem cutoff_relative_entropy_identity {μ : Measure X} [SFinite μ] (b : ℝ)
    (f : X × Velocity → ℝ)
    (hpre : Integrable (fun z => Real.log (f (z.1.1,z.1.2.1)/maxwellian z.1.2.1)*
      truncatedPreRate b f z) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => Real.log (f (z.1.1,z.1.2.1)/maxwellian z.1.2.1)*
      truncatedPostRate b f z) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ p, Real.log (f p/maxwellian p.2)*KineticCollisionNullSets.gain b f p ∂μ.prod volume)-
      (∫ p, Real.log (f p/maxwellian p.2)*cutoffLossDensity b f p ∂μ.prod volume) =
      -(∫ z, positiveCutoffProduction b f z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hp := (collision_test_marginal (truncatedPostRate b f)
    (fun p => Real.log (f p/maxwellian p.2)) hpost).2
  have hl := (collision_test_marginal (truncatedPreRate b f)
    (fun p => Real.log (f p/maxwellian p.2)) hpre).2
  simp only [← cutoffGain_eq_marginal] at hp
  simp only [← cutoffLoss_eq_marginal] at hl
  rw [hp,hl,cutoff_production_identity b f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost]
  simp only [positiveCutoffProduction,mul_assoc,integral_const_mul]
  ring

theorem bounded_positive_entropy_identity (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A δ b : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hδ : 0 < δ) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hfl : ∀ p, δ*Real.exp (-2*‖p.2‖^2) ≤ f p) (hfb : ∀ p, f p ≤ A*H q p.2) :
    Integrable (positiveCutoffProduction b f)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    (∫ p, Real.log (f p/maxwellian p.2)*collisionSource b f p ∂μ.prod volume) =
      -(∫ z, positiveCutoffProduction b f z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hfn : ∀ p, 0 ≤ f p := fun p => (mul_pos hδ (Real.exp_pos _)).le.trans (hfl p)
  have hpair := bounded_pair_integrable (μ := μ) hq₂ hA hfm hfn hfb
  have hgL := bounded_log_gainLoss_integrable (μ := μ) hcarleman hq₁ hq₂ hA hA hδ hb hfm hfm hfn hfb hfl hfb
  have hlog : Measurable (fun p : X × Velocity => Real.log (f p/maxwellian p.2)) := by
    have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
    exact (hfm.div hm).log
  have hS : MeasurableSet {z : (X × (Velocity × Velocity)) × Sphere | ‖z.1.2.1-z.1.2.2‖ < b} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hprei := (preRate_integrable hfm hfn hpair).indicator hS
  have hposti := (postRate_integrable hfm hfn hpair).indicator hS
  have hpren : ∀ z, 0 ≤ truncatedPreRate b f z := fun z =>
    Set.indicator_nonneg (fun z _ => preRate_nonneg hfn z) z
  have hpostn : ∀ z, 0 ≤ truncatedPostRate b f z := fun z =>
    Set.indicator_nonneg (fun z _ => preRate_nonneg hfn (scatterTriple z)) z
  have hpre := collision_test_integrable_of_marginal (truncatedPreRate_measurable hfm b)
    hpren hprei hlog (by simpa only [← cutoffLoss_eq_marginal] using hgL.2)
  have hpost := collision_test_integrable_of_marginal (truncatedPostRate_measurable hfm b)
    hpostn hposti hlog (by simpa only [← cutoffGain_eq_marginal] using hgL.1)
  obtain ⟨hjpre,hjpost⟩ := collisionJump_integrable b f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost
  constructor
  · convert (hjpost.sub hjpre).const_mul (1/4:ℝ) using 1
    funext z
    simp only [positiveCutoffProduction,Pi.sub_apply]
    ring
  · have hloss := cutoff_loss_ae_eq_frequency hfm hfn hpair b
    have hLi : Integrable (fun p => Real.log (f p/maxwellian p.2)*
        (f p*KineticCollisionNullSets.frequency b f p)) (μ.prod volume) := by
      apply hgL.2.congr
      filter_upwards [hloss] with p hp
      rw [hp]
    calc
      _ = (∫ p, Real.log (f p/maxwellian p.2)*KineticCollisionNullSets.gain b f p ∂μ.prod volume)-
          (∫ p, Real.log (f p/maxwellian p.2)*cutoffLossDensity b f p ∂μ.prod volume) := by
        simp_rw [collisionSource,mul_sub]
        rw [integral_sub hgL.1 hLi]
        congr 1
        apply integral_congr_ae
        filter_upwards [hloss] with p hp
        rw [hp]
      _ = _ := cutoff_relative_entropy_identity b f hpre hpost

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Uniform integrability upgrades positive-difference convergence to strong L1 convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
open TransportPrimitive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem positiveDifference_L1 {u v : ℕ → X → ℝ}
    (hum : ∀ n, Measurable (u n)) (hvm : ∀ n, Measurable (v n))
    (hu : ∀ n x, 0 ≤ u n x) (hv : ∀ n x, 0 ≤ v n x)
    (hui : UniformIntegrable u 1 μ) (hvi : UniformIntegrable v 1 μ)
    (hd : Tendsto (fun n => eLpNorm (fun x => positiveDifference (u n x) (v n x)) 1 μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => u n x-v n x) 1 μ) atTop (𝓝 0) := by
  have hclip (K : ℝ) (hK : 0 ≤ K) :
      Tendsto (fun n => eLpNorm (fun x => min (u n x) K-min (v n x) K) 1 μ) atTop (𝓝 0) := by
    have hmul := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (1+2*K)) hd
      (Or.inr ENNReal.ofReal_ne_top)
    simp only [mul_zero] at hmul
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul (fun _ => zero_le)
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (((hum n).min measurable_const).sub ((hvm n).min measurable_const)).aestronglyMeasurable
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using
        min_difference_le_positiveDifference (hu n x) (hv n x) hK)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε4 : 0 < ε/4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨C,hC⟩ := uniform_min_truncation hum hu hui hε4
  obtain ⟨D,hD⟩ := uniform_min_truncation hvm hv hvi hε4
  let K : ℝ := max (C:ℝ) (D:ℝ)
  have hK : 0 ≤ K := C.coe_nonneg.trans (le_max_left _ _)
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hclip K hK) (ε/4) hε4] with n hn
  have he : (fun x => u n x-v n x) =
      (fun x => u n x-min (u n x) K)+
      (fun x => min (u n x) K-min (v n x) K)+
      (fun x => min (v n x) K-v n x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [he]
  calc
    _ ≤ (eLpNorm (fun x => u n x-min (u n x) K) 1 μ+
        eLpNorm (fun x => min (u n x) K-min (v n x) K) 1 μ)+
        eLpNorm (fun x => min (v n x) K-v n x) 1 μ :=
      (eLpNorm_add_le (by norm_num)).trans
        (add_le_add (eLpNorm_add_le (by norm_num)) le_rfl)
    _ ≤ (ε/4+ε/4)+ε/4 := by
      apply add_le_add (add_le_add (hC K (le_max_left _ _) n) hn)
      change eLpNorm ((fun x => min (v n x) K)-v n) 1 μ ≤ _
      rw [eLpNorm_sub_comm]
      exact hD K (le_max_right _ _) n
    _ ≤ ε := by
      calc
        (ε/4+ε/4)+ε/4 ≤ (ε/4+ε/4)+(ε/4+ε/4) := add_le_add le_rfl le_self_add
        _ = 4*(ε/4) := by ring
        _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Absolute continuity and evolution of the bounded positive-path difference -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem inv_lipschitzOn_one : LipschitzOnWith 1 (fun x : ℝ => x⁻¹) (Ici 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have he : x⁻¹-y⁻¹ = (y-x)/(x*y) := by field_simp
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  rw [he,abs_div,abs_of_pos (mul_pos hx0 hy0),abs_sub_comm y x]
  apply (div_le_iff₀ (mul_pos hx0 hy0)).mpr
  have hxy : 1 ≤ x*y := by simpa only [one_mul] using mul_le_mul hx hy (by norm_num) hx0.le
  nlinarith [abs_nonneg (x-y)]

theorem positiveDifference_absolutelyContinuous {T : ℝ} (hT : 0 ≤ T) {u v : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 T) (hv : AbsolutelyContinuousOnInterval v 0 T)
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc 0 T, 0 ≤ v t) :
    AbsolutelyContinuousOnInterval (fun t => positiveDifference (u t) (v t)) 0 T := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1:ℝ)) 0 T :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hd : AbsolutelyContinuousOnInterval (fun t => 1+u t+v t) 0 T := (hc.add hu).add hv
  have hi := inv_lipschitzOn_one.comp_absolutelyContinuousOnInterval
    (fun t ht => by
      have hmem : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
      change 1 ≤ 1+u t+v t
      linarith [hu0 t hmem,hv0 t hmem]) hd
  exact (hu.sub hv).mul hi

theorem positiveDifference_hasDerivAt {u v : ℝ → ℝ} {du dv t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) (hu0 : 0 ≤ u t) (hv0 : 0 ≤ v t) :
    HasDerivAt (fun s => positiveDifference (u s) (v s))
      (((du-dv)*(1+u t+v t)-(u t-v t)*(du+dv))/(1+u t+v t)^2) t := by
  exact (hu.sub hv).div ((hu.const_add 1).add hv) (by positivity)

theorem positiveDifference_evolution {u v : ℝ → ℝ} {a b k l e f t : ℝ}
    (hu : HasDerivAt u (a-k*u t+e) t) (hv : HasDerivAt v (b-l*v t+f) t)
    (hu0 : 0 ≤ u t) (hv0 : 0 ≤ v t) :
    HasDerivAt (fun s => positiveDifference (u s) (v s))
      (positiveDifferenceForcing (u t) (v t) a b k l e f-
        positiveDifferenceDamping (u t) (v t) a b k l e f*positiveDifference (u t) (v t)) t := by
  have h := positiveDifference_hasDerivAt hu hv hu0 hv0
  rwa [positiveDifference_derivative_identity hu0 hv0] at h

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Stability in a bounded metric for positive characteristic profiles -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem positiveDifference_stability {T : ℝ} (hT : 0 ≤ T)
    {u v a b k l e f : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 T) (hv : AbsolutelyContinuousOnInterval v 0 T)
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc 0 T, 0 ≤ v t)
    (ha : ∀ t ∈ Icc 0 T, 0 ≤ a t) (hb : ∀ t ∈ Icc 0 T, 0 ≤ b t)
    (hk0 : ∀ t ∈ Icc 0 T, 0 ≤ k t) (hl0 : ∀ t ∈ Icc 0 T, 0 ≤ l t)
    (he0 : ∀ t ∈ Icc 0 T, 0 ≤ e t) (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hdi : IntervalIntegrable
      (fun t => positiveDifferenceDamping (u t) (v t) (a t) (b t) (k t) (l t) (e t) (f t)) volume 0 T)
    (hri : IntervalIntegrable
      (fun t => positiveDifferenceForcing (u t) (v t) (a t) (b t) (k t) (l t) (e t) (f t)) volume 0 T)
    (hdu : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt u (a t-k t*u t+e t) t)
    (hdv : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt v (b t-l t*v t+f t) t) :
    |positiveDifference (u T) (v T)| ≤ |positiveDifference (u 0) (v 0)|+
      ∫ t in 0..T, |positiveDifferenceForcing (u t) (v t) (a t) (b t) (k t) (l t) (e t) (f t)| := by
  have hw := positiveDifference_absolutelyContinuous hT hu hv hu0 hv0
  apply damped_path_abs_le hT hw hdi hri
  · intro t ht
    exact positiveDifference_damping_nonneg (hu0 t ht) (hv0 t ht) (ha t ht) (hb t ht)
      (hk0 t ht) (hl0 t ht) (he0 t ht) (hf0 t ht)
  · filter_upwards [hdu,hdv] with t htu htv ht
    exact positiveDifference_evolution (htu ht) (htv ht) (hu0 t ht) (hv0 t ht)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Integrability of the exact bounded positive-comparison equation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem positiveComparison_integrable {T : ℝ} (hT : 0 ≤ T)
    {u v a b k l e f : ℝ → ℝ}
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc 0 T, 0 ≤ v t)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hl : IntervalIntegrable l volume 0 T)
    (he : IntervalIntegrable e volume 0 T) (hf : IntervalIntegrable f volume 0 T) :
    IntervalIntegrable (fun t =>
      positiveDifferenceDamping (u t) (v t) (a t) (b t) (k t) (l t) (e t) (f t)) volume 0 T ∧
    IntervalIntegrable (fun t =>
      positiveDifferenceForcing (u t) (v t) (a t) (b t) (k t) (l t) (e t) (f t)) volume 0 T := by
  have hd0 t (ht : t ∈ Icc 0 T) : 1+u t+v t ≠ 0 := by
    have := hu0 t ht
    have := hv0 t ht
    positivity
  have hc : ContinuousOn (fun t => (1+u t+v t)⁻¹) (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    exact ((continuousOn_const.add hu).add hv).inv₀ hd0
  have hq : ContinuousOn (fun t => (u t+v t+4*u t*v t)/(2*(1+u t+v t)^2))
      (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    apply ((hu.add hv).add ((continuousOn_const.mul hu).mul hv)).div
      (continuousOn_const.mul (((continuousOn_const.add hu).add hv).pow 2))
    intro t ht
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (hd0 t ht))
  constructor
  · have h := (((ha.add hb).add he).add hf |>.add ((hk.add hl).div_const 2)).mul_continuousOn hc
    convert h using 1
    funext t
    exact div_eq_mul_inv _ _
  · have h := (((ha.sub hb).add he).sub hf).mul_continuousOn hc
    have h' := (hl.sub hk).mul_continuousOn hq
    convert h.add h' using 1
    funext t
    unfold positiveDifferenceForcing
    ring

theorem positiveComparison_error_integrable {T : ℝ} (hT : 0 ≤ T)
    {u v a b k l e f : ℝ → ℝ}
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc 0 T, 0 ≤ v t)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hl : IntervalIntegrable l volume 0 T)
    (he : IntervalIntegrable e volume 0 T) (hf : IntervalIntegrable f volume 0 T) :
    IntervalIntegrable (fun t => |a t-b t|/(1+u t+v t)+e t/(1+u t)+f t/(1+v t)+|k t-l t|)
      volume 0 T := by
  have hdu t (ht : t ∈ Icc 0 T) : 1+u t ≠ 0 := by have := hu0 t ht; positivity
  have hdv t (ht : t ∈ Icc 0 T) : 1+v t ≠ 0 := by have := hv0 t ht; positivity
  have hd t (ht : t ∈ Icc 0 T) : 1+u t+v t ≠ 0 := by
    have := hu0 t ht
    have := hv0 t ht
    positivity
  have cu : ContinuousOn (fun t => (1+u t)⁻¹) (uIcc 0 T) := by
    rw [uIcc_of_le hT]; exact (continuousOn_const.add hu).inv₀ hdu
  have cv : ContinuousOn (fun t => (1+v t)⁻¹) (uIcc 0 T) := by
    rw [uIcc_of_le hT]; exact (continuousOn_const.add hv).inv₀ hdv
  have cd : ContinuousOn (fun t => (1+u t+v t)⁻¹) (uIcc 0 T) := by
    rw [uIcc_of_le hT]; exact ((continuousOn_const.add hu).add hv).inv₀ hd
  have h := ((((ha.sub hb).abs.mul_continuousOn cd).add
    (he.mul_continuousOn cu)).add (hf.mul_continuousOn cv)).add (hk.sub hl).abs
  simpa only [div_eq_mul_inv] using h

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # A positive-path stability bound using only the physical source discrepancies -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem positiveDifference_error_bound {T : ℝ} (hT : 0 ≤ T)
    {u v a b k l e f : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 T) (hv : AbsolutelyContinuousOnInterval v 0 T)
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc 0 T, 0 ≤ v t)
    (ha0 : ∀ t ∈ Icc 0 T, 0 ≤ a t) (hb0 : ∀ t ∈ Icc 0 T, 0 ≤ b t)
    (hk0 : ∀ t ∈ Icc 0 T, 0 ≤ k t) (hl0 : ∀ t ∈ Icc 0 T, 0 ≤ l t)
    (he0 : ∀ t ∈ Icc 0 T, 0 ≤ e t) (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hl : IntervalIntegrable l volume 0 T)
    (he : IntervalIntegrable e volume 0 T) (hf : IntervalIntegrable f volume 0 T)
    (hdu : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt u (a t-k t*u t+e t) t)
    (hdv : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt v (b t-l t*v t+f t) t) :
    |positiveDifference (u T) (v T)| ≤ |positiveDifference (u 0) (v 0)|+
      ∫ t in 0..T, |a t-b t|/(1+u t+v t)+e t/(1+u t)+f t/(1+v t)+|k t-l t| := by
  have huc : ContinuousOn u (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using hu.continuousOn
  have hvc : ContinuousOn v (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using hv.continuousOn
  obtain ⟨hdi,hri⟩ := positiveComparison_integrable hT huc hvc hu0 hv0 ha hb hk hl he hf
  have h := positiveDifference_stability hT hu hv hu0 hv0 ha0 hb0 hk0 hl0 he0 hf0 hdi hri hdu hdv
  apply h.trans
  apply add_le_add le_rfl
  apply intervalIntegral.integral_mono_on hT hri.abs
    (positiveComparison_error_integrable hT huc hvc hu0 hv0 ha hb hk hl he hf)
  intro t ht
  exact positiveDifference_forcing_bound (hu0 t ht) (hv0 t ht) (he0 t ht) (hf0 t ht)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI

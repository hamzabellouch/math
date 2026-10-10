import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.SlopeApprox
import OAI.Geometry.WeakHessian.Transport.HopfObjective

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X]

def ascendingSlope (f : X → ℝ) (x : X) : ℝ≥0∞ :=
  limsup (fun y => ENNReal.ofReal ((f y-f x)/dist y x)) (𝓝[≠] x)
def ascendingSlopeApprox (f : X → ℝ) (n : ℕ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist y x < 1/(n+1:ℝ)), ENNReal.ofReal ((f y-f x)/dist y x)

lemma ascendingSlope_eq_iInf (f : X → ℝ) (x : X) :
    ascendingSlope f x = ⨅ n : ℕ, ascendingSlopeApprox f n x := by
  rw [ascendingSlope,nhdsWithin,
    ((Metric.nhds_basis_ball_inv_nat_succ (x := x)).inf_principal ({x}ᶜ)).limsup_eq_iInf_iSup]
  simp only [iInf_true]
  apply iInf_congr
  intro n
  apply le_antisymm
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact le_iSup_of_le y (le_iSup_of_le hy.1 le_rfl)
  · apply iSup_le
    intro y
    apply iSup_le
    intro hy
    by_cases he : y = x
    · simp [he]
    · exact le_iSup_of_le y (le_iSup_of_le ⟨hy,he⟩ le_rfl)

lemma ascendingSlopeApprox_le {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (n : ℕ) (x : X) :
    ascendingSlopeApprox f n x ≤ L := by
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  calc
    ENNReal.ofReal ((f y-f x)/dist y x) ≤ ENNReal.ofReal (|f y-f x|/dist y x) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_abs_self _) dist_nonneg)
    _ ≤ slopeApprox f n x := le_iSup_of_le y (le_iSup_of_le hy le_rfl)
    _ ≤ L := slopeApprox_le_lipschitz hf n x

lemma ascendingSlope_le {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (x : X) :
    ascendingSlope f x ≤ L := by
  rw [ascendingSlope_eq_iInf]
  exact (iInf_le _ 0).trans (ascendingSlopeApprox_le hf 0 x)

lemma lowerSemicontinuous_ascendingSlopeApprox {f : X → ℝ} (hf : Continuous f) (n : ℕ) :
    LowerSemicontinuous (ascendingSlopeApprox f n) := by
  intro x a ha
  obtain ⟨y,hy⟩ := lt_iSup_iff.mp ha
  obtain ⟨hy,hay⟩ := lt_iSup_iff.mp hy
  have hyx : y ≠ x := by intro he; simp [he] at hay
  have hd : ContinuousAt (fun z => dist y z) x := (continuous_const.dist continuous_id).continuousAt
  have hq : ContinuousAt (fun z => ENNReal.ofReal ((f y-f z)/dist y z)) x :=
    ENNReal.continuous_ofReal.continuousAt.comp
      ((continuous_const.sub hf).continuousAt.div hd (dist_ne_zero.mpr hyx))
  filter_upwards [hd.eventually_lt continuousAt_const hy,
    continuousAt_const.eventually_lt hq hay] with z hz hqz
  exact hqz.trans_le (le_iSup_of_le y (le_iSup_of_le hz le_rfl))

lemma measurable_ascendingSlope [MeasurableSpace X] [BorelSpace X]
    {f : X → ℝ} (hf : Continuous f) : Measurable (ascendingSlope f) := by
  simp_rw [show ascendingSlope f = fun x => ⨅ n,ascendingSlopeApprox f n x from
    funext (ascendingSlope_eq_iInf f)]
  exact Measurable.iInf fun n => (lowerSemicontinuous_ascendingSlopeApprox hf n).measurable

lemma ascending_quotient_limsup_le {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) (n : ℕ) :
    limsup (fun s => ENNReal.ofReal ((f (evalReal γ s)-f (evalReal γ t))/|s-t|)) (𝓝[≠] t) ≤
      ascendingSlopeApprox f n (evalReal γ t)*metricSpeed γ t := by
  have hγc : Continuous (evalReal γ) := continuous_evalReal.comp (continuous_const.prodMk continuous_id)
  have hn : ∀ᶠ s in 𝓝 t, dist (evalReal γ s) (evalReal γ t) < 1/(n+1:ℝ) := by
    apply (hγc.dist continuous_const).continuousAt.eventually_lt continuousAt_const
    simp only [dist_self]
    positivity
  calc
    _ ≤ limsup (fun s => ascendingSlopeApprox f n (evalReal γ t)*ENNReal.ofReal
        (dist (evalReal γ s) (evalReal γ t)/|s-t|)) (𝓝[≠] t) := by
      refine limsup_le_limsup ?_
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with s hs
      by_cases he : evalReal γ s = evalReal γ t
      · simp [he]
      have hdne := dist_ne_zero.mpr he
      have hid : (f (evalReal γ s)-f (evalReal γ t))/|s-t| =
          ((f (evalReal γ s)-f (evalReal γ t))/dist (evalReal γ s) (evalReal γ t))*
            (dist (evalReal γ s) (evalReal γ t)/|s-t|) := by field_simp
      rw [hid,ENNReal.ofReal_mul' (div_nonneg dist_nonneg (abs_nonneg _))]
      apply mul_le_mul_left
      exact le_iSup_of_le (evalReal γ s) (le_iSup_of_le hs le_rfl)
    _ = _ := ENNReal.limsup_const_mul_of_ne_top
       (ne_top_of_le_ne_top ENNReal.coe_ne_top (ascendingSlopeApprox_le hf n _))

lemma deriv_comp_le_ascendingSlopeApprox {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) (n : ℕ) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      ascendingSlopeApprox f n (evalReal γ t)*metricSpeed γ t := by
  by_cases hd : DifferentiableAt ℝ (fun s => f (evalReal γ s)) t
  · let u := fun s => f (evalReal γ s)
    change DifferentiableAt ℝ u t at hd
    have Hd : Tendsto (fun s => (u s-u t)/(s-t)) (𝓝[≠] t) (𝓝 (deriv u t)) := by
      simpa only [slope_fun_def_field] using
        hasDerivAt_iff_tendsto_slope.mp hd.hasDerivAt
    have hrle : 𝓝[>] t ≤ 𝓝[≠] t := nhdsWithin_mono _ (fun s hs => ne_of_gt hs)
    have hlle : 𝓝[<] t ≤ 𝓝[≠] t := nhdsWithin_mono _ (fun s hs => ne_of_lt hs)
    have Hr : Tendsto (fun s => ENNReal.ofReal ((u s-u t)/|s-t|))
        (𝓝[>] t) (𝓝 (ENNReal.ofReal (deriv u t))) := by
      apply (ENNReal.tendsto_ofReal (Hd.mono_left hrle)).congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [abs_of_pos (sub_pos.mpr hs)]
    have Hl : Tendsto (fun s => ENNReal.ofReal ((u s-u t)/|s-t|))
        (𝓝[<] t) (𝓝 (ENNReal.ofReal (-deriv u t))) := by
      apply (ENNReal.tendsto_ofReal (Hd.mono_left hlle).neg).congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [abs_of_neg (sub_neg.mpr hs),div_neg]
    have HR : ENNReal.ofReal (deriv u t) ≤ _ :=
      Hr.limsup_eq.symm.le.trans (limsup_le_limsup_of_le hrle)
    have HL : ENNReal.ofReal (-deriv u t) ≤ _ :=
      Hl.limsup_eq.symm.le.trans (limsup_le_limsup_of_le hlle)
    have HH := ascending_quotient_limsup_le hf γ t n
    rcases le_total 0 (deriv u t) with h | h
    · rw [abs_of_nonneg h]
      exact HR.trans HH
    · rw [abs_of_nonpos h]
      exact HL.trans HH
  · simp only [deriv_zero_of_not_differentiableAt hd,abs_zero,ENNReal.ofReal_zero]
    exact bot_le
lemma deriv_comp_le_ascendingSlope {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (γ : Curve X) (t : ℝ) (hspeed : metricSpeed γ t ≠ ∞) :
    ENNReal.ofReal |deriv (fun s => f (evalReal γ s)) t| ≤
      ascendingSlope f (evalReal γ t) * metricSpeed γ t := by
  rw [ascendingSlope_eq_iInf, ENNReal.iInf_mul (fun h => (hspeed h).elim)]
  exact le_iInf fun n => deriv_comp_le_ascendingSlopeApprox hf γ t n

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma ascendingSlope_isLocalWeakUpperGradient (hfinite : FiniteOnBoundedSets m)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    IsLocalWeakUpperGradient m f (fun x => (ascendingSlope f x).toReal) := by
  have hm : Measurable (fun x => (ascendingSlope f x).toReal) :=
    (measurable_ascendingSlope hf.continuous).ennreal_toReal
  have hbound : ∀ x, ‖(ascendingSlope f x).toReal‖ ≤ (L : ℝ) := by
    intro x
    rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.coe_ne_top (ascendingSlope_le hf x)).trans_eq
      (ENNReal.coe_toReal L)
  have hsl : ∀ x, ascendingSlope f x ≠ ∞ := fun x =>
    ne_top_of_le_ne_top ENNReal.coe_ne_top (ascendingSlope_le hf x)
  refine ⟨?_, ae_of_all m fun _ => ENNReal.toReal_nonneg, ?_⟩
  · intro o R _hR
    let : IsFiniteMeasure (m.restrict (Metric.ball o R)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using
        hfinite (Metric.ball o R) Metric.isBounded_ball⟩
    exact MemLp.of_bound hm.aestronglyMeasurable (L : ℝ) (ae_of_all _ hbound)
  · intro π hπ _hb
    let : IsProbabilityMeasure π := hπ.1
    have hsm : Measurable (fun p : Curve X × ℝ => metricSpeed p.1 p.2 ^ 2) :=
      measurable_metricSpeed.pow_const 2
    have hfin := ae_lt_top hsm.lintegral_prod_right hπ.2.2.2.ne
    apply lintegral_mono_ae
    filter_upwards [hπ.2.2.1, hfin] with γ hγ hfinγ
    have hfiniteSpeed : ∀ᵐ t ∂volume.restrict (Set.Icc (0 : ℝ) 1), metricSpeed γ t ≠ ∞ := by
      have hh := ae_lt_top (hsm.comp measurable_prodMk_left) hfinγ.ne
      filter_upwards [hh] with t ht
      exact fun heq => by simp [heq] at ht
    have hac := lipschitz_comp_absolutelyContinuous hf hγ.absolutelyContinuous
    calc
      ENNReal.ofReal |f (γ timeOne) - f (γ timeZero)| =
          ‖∫ t in Set.Icc (0 : ℝ) 1, deriv (fun s => f (evalReal γ s)) t‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le zero_le_one, hac.integral_deriv_eq_sub]
        simp [evalReal, clampTime, timeOne, timeZero]
        rfl
      _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖deriv (fun s => f (evalReal γ s)) t‖ₑ :=
        enorm_integral_le_lintegral_enorm _
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [hfiniteSpeed] with t ht
        simpa only [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_toReal (hsl _)]
          using deriv_comp_le_ascendingSlope hf γ t ht

lemma weakGradient_le_ascendingSlope (hfinite : FiniteOnBoundedSets m)
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) :
    ∀ᵐ x ∂m, weakGradient m u x ≤ (ascendingSlope u x).toReal := by
  by_cases h : ∃ D, IsMinimalLocalWeakUpperGradient m u D
  · exact (weakGradient_isMinimal h).2 _ (ascendingSlope_isLocalWeakUpperGradient hfinite hu)
  · simp only [weakGradient,dite_eq_right h,Pi.zero_apply]
    exact ae_of_all m fun _ => ENNReal.toReal_nonneg

omit [MeasurableSpace X] [BorelSpace X] in
lemma ascendingSlope_le_of_quadratic_increment {u : X → ℝ} {x : X} {a b : ℝ}
    (hu : ∀ z, u z-u x ≤ a*dist z x+b*dist z x^2) :
    ascendingSlope u x ≤ ENNReal.ofReal a := by
  rcases eq_or_ne (𝓝[≠] x) ⊥ with h | h
  · simp [ascendingSlope,h]
  have : NeBot (𝓝[≠] x) := ⟨h⟩
  have H : Tendsto (fun z => ENNReal.ofReal (a+b*dist z x)) (𝓝[≠] x)
      (𝓝 (ENNReal.ofReal a)) := by
    apply ENNReal.tendsto_ofReal
    have hc : Continuous (fun z : X => a+b*dist z x) := by fun_prop
    simpa using hc.continuousAt.tendsto.mono_left (show 𝓝[≠] x ≤ 𝓝 x from nhdsWithin_le_nhds)
  calc
    ascendingSlope u x ≤ limsup (fun z => ENNReal.ofReal (a+b*dist z x)) (𝓝[≠] x) := by
      refine limsup_le_limsup ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      apply ENNReal.ofReal_le_ofReal
      apply (div_le_iff₀ (dist_pos.mpr hz)).mpr
      nlinarith [hu z]
    _ = _ := H.limsup_eq

omit [MeasurableSpace X] [BorelSpace X] in
lemma ascendingSlope_hopf_contact {f : X → ℝ} {B t : ℝ}
    (hlower : ∀ y, B ≤ f y) (ht : 0 < t) {x y : X}
    (hy : WeakHessianTransport.hopfObjective f t x y = WeakHessianTransport.hopfLax f t x) :
    ascendingSlope (WeakHessianTransport.hopfLax f t) x ≤ ENNReal.ofReal (dist x y/t) := by
  apply ascendingSlope_le_of_quadratic_increment (b := 1/(2*t))
  intro z
  simpa only [one_div,mul_comm (_⁻¹),← div_eq_mul_inv] using
    WeakHessianTransport.hopf_spatial_increment hlower ht hy z

omit [MeasurableSpace X] [BorelSpace X] in

lemma ascendingSlope_contact {φ ψ : X → ℝ} (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2)
    {x y : X} (hcontact : φ x+ψ y = dist x y^2/2) :
    ascendingSlope φ x ≤ ENNReal.ofReal (dist x y) := by
  apply ascendingSlope_le_of_quadratic_increment (b := 1/2)
  intro z
  have H := hdual z y
  have hd : dist z y^2 ≤ (dist z x+dist x y)^2 :=
    (sq_le_sq₀ dist_nonneg (by positivity)).mpr (dist_triangle z x y)
  nlinarith

omit [MeasurableSpace X] [BorelSpace X] in

lemma contact_geodesic_decrease {φ ψ : X → ℝ}
    (hdual : ∀ x y, φ x+ψ y ≤ dist x y^2/2) {γ : Curve X} (hγ : IsGeodesic γ)
    (hcontact : φ (γ timeZero)+ψ (γ timeOne) = dist (γ timeZero) (γ timeOne)^2/2)
    (t : Time) :
    t.val*(1-t.val/2)*dist (γ timeZero) (γ timeOne)^2 ≤ φ (γ timeZero)-φ (γ t) := by
  have H := hdual (γ t) (γ timeOne)
  have hd := hγ t timeOne
  have ht := t.property.2
  change dist (γ t) (γ timeOne) = |t.val - 1| * dist (γ timeZero) (γ timeOne) at hd
  rw [abs_of_nonpos (sub_nonpos.mpr ht)] at hd
  rw [hd] at H
  nlinarith

end WeakHessian

end
end InlinedFile0

end OAI

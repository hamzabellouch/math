import OAI.Geometry.IsometricImmersion.Pulses.PulseFlowDistance
import OAI.Geometry.IsometricImmersion.Pulses.PulseNeighborhood
import OAI.Geometry.IsometricImmersion.Metrics.MetricLocality

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation

theorem exists_sectionFour_radius {M L : ℝ} (hM : 0 ≤ M) (hL : 0 < L) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      M*(r+107*(L*r)/100) ≤ 9/(100*L) := by
  let A := M*(1+107*L/100)
  let alpha := 9/(100*L)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have ha : 0 < alpha := by dsimp only [alpha]; positivity
  let r := min (1/40 : ℝ) (min (1/(20*L)) (alpha/(2*(A+1))))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hr1 : r ≤ 1/40 := min_le_left _ _
  have hr2 : r ≤ 1/(20*L) := (min_le_right _ _).trans (min_le_left _ _)
  have hr3 : r ≤ alpha/(2*(A+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hr2' := (le_div_iff₀ (by positivity : 0 < 20*L)).mp hr2
  have hr3' := (le_div_iff₀ (by positivity : 0 < 2*(A+1))).mp hr3
  refine ⟨r,hr,by linarith,by nlinarith,?_⟩
  have he : M*(r+107*(L*r)/100) = A*r := by dsimp only [A]; ring
  rw [he]
  change A*r ≤ alpha
  nlinarith

theorem pulse_width_eventually {r : ℝ} (hr : 0 < r) (delta : ℝ) :
    ∀ᶠ tau : ℝ in atTop, 1 ≤ tau ∧ delta/(2*tau) ≤ r/4 := by
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun tau : ℝ => tau⁻¹) atTop (𝓝 0))
  have hw : Tendsto (fun tau : ℝ => delta/(2*tau)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_left_comm,mul_comm] using hi.const_mul (delta/2)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hw.eventually_lt tendsto_const_nhds (show (0 : ℝ) < r/4 by linarith)] with tau ht hwidth
  exact ⟨ht,hwidth.le⟩

theorem pulseOriginalBox_coordinate_bounds {q0 a delta tau : ℝ} {p : Coord}
    (hp : p ∈ pulseOriginalBox q0 a delta tau) :
    |p 0| ≤ a ∧ |p 1+q0*p 0| ≤ delta/(2*tau) := by
  obtain ⟨v,hv,rfl⟩ := hp
  have hx : |v 0| ≤ a := abs_le.mpr
    ⟨by simpa [pulseLocalBox] using hv.1 0,by simpa [pulseLocalBox] using hv.2 0⟩
  have hy : |v 1| ≤ delta/(2*tau) := abs_le.mpr
    ⟨by simpa [pulseLocalBox] using hv.1 1,by simpa [pulseLocalBox] using hv.2 1⟩
  constructor
  · simpa [inverseShearCoordinates] using hx
  · have he : (inverseShearCoordinates q0 v) 1+q0*(inverseShearCoordinates q0 v) 0 = v 1 := by
      simp [inverseShearCoordinates]
    simpa only [he] using hy

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem pulseBox_seed_abs_lt_half
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L r a delta tau : ℝ} (hM : 0 ≤ M) (hL : 0 < L) (hr : 0 < r)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : L*r < 2) (ha : a ≤ L*r)
    (hrsmall : M*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hwidth : delta/(2*tau) ≤ r/4)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hpulse : capChart Y p ∈ pulseOriginalBox q0 a delta tau) :
    |p 1| < r/2 := by
  obtain ⟨hx,htheta⟩ := pulseOriginalBox_coordinate_bounds hpulse
  have htime : p 0 ∈ Icc (-(L*r)) (L*r) := by
    apply abs_le.mp
    exact (by simpa only [capChart_zero] using hx : |p 0| ≤ a).trans ha
  have htheta' : |Y (p 1) (p 0)+q0*p 0| ≤ delta/(2*tau) := by
    simpa only [capChart_one,capChart_zero,capFlowHeight] using htheta
  have hthetaR : |Y (p 1) (p 0)+q0*p 0| ≤ r := htheta'.trans (hwidth.trans (by linarith))
  have hclose := flow_segment_quotient_near_center hq hU hSU hY hrange hstart hode
    hsmall hM hL hpartial hq0 hcenter (mul_pos hL hr) hT hp.2 htime hthetaR hrsmall
  have hdist := actual_shear_seed_distance hq hU hSU hY hrange hstart hode
    (mul_pos hL hr) hT hp.2 htime hclose
  have htimeAbs : |p 0| ≤ L*r := abs_le.mpr htime
  have hdist' : |Y (p 1) (p 0)+q0*p 0-p 1| ≤ r/10 := by
    have he : (1/(10*L))*(L*r) = r/10 := by
      field_simp [hL.ne']
    exact hdist.trans ((mul_le_mul_of_nonneg_left htimeAbs (by positivity)).trans_eq he)
  have hsabs : |p 1| ≤ |Y (p 1) (p 0)+q0*p 0-p 1|+|Y (p 1) (p 0)+q0*p 0| := by
    calc
      |p 1| = |(Y (p 1) (p 0)+q0*p 0)-(Y (p 1) (p 0)+q0*p 0-p 1)| := by congr 1; ring
      _ ≤ |Y (p 1) (p 0)+q0*p 0|+|Y (p 1) (p 0)+q0*p 0-p 1| := abs_sub _ _
      _ = _ := add_comm _ _
  linarith

theorem pulseTensor_not_tsupport_exterior_seed
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L r a delta tau : ℝ} (hM : 0 ≤ M) (hL : 0 < L) (hr : 0 < r)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : L*r < 2) (ha : 0 < a) (haL : a ≤ L*r)
    (hrsmall : M*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hd : 0 < delta) (ht : 0 < tau) (hwidth : delta/(2*tau) ≤ r/4)
    (N : ℕ) {p : Coord} (hp : p ∈ capChartDomain) (hseed : r/2 ≤ |p 1|) :
    capChart Y p ∉ tsupport (pulseTensor q0 a N delta tau) := by
  intro hin
  have hbox := pulseTensor_tsupport_subset ha hd ht N hin
  exact (not_lt_of_ge hseed) (pulseBox_seed_abs_lt_half hq hU hSU hY hrange hstart hode
    hsmall hM hL hr hpartial hq0 hcenter hT haL hrsmall hwidth hp hbox)

theorem testMetric_eventuallyEq_on_lower_cap
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    {M q0 L r a delta tau : ℝ} (hM : 0 ≤ M) (hL : 0 < L) (hr : 0 < r)
    (hpartial : ∀ p ∈ modelSquare, ∀ i : Fin 2, |coordPartial i q p| ≤ M)
    (hq0 : |q0| ≤ 1/20) (hcenter : |q 0-q0| ≤ 1/(100*L))
    (hT : L*r < 2) (ha : 0 < a) (haL : a ≤ L*r)
    (hrsmall : M*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hd : 0 < delta) (ht : 0 < tau) (hwidth : delta/(2*tau) ≤ r/4)
    (gStar : MetricField) (N : ℕ) (R : LowerCapRectangle (-r/2))
    {p : Coord} (hp : p ∈ R.image Y) :
    testMetric gStar q0 a N delta tau =ᶠ[𝓝 p] gStar := by
  obtain ⟨v,hv,rfl⟩ := hp
  have hseed : r/2 ≤ |v 1| := by
    have htop : v 1 ≤ R.top := hv.2.2
    have hceil := R.top_lt
    have habs := neg_le_abs (v 1)
    linarith
  exact metric_add_eventuallyEq_of_not_mem_tsupport gStar (pulseTensor q0 a N delta tau)
    (pulseTensor_not_tsupport_exterior_seed hq hU hSU hY hrange hstart hode hsmall hM hL hr
      hpartial hq0 hcenter hT ha haL hrsmall hd ht hwidth N (R.region_subset_domain hv) hseed)

end SmoothLocal.Pulse

end

end OAI

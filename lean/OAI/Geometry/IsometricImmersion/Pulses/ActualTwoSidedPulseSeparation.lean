import OAI.Geometry.IsometricImmersion.Caps.ActualLowerCutImage
import OAI.Geometry.IsometricImmersion.Caps.UpperCapWords

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Flow.Reflection
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

theorem actual_testMetric_eventuallyEq_on_upper_cap
    {G Z d c e0 kappa q0 L r delta tau : ℝ}
    {g : MetricField} {U W : Set Coord} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hh : CapInductionHeight g U Z c e0 z)
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hr : 0 < r) (hLr : L*r ≤ 1/20)
    (hq0 : |q0| ≤ 1/20) (hcenter : |hessianQuotient g z 0-q0| ≤ 1/(100*L))
    (hrsmall : heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L))
    (hdelta : 0 < delta) (htau : 0 < tau) (hwidth : delta/(2*tau) ≤ r/4)
    (gStar : MetricField) (N : ℕ) (R : UpperCapRectangle (r/2))
    {p : Coord} (hp : p ∈ R.image Y) :
    testMetric gStar q0 (L*r/16) N delta tau =ᶠ[𝓝 p] gStar := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hpartial (v : Coord) (hv : v ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient g z) v| ≤ M := hf.quotientBound [i] (by norm_num) v hv
  obtain ⟨v,hv,rfl⟩ := hp
  have hseed : r/2 ≤ |v 1| := by
    have hbottom : R.bottom ≤ v 1 := hv.2.1
    have hfloor := R.bottom_gt
    have habs := le_abs_self (v 1)
    linarith
  exact metric_add_eventuallyEq_of_not_mem_tsupport gStar (pulseTensor q0 (L*r/16) N delta tau)
    (pulseTensor_not_tsupport_exterior_seed hf.quotientSmooth hf.domainOpen hf.squareSubset
      hf.continuous hf.range hf.start hf.ode hh.quotient hM hL hr hpartial hq0 hcenter
      (by linarith : L*r < 2) (by positivity : 0 < L*r/16)
      (by nlinarith [mul_pos hL hr] : L*r/16 ≤ L*r) hrsmall hdelta htau hwidth N
      (R.region_subset_domain hv) hseed)

theorem exists_uniform_actual_two_sided_pulse_exclusion
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop, 1 ≤ tau ∧
          ∀ (g gStar : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
            |hessianQuotient g z 0-q0| ≤ 1/(100*L) →
            (∀ R : LowerCapRectangle (-r/2), ∀ p ∈ R.image Y,
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar) ∧
            (∀ R : UpperCapRectangle (r/2), ∀ p ∈ R.image Y,
              testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar) := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  obtain ⟨r,hr,hrhalf,hLr,hrsmall⟩ := exists_sectionFour_radius hM hL
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N delta hdelta
  have hevent : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hevent] with tau htau
  have htau0 : (0 : ℝ) < (tau : ℝ) := zero_lt_one.trans_le htau.1
  refine ⟨by exact_mod_cast htau.1,?_⟩
  intro g gStar U W z Y hh hf hcenter
  have hpartial (v : Coord) (hv : v ∈ modelSquare) (i : Fin 2) :
      |coordPartial i (hessianQuotient g z) v| ≤ M := hf.quotientBound [i] (by norm_num) v hv
  constructor
  · intro R p hp
    exact testMetric_eventuallyEq_on_lower_cap hf.quotientSmooth hf.domainOpen hf.squareSubset
      hf.continuous hf.range hf.start hf.ode hh.quotient hM hL hr hpartial hq0 hcenter
      (by linarith : L*r < 2) (by positivity : 0 < L*r/16)
      (by nlinarith [mul_pos hL hr] : L*r/16 ≤ L*r) hrsmall hdelta htau0 htau.2 gStar N R hp
  · intro R p hp
    exact actual_testMetric_eventuallyEq_on_upper_cap hh hf hG hZ hd hc hL hr hLr
      hq0 hcenter hrsmall hdelta htau0 htau.2 gStar N R hp

end SmoothLocal.Pulse

end

end OAI

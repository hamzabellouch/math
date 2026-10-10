import OAI.Geometry.RCD.Sobolev.UniformPhysicalInnerTests
import OAI.Geometry.RCD.Metric.MeasuredAnnularMass
import OAI.Geometry.RCD.Coordinates.NormalizedQuotientError

namespace OAI

/-! # Uniform test convergence with the smaller ball's own normalization -/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem uniform_normalized_inner_tests {n : ℕ} {S R : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : R≤S)
    {μ : Measure X} {p : ℕ → X} {r ε : ℕ → ℝ} {V : ℕ → X → Euclidean n}
    (hr : ∀ k, 0<r k)
    (hV : ∀ k, IsMeasuredEuclideanApproximation μ n (p k) (r k) S (ε k) (V k))
    (hfin : ∀ k, μ (ball (p k) (S*r k))≠⊤)
    (hpos : ∀ k, 0<μ.real (ball (p k) (S*r k))) (hε : Tendsto ε atTop (𝓝 0)) :
    ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ φ : Euclidean n →ᵇ ℝ, LipschitzWith 1 φ → ‖φ‖≤1 →
      |(μ.real (ball (p k) (R*r k)))⁻¹*(∫ x in ball (p k) (R*r k), φ (V k x) ∂μ)-
        (volume.real (ball (0:Euclidean n) R))⁻¹*(∫ z in ball 0 R, φ z)|<η := by
  let : IsFiniteMeasure (volume.restrict (ball (0:Euclidean n) R)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top (μ := (volume : Measure (Euclidean n))) (x := 0) (r := R))⟩
  let VS := volume.real (ball (0:Euclidean n) S)
  let VR := volume.real (ball (0:Euclidean n) R)
  let b := VS⁻¹*VR
  have hVS : 0<VS := ENNReal.toReal_pos (measure_ball_pos volume 0 hS).ne' measure_ball_ne_top
  have hVR : 0<VR := ENNReal.toReal_pos (measure_ball_pos volume 0 hR).ne' measure_ball_ne_top
  have hb : 0<b := mul_pos (inv_pos.mpr hVS) hVR
  have hmass := measured_ball_mass_tendsto hS hR hRS hr hV hfin hpos hε
  intro η hη
  let δ := η*b/8
  have hδ : 0<δ := by dsimp only [δ]; positivity
  have hm := (Metric.tendsto_nhds.mp hmass) δ hδ
  have hl := hmass.eventually (Ioi_mem_nhds (half_lt_self hb))
  filter_upwards [hm,hl,uniform_physical_inner_tests hS hR hRS hr hV hfin hpos hε δ hδ] with k hmk hlk htests
  intro φ hφ hφn
  let a := VS⁻¹*(∫ z in ball (0:Euclidean n) R, φ z)
  let ak := (μ.real (ball (p k) (S*r k)))⁻¹*(∫ x in ball (p k) (R*r k), φ (V k x) ∂μ)
  let bk := (μ.real (ball (p k) (S*r k)))⁻¹*μ.real (ball (p k) (R*r k))
  have ha : |a|≤b := by
    have hi := norm_integral_le_of_norm_le_const (μ := volume.restrict (ball (0:Euclidean n) R))
      (C := (1:ℝ)) (Eventually.of_forall fun z => (φ.norm_coe_le_norm z).trans hφn)
    have hi' : |∫ z in ball (0:Euclidean n) R, φ z|≤VR := by
      simpa only [VR,Real.norm_eq_abs,Measure.real,Measure.restrict_apply_univ,one_mul] using hi
    change |VS⁻¹*(∫ z in ball (0:Euclidean n) R, φ z)|≤VS⁻¹*VR
    rw [abs_mul,abs_of_pos (inv_pos.mpr hVS)]
    exact mul_le_mul_of_nonneg_left hi' (inv_nonneg.mpr hVS.le)
  have he := normalized_quotient_error hb hlk.le ha (ak:=ak) (bk:=bk)
  have hea : |ak-a|<δ := htests φ hφ hφn
  have heb : |bk-b|<δ := by simpa only [Real.dist_eq] using hmk
  have hsmall : (2/b)*(|ak-a|+|bk-b|)<η := by
    have hsum : |ak-a|+|bk-b|<2*δ := by linarith
    have hx := mul_lt_mul_of_pos_left hsum (show 0<2/b from div_pos (by norm_num) hb)
    have hval : (2/b)*(2*δ)=η/2 := by dsimp only [δ]; field_simp [hb.ne']; ring
    rw [hval] at hx
    exact hx.trans (half_lt_self hη)
  have hbki : μ.real (ball (p k) (R*r k))≠0 := by
    intro hz
    have : bk=0 := by simp only [bk,hz,mul_zero]
    change b/2<bk at hlk
    linarith
  have halg : ak/bk=(μ.real (ball (p k) (R*r k)))⁻¹*
      (∫ x in ball (p k) (R*r k), φ (V k x) ∂μ) := by
    dsimp only [ak,bk]
    field_simp [(hpos k).ne',hbki]
  have halg' : a/b=VR⁻¹*(∫ z in ball (0:Euclidean n) R, φ z) := by
    dsimp only [a,b]
    field_simp [hVS.ne',hVR.ne']
  rw [halg,halg'] at he
  exact he.trans_lt hsmall

end RegularPointCoordinates

end

end OAI

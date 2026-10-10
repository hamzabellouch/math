import OAI.Geometry.RCD.Heat.CompactHeatUniformDensity
import OAI.Geometry.RCD.Heat.CompactHeatDensityGaussianTail
import OAI.Geometry.RCD.Heat.GaussianValueIntegrable
import OAI.Geometry.RCD.Metric.FiniteDensityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov

namespace OAI

/-! # The actual interpolation laws are uniformly tight

A single finite measure dominates every noise index and every interior
time. It is built from the established uniform density and Gaussian tail.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

def interpolationLaw (k : ℕ) (t : Ioo (0 : ℝ) 1) : ProbabilityMeasure X :=
  ⟨(hausdorff n X).withDensity (fun x => ENNReal.ofReal (D.interpolationDensity k t x)),
    D.interpolationDensity_probability k t⟩

theorem interpolationLaw_integral (k : ℕ) (t : Ioo (0 : ℝ) 1) (f : X → ℝ) :
    (∫ x, f x ∂(D.interpolationLaw k t : Measure X)) =
      ∫ x, D.interpolationDensity k t x*f x ∂hausdorff n X := by
  change (∫ x, f x ∂(hausdorff n X).withDensity
    (fun x => ENNReal.ofReal (D.interpolationDensity k t x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (D.interpolationDensity_continuous k t).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (ENNReal.ofReal (D.interpolationDensity k t x)).toReal • f x = _
    rw [ENNReal.toReal_ofReal (D.interpolationDensity_pos k t x).le,smul_eq_mul]

theorem interpolationLaw_finite_dominator (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ y:S, dist z y ≤ R) (hT : ∀ y:T, dist z y ≤ R) :
    ∃ σ : FiniteMeasure X, ∀ k t, (D.interpolationLaw k t : Measure X) ≤ σ := by
  let m := hausdorff n X
  obtain ⟨B,hB,hbound⟩ := D.interpolationDensity_uniform_bound hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν z hR hS hT
  obtain ⟨A,L,hA,_hL,htail⟩ := D.interpolationDensity_gaussian_tail hε1 z hR hS hT
  obtain ⟨V,b,hV,hb,hvol⟩ := hX.exponential_volume K n hn z
  let G x := Real.exp (-((1:ℝ)/40)*(dist z x)^2)
  have hGi : Integrable G m := by
    simpa only [G,dist_comm] using gaussian_integrable m z hV hb (c := (1:ℝ)/40) (by norm_num) hvol
  let I := (closedBall z L).indicator (fun _ : X => B)
  have hIi : Integrable I m := by
    let : IsFiniteMeasure (m.restrict (closedBall z L)) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall z L).measure_lt_top.ne
    exact (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrable_const B : IntegrableOn (fun _ : X => B) (closedBall z L) m)
  let F x := I x+A*G x
  have hFi : Integrable F m := hIi.add (hGi.const_mul A)
  refine ⟨finiteDensityMeasure m hFi,?_⟩
  intro k t
  apply withDensity_mono
  refine Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal ?_
  change D.interpolationDensity k t x ≤ I x+A*G x
  by_cases hx : x ∈ closedBall z L
  · rw [show I x=B from indicator_of_mem hx _]
    exact (hbound k t x).trans (le_add_of_nonneg_right (by dsimp [G]; positivity))
  · rw [show I x=0 from indicator_of_notMem hx _ ,zero_add]
    have hd : L ≤ dist x z := le_of_lt (lt_of_not_ge hx)
    have he : G x = Real.exp (-(dist x z)^2/40) := by
      dsimp only [G]
      rw [dist_comm z x]
      congr 1
      ring
    rw [he]
    exact htail k t x hd

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI

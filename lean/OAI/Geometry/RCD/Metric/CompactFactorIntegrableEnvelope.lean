import OAI.Geometry.RCD.Metric.CompactFactorTimeTail
import OAI.Geometry.RCD.Heat.GaussianValueIntegrable
import OAI.Geometry.RCD.Metric.CompactFactorNonnegativeL2
import OAI.Geometry.RCD.Coordinates.KernelHeatBoundedRegularity

namespace OAI

/-! # A common integrable bound for compact heat factors on a time window -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_factor_integrable_envelope {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (ρ : X → ℝ)
    (hm : Measurable ρ) (hρ : ∀ x, 0 ≤ ρ x) {B : ℝ≥0}
    (hB : ∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B)
    (hν : ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)))
    (F : C(S,ℝ)) (hF : ∀ y, 0 < F y) (z : X) {R a b : ℝ}
    (hR : 1 ≤ R) (hS : ∀ y : S, dist z y ≤ R)
    (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∃ H : X → ℝ, Integrable H (hausdorff n X) ∧ (∀ x, 0 ≤ H x) ∧
      ∀ (t : ℝ) (hat : a ≤ t) (_htb : t ≤ b) (x : X),
        |hX.compactHeatFactor hn p ν F t (ha.trans_le hat) x| ≤ H x := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨f,A,_hf0,hf,hval⟩ := hX.compact_heat_factor_nonnegative_L2 hn p ν ρ hm hρ hB hν F
    (fun y => (hF y).le)
  obtain ⟨C,hC,htail⟩ := hX.compact_factor_time_tail hn p ν F (fun y => (hF y).le)
    z hR hS ha hab hb
  obtain ⟨V,D,hV,hD,hvol⟩ := hX.exponential_volume K n hn z
  have hb0 : 0 < b := ha.trans_le hab
  let g := fun x : X => Real.exp (-(dist x z)^2/(20*b))
  have hg : Integrable g m := by
    have he : g = fun x => Real.exp (-(1/(20*b))*(dist z x)^2) := by
      funext x
      dsimp only [g]
      rw [dist_comm x z]
      congr 1
      ring
    rw [he]
    simpa only [dist_comm] using
      (gaussian_integrable m z (c := 1/(20*b)) hV hD (by positivity) hvol)
  let H := fun x => (closedBall z (2*R)).indicator (fun _ => (A:ℝ)) x+C*g x
  have hAi : IntegrableOn (fun _ : X => (A:ℝ)) (closedBall z (2*R)) m :=
    continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall z (2*R))
  have hHi : Integrable H m :=
    ((integrable_indicator_iff measurableSet_closedBall).mpr hAi).add (hg.const_mul C)
  have hH0 (x : X) : 0 ≤ H x := by
    apply add_nonneg
    · exact indicator_nonneg (fun _ _ => A.coe_nonneg) x
    · exact mul_nonneg hC (Real.exp_pos _).le
  refine ⟨H,hHi,hH0,?_⟩
  intro t hat htb x
  have ht := ha.trans_le hat
  by_cases hx : x ∈ closedBall z (2*R)
  · have hbound := (hX.kernelHeat_bounded_regularity hn p hk f A hf t ht).2 x
    rw [← hval t ht x] at hbound
    dsimp only [H]
    rw [indicator_of_mem hx]
    exact hbound.trans (le_add_of_nonneg_right (mul_nonneg hC (Real.exp_pos _).le))
  · have hfar : 2*R ≤ dist x z := le_of_lt (lt_of_not_ge hx)
    have hbound := htail t hat htb x hfar
    rw [← abs_of_pos (hX.compactHeatFactor_positive hn p ν F hF t ht x)] at hbound
    dsimp only [H,g]
    rw [indicator_of_notMem hx,zero_add]
    exact hbound

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

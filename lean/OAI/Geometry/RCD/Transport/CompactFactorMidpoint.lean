import OAI.Geometry.RCD.Heat.CompactFactorTimeRatio
import OAI.Geometry.RCD.Coordinates.CompactFactorRegularity
import OAI.Geometry.RCD.Heat.HeatHamiltonPositive

namespace OAI

/-! # A normalized midpoint datum for each actual compact heat factor

The amplitude is the supremum of the earlier heat factor. Kernel
comparison controls this same supremum at every observation point.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_heat_factor_midpoint :
    ∃ C D : ℝ, 0≤C ∧ 0<D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
        (ρ : X → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0≤ρ x) {B : ℝ≥0},
        (∀ᵐ x ∂hausdorff n X, |ρ x|≤B) →
        ν.map Subtype.val = (hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
        ∀ (F : C(S, ℝ)), (∀ a, 0<F a) → ∀ (t : ℝ) (ht : 0<t), t≤1/2 →
        ∃ (g : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0), 0<(A:ℝ) ∧ 0≤g ∧
          (∀ᵐ x ∂hausdorff n X, |g x|≤A) ∧
          (∀ (s : ℝ) (hs : 0<s) (x : X),
            kernelHeat (hausdorff n X) hX.quadratic
              (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s g x =
            hX.compactHeatFactor hn p ν F (t+s) (add_pos ht hs) x) ∧
          ∀ (x : X) (R : ℝ), 0≤R → (∀ a : S, dist x a≤R) →
            Real.log A-Real.log (hX.compactHeatFactor hn p ν F (2*t) (by positivity) x)≤
              C+D*R^2/t := by
  obtain ⟨Q,D,hQ,hD,hcomp⟩ := hX.compact_heat_factor_time_ratio hn p
  refine ⟨|Real.log Q|,D,abs_nonneg _,hD,?_⟩
  intro S _ ν _ ρ hρ hρ0 B hB hν F hF t ht ht1
  let μ := hausdorff n X
  let q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨f,hf,he⟩ := hX.compact_heat_factor_L2 hn p ν ρ hρ hρ0 hB hν F
  obtain ⟨E,hE⟩ := hf
  let H := hX.compactHeatFactor hn p ν F t ht
  have hHb (x : X) : |H x|≤E := by
    rw [show H x=kernelHeat μ q hk t f x from he t ht x]
    exact (hX.kernelHeat_bounded_regularity hn p hk f E hE t ht).2 x
  let V : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup H H.continuous E
    (fun x => by simpa only [Real.norm_eq_abs] using hHb x)
  let g := heatAt μ q t f
  have hrep : H =ᵐ[μ] g :=
    (show H =ᵐ[μ] kernelHeat μ q hk t f from .of_forall (he t ht)).trans
      (kernelHeat_represents_L2 μ q hk ht f)
  have hV0 : 0<‖V‖ := lt_of_lt_of_le (by
    change 0<‖H p‖
    rw [Real.norm_eq_abs,abs_of_pos (hX.compactHeatFactor_positive hn p ν F hF t ht p)]
    exact hX.compactHeatFactor_positive hn p ν F hF t ht p) (V.norm_coe_le_norm p)
  have hg0 : 0≤g := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hrep] with x hx
    rw [←hx]
    exact (hX.compactHeatFactor_positive hn p ν F hF t ht x).le
  have hgA : ∀ᵐ x ∂μ, |g x|≤‖V‖₊ := by
    filter_upwards [hrep] with x hx
    rw [←hx]
    exact V.norm_coe_le_norm x
  refine ⟨g,‖V‖₊,hV0,hg0,hgA,?_,?_⟩
  · intro s hs x
    rw [←kernelHeat_add μ q hk ht hs f x]
    exact (he (t+s) (add_pos ht hs) x).symm
  · intro x R hR hdist
    have hv := hX.compactHeatFactor_positive hn p ν F hF (2*t) (by positivity) x
    have hnorm : ‖V‖≤Q*Real.exp (D*R^2/t)*hX.compactHeatFactor hn p ν F (2*t) (by positivity) x := by
      apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
      intro y
      change ‖H y‖≤_
      rw [Real.norm_eq_abs,abs_of_pos (hX.compactHeatFactor_positive hn p ν F hF t ht y)]
      exact hcomp ν F (fun a => (hF a).le) t ht ht1 x R hR hdist y
    have hl := Real.log_le_log hV0 hnorm
    rw [Real.log_mul (mul_pos hQ (Real.exp_pos _)).ne' hv.ne',
      Real.log_mul hQ.ne' (Real.exp_ne_zero _),Real.log_exp] at hl
    change Real.log ‖V‖-Real.log _≤_
    linarith only [hl,le_abs_self (Real.log Q)]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

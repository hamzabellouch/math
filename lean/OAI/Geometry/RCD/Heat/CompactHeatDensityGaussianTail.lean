import OAI.Geometry.RCD.Heat.CompactHeatDensityKernelBound
import OAI.Geometry.RCD.Heat.CompactEndpointKernelBounds
import OAI.Geometry.RCD.Heat.GaussianBridgeKernelBound

namespace OAI

/-! # Uniform Gaussian tails for the original compact scaling densities

The row normalization cancels the two endpoint weights. The estimate is
uniform in the noise index and over the entire open time interval.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal
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

theorem interpolationDensity_gaussian_tail (hε1 : ∀ k, ε k ≤ 1)
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ b : T, dist z b ≤ R) :
    ∃ B L : ℝ, 0 < B ∧ 0 < L ∧ ∀ (k : ℕ) (t : Ioo (0:ℝ) 1) (x : X),
      L ≤ dist x z → D.interpolationDensity k t x ≤ B*Real.exp (-(dist x z)^2/40) := by
  obtain ⟨A,B,hA,hB,hupper⟩ := hX.compact_endpoint_kernel_upper hn p z hR
  obtain ⟨a,E,ha,hE,hlower⟩ := hX.compact_endpoint_kernel_lower hn p z hR
  obtain ⟨C,hC,hbridge⟩ := gaussian_bridge_kernel_bound n
  let L := max (2*R) (max 1 (Real.sqrt (20*E)))
  have hL1 : 1 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨A^2/a*Real.exp (2*B)*C^2,L,by positivity,lt_of_lt_of_le (by norm_num) hL1,?_⟩
  intro k t x hx
  let c := ε k/4
  have hc : 0 < c := div_pos (hε k) (by norm_num)
  have hc1 : c ≤ 1 := by dsimp only [c]; linarith [hε1 k]
  have hs : 0 < c*(t:ℝ) := mul_pos hc t.property.1
  have ht : 0 < c*(1-t) := mul_pos hc (sub_pos.mpr t.property.2)
  have hsc : c*(t:ℝ) ≤ c := mul_le_of_le_one_right hc.le t.property.2.le
  have htc : c*(1-t) ≤ c := mul_le_of_le_one_right hc.le (by linarith [t.property.1])
  have hd : 1 ≤ dist x z := hL1.trans hx
  have hfar : 2*R ≤ dist x z := (le_max_left _ _).trans hx
  have hroot : Real.sqrt (20*E) ≤ dist x z :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hbudget : 20*E ≤ (dist x z)^2 := by
    have hh := Real.sq_sqrt (show 0 ≤ 20*E by positivity)
    have hsqr := pow_le_pow_left₀ (Real.sqrt_nonneg (20*E)) hroot 2
    rwa [hh] at hsqr
  apply D.interpolationDensity_kernel_bound k t x
  intro y w
  have hy : dist (y:X) z ≤ R := by simpa only [dist_comm] using hS y
  have hw : dist (w:X) z ≤ R := by simpa only [dist_comm] using hT w
  exact hbridge hA.le ha hc hc1 hs ht hsc htc hd hbudget
    (hX.canonicalHeatKernel_pos hn p _ ht x w).le
    (hupper hs (hsc.trans hc1) x y hy hfar)
    (hupper ht (htc.trans hc1) x w hw hfar)
    (hlower hc hc1 y w hy hw)

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI

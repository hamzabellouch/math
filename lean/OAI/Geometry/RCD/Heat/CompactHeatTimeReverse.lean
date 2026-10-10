import OAI.Geometry.RCD.Heat.CompactHeatScalingDensity

namespace OAI

/-! # Reversal of the actual compact heat scaling family -/

open Set MeasureTheory TopologicalSpace
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}

omit [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)]
  [CompactSpace S] [IsProbabilityMeasure μ] in
theorem kernel_integral_swap (s : ℝ) (y : X) (f : S → ℝ) :
    (∫ a, hX.canonicalHeatKernel hn p s y a*f a ∂μ) =
      ∫ a, hX.canonicalHeatKernel hn p s a y*f a ∂μ := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a =>
    congrArg (fun r : ℝ => r*f a) (hX.canonicalHeatKernel_symmetric hn p s y a)

theorem reverse_row (D : hX.CompactHeatScalingData hn p μ ν ε hε) (k : ℕ) (b : T) :
    D.right k b*(∫ a, hX.canonicalHeatKernel hn p (ε k/4) b a*D.left k a ∂μ)=1 :=
  (congrArg (fun r : ℝ => D.right k b*r)
    (kernel_integral_swap (hX := hX) (hn := hn) (p := p) (S := S) (μ := μ) (ε k/4) (b:X) (D.left k))).trans (D.col k b)

theorem reverse_col (D : hX.CompactHeatScalingData hn p μ ν ε hε) (k : ℕ) (a : S) :
    D.left k a*(∫ b, hX.canonicalHeatKernel hn p (ε k/4) b a*D.right k b ∂ν)=1 :=
  (congrArg (fun r : ℝ => D.left k a*r)
    (kernel_integral_swap (hX := hX) (hn := hn) (p := p) (S := T) (μ := ν) (ε k/4) (a:X) (D.right k)).symm).trans (D.row k a)

def reverse (D : hX.CompactHeatScalingData hn p μ ν ε hε) :
    hX.CompactHeatScalingData hn p ν μ ε hε where
  left := D.right
  right := D.left
  forward := D.backward
  backward := D.forward
  index := D.index
  strict := D.strict
  left_pos := D.right_pos
  right_pos := D.left_pos
  row := D.reverse_row
  col := D.reverse_col
  forward_limit := D.backward_limit
  backward_limit := D.forward_limit
  left_limit := D.right_limit
  right_limit := D.left_limit

theorem reverse_density (D : hX.CompactHeatScalingData hn p μ ν ε hε)
    (k : ℕ) (t : Ioo (0:ℝ) 1) (x : X) :
    D.reverse.interpolationDensity k ⟨1-t,by constructor <;> linarith [t.property.1,t.property.2]⟩ x =
      D.interpolationDensity k t x := by
  change (∫ b, hX.canonicalHeatKernel hn p (ε k/4*(1-t)) x b*D.right k b ∂ν)*
      (∫ a, hX.canonicalHeatKernel hn p (ε k/4*(1-(1-t))) x a*D.left k a ∂μ) =
    (∫ a, hX.canonicalHeatKernel hn p (ε k/4*t) x a*D.left k a ∂μ)*
      (∫ b, hX.canonicalHeatKernel hn p (ε k/4*(1-t)) x b*D.right k b ∂ν)
  rw [show 1-(1-(t:ℝ)) = t by ring,mul_comm]

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI

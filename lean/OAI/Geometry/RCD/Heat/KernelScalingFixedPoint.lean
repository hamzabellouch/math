import OAI.Geometry.RCD.Heat.KernelDifferenceTransform
import Mathlib.Topology.MetricSpace.Contracting

namespace OAI

/-! # The fixed point for compact positive kernel scaling

Alternating the two negative logarithmic transforms is a strict
contraction on continuous functions modulo constants.
-/

open Set MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

def transposeContinuousKernel (K : C(X × Y, ℝ)) : C(Y × X, ℝ) :=
  ⟨fun p => K (p.2,p.1),K.continuous.comp continuous_swap⟩

theorem positive_kernel_difference_fixedPoint (K : C(X × Y, ℝ)) {m M : ℝ}
    (hm : 0 < m) (hK : ∀ x y, m ≤ K (x,y)) (hM : ∀ x y, K (x,y) ≤ M)
    (x₀ : X) (y₀ : Y) :
    ∃ d : ContinuousDifference X,
      kernelDifferenceTransform ν K hm hK y₀
        (kernelDifferenceTransform μ (transposeContinuousKernel K) hm (fun y x => hK x y) x₀ d) = d := by
  let : Nonempty X := ⟨x₀⟩
  let : Nonempty Y := ⟨y₀⟩
  have hmM : m ≤ M := (hK x₀ y₀).trans (hM x₀ y₀)
  have hM0 : 0 < M := hm.trans_le hmM
  have hq0 : 0 ≤ 1-m/M := sub_nonneg.mpr ((div_le_one hM0).mpr hmM)
  have hq1 : 1-m/M < 1 := sub_lt_self 1 (div_pos hm hM0)
  let q : ℝ≥0 := ⟨1-m/M,hq0⟩
  have hqval : (q : ℝ)=1-m/M := rfl
  let A := kernelDifferenceTransform ν K hm hK y₀
  let B := kernelDifferenceTransform μ (transposeContinuousKernel K) hm (fun y x => hK x y) x₀
  have hA : LipschitzWith q A := by
    apply LipschitzWith.of_dist_le_mul
    intro d e
    rw [dist_eq_norm,dist_eq_norm,hqval]
    exact kernelDifferenceTransform_norm ν K hm hK hM y₀ d e hmM
  have hB : LipschitzWith q B := by
    apply LipschitzWith.of_dist_le_mul
    intro d e
    rw [dist_eq_norm,dist_eq_norm,hqval]
    exact kernelDifferenceTransform_norm μ (transposeContinuousKernel K)
      hm (fun y x => hK x y) (fun y x => hM x y) x₀ d e hmM
  have hAB : ContractingWith (q*q) (A ∘ B) := by
    refine ⟨?_,hA.comp hB⟩
    change (1-m/M)*(1-m/M) < 1
    nlinarith
  exact ⟨hAB.fixedPoint (A ∘ B),hAB.fixedPoint_isFixedPt⟩

end RegularPointCoordinates

end

end OAI

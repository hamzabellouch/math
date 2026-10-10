import OAI.Analysis.ModularTheory.CovariantKernel
import OAI.Analysis.OperatorAlgebra.IntegratedModularField

namespace OAI

/-! Integrable regularizations of the actual scalar-slice kernel lie in
the crossed product. The subsequent reconstruction step identifies these
operators with bounded convolution/dual-action regularizations. -/

noncomputable section
open MeasureTheory
open scoped Topology

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def modularKernelCoefficient
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (r : ℝ) : H →L[ℂ] H :=
  modularSliceKernel T f g 0 (-r)

lemma modularKernelCoefficient_continuous
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) : Continuous (modularKernelCoefficient T f g) := by
  have hp : Continuous (fun r : ℝ => ((0 : ℝ), -r)) :=
    continuous_const.prodMk continuous_neg
  change Continuous ((fun p : ℝ × ℝ => modularSliceKernel T f g p.1 p.2) ∘
    (fun r : ℝ => ((0 : ℝ), -r)))
  exact (modularSliceKernel_continuous T f g).comp hp

lemma modularKernelCoefficient_bound
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (r : ℝ) :
    ‖modularKernelCoefficient T f g r‖ ≤ ‖f‖ * ‖T‖ * ‖g‖ :=
  modularSliceKernel_norm_le T f g 0 (-r)

def modularKernelRegularization (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (k : ℝ → ℂ) (hk : Integrable k) :
    Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ) :=
  integratedModularField S (modularKernelCoefficient T f g)
    (modularKernelCoefficient_continuous T f g) (‖f‖ * ‖T‖ * ‖g‖)
    (modularKernelCoefficient_bound T f g) k hk

theorem modularKernelRegularization_mem (S : BoundedRecovery.StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ amplifiedModularAlgebra volume S)
    (f g : Lp ℂ 2 (volume : Measure ℝ)) (k : ℝ → ℂ) (hk : Integrable k) :
    modularKernelRegularization S T f g k hk ∈ modularCrossedProduct volume S :=
  integratedModularField_mem S _ _ (fun r => modularSliceKernel_mem S T hT f g 0 (-r))
    _ _ k hk

end WeakPureInfiniteness

end

end OAI

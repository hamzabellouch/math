import OAI.Geometry.RCD.Heat.CompactKernelFactor
import OAI.Geometry.RCD.Heat.CanonicalStrictPositivity

namespace OAI

/-! # Actual forward and backward heat factors for compact endpoint laws -/

open Set MeasureTheory TopologicalSpace
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

def compactHeatFactorKernel (S : Set X) (t : ℝ) (ht : 0 < t) : C(X × S, ℝ) := by
  let inc : X × S → X × X := fun z => (z.1,z.2.val)
  have hi : Continuous inc := continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hk := hX.canonicalHeatKernel_continuous_joint hn p t ht
  exact ⟨(fun z : X × X => hX.canonicalHeatKernel hn p t z.1 z.2) ∘ inc,hk.comp hi⟩

def compactHeatFactor {S : Set X} [CompactSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (F : C(S, ℝ)) (t : ℝ) (ht : 0 < t) : C(X, ℝ) :=
  compactKernelFactor μ (hX.compactHeatFactorKernel hn p S t ht) F

theorem compactHeatFactor_positive {S : Set X} [CompactSpace S] (μ : Measure S)
    [IsProbabilityMeasure μ] (F : C(S, ℝ)) (hF : ∀ y, 0 < F y)
    (t : ℝ) (ht : 0 < t) (x : X) : 0 < hX.compactHeatFactor hn p μ F t ht x := by
  exact compactKernelFactor_pos μ _ F
    (fun x y => hX.canonicalHeatKernel_pos hn p t ht x y) hF x

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI

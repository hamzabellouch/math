import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatContinuous
import OAI.Geometry.WeakHessian.LocalBounds.SquareTimePairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile135
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

lemma cheegerHeat_variance_continuousOn (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (u ρ : Lp ℝ 2 m) (n : ℕ)
    (hub : ∀ᵐ x ∂m,|u x| ≤ (n:ℝ)) (t : ℝ) :
    ContinuousOn (fun s => ∫ x,(cheegerHeat h s u x)^2*cheegerHeat h (t-s) ρ x ∂m) (Icc 0 t) := by
  have hcu := (continuous_clipSquareLp (m := m) n).comp_continuousOn
    ((cheegerHeat_continuousOn hfin h u).mono (show Icc (0:ℝ) t ⊆ Ici (0:ℝ) from fun _ hx => hx.1))
  have hcv : ContinuousOn (fun s => cheegerHeat h (t-s) ρ) (Icc 0 t) :=
    (cheegerHeat_continuousOn hfin h ρ).comp (continuous_const.sub continuous_id).continuousOn
      (fun _ hx => sub_nonneg.mpr hx.2)
  apply (hcu.inner hcv).congr
  intro s hs
  dsimp only [Function.comp_def]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [clipSquareLp_eq_square (cheegerHeat_bounded h hs.1 (Nat.cast_nonneg n) u hub)] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
  ring
end WeakHessian

end
end InlinedFile135

end OAI

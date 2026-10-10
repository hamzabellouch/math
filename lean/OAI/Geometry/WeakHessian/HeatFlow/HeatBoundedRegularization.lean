import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.ReversePoincarePointwise
import OAI.Geometry.WeakHessian.LocalBounds.LpLipschitzClosed
import OAI.Geometry.WeakHessian.Entropy.BoundedLipschitzDensity

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile142
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

omit [CompleteSpace X] in
lemma RCD.cheegerHeat_bounded_regularization {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) (u : Lp ℝ 2 m)
    (n : ℕ) (hu : ∀ᵐ x ∂m,|u x| ≤ (n:ℝ)) {t : ℝ} (ht : 0 < t) :
    ∃ g : X → ℝ,LipschitzWith (Real.toNNReal (Real.sqrt ((n:ℝ)^2/(2*t*Real.exp (-2*|K| *t))))) g ∧
      g =ᵐ[m] cheegerHeat h t u := by
  obtain ⟨fs,hf,hb,hf2,hT⟩ := bounded_lipschitz_L2_approx hfin h u n hu
  have hex (k : ℕ) := hrcd.cheegerHeat_reversePoincare_lipschitz hN hfull hfin h o
    (hf k).choose_spec (hf2 k) n (hb k) ht
  choose gs hLip he using hex
  have HT := (cheegerHeat h t).continuous.tendsto u |>.comp hT
  exact exists_lipschitz_of_tendsto_Lp HT hLip he
end WeakHessian

end
end InlinedFile142

end OAI

import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.FormGenerator

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile158
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

omit [CompleteSpace E] in
lemma ClosedQuadraticEnergy.generator_pairing_bound_of_graph_approx
    (S : E → E → Prop)
    (hS : ∀ u A,S u A → hQ.IsFormGenerator u A)
    (hd : ∀ u A,hQ.IsFormGenerator u A → ∃ us As : ℕ → E,
      (∀ n,S (us n) (As n)) ∧ Tendsto us atTop (𝓝 u) ∧ Tendsto As atTop (𝓝 A))
    (f : E) (C : ℝ)
    (hb : ∀ u A,S u A → |⟪f,A⟫_ℝ| ≤ C*(‖u‖+Real.sqrt (2*(Q u).toReal))) :
    ∀ u A,hQ.IsFormGenerator u A → |⟪f,A⟫_ℝ| ≤ C*(‖u‖+Real.sqrt (2*(Q u).toReal)) := by
  intro u A hgen
  obtain ⟨us,As,hs,hu,hA⟩ := hd u A hgen
  have he : Tendsto (fun n => 2*(Q (us n)).toReal) atTop (𝓝 (2*(Q u).toReal)) := by
    simp_rw [hQ.formGenerator_energy (hS _ _ (hs _)),hQ.formGenerator_energy hgen]
    exact (hA.inner hu).neg
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds.inner hA |>.abs)
    (tendsto_const_nhds.mul (hu.norm.add he.sqrt)) (Eventually.of_forall fun n => hb _ _ (hs n))
end WeakHessianFunctional

end
end InlinedFile158

end OAI

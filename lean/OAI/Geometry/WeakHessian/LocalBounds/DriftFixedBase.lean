import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile150
open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace WeakHessian
variable {X : Type*} [MeasurableSpace X] {m : Measure X}
lemma ae_bounded_of_tendsto_L2 {us : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (ht : Tendsto us atTop (𝓝 u)) {B : ℝ}
    (hb : ∀ n,∀ᵐ x ∂m,|us n x| ≤ B) : ∀ᵐ x ∂m,|u x| ≤ B := by
  have H := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  obtain ⟨ns,hns,hlim⟩ := H
  filter_upwards [hlim,ae_all_iff.mpr (fun n => hb (ns n))] with x hx hB
  exact le_of_tendsto hx.abs (Eventually.of_forall hB)
end WeakHessian

end
end InlinedFile150

end OAI

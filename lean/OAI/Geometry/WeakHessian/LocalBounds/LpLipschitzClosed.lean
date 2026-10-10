import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile140
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma exists_lipschitz_of_tendsto_Lp {L : ℝ≥0} {us : ℕ → Lp ℝ 2 m} {u : Lp ℝ 2 m}
    (hu : Tendsto us atTop (𝓝 u)) {fs : ℕ → X → ℝ}
    (hf : ∀ n,LipschitzWith L (fs n)) (he : ∀ n,fs n =ᵐ[m] us n) :
    ∃ f : X → ℝ,LipschitzWith L f ∧ f =ᵐ[m] u := by
  obtain ⟨ns,hns,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hu).exists_seq_tendsto_ae
  have H : ∀ᵐ x ∂m,Tendsto (fun n => fs (ns n) x) atTop (𝓝 (u x)) := by
    filter_upwards [hlim,ae_all_iff.mpr he] with x hx he
    exact hx.congr (fun n => (he (ns n)).symm)
  let S := {x | Tendsto (fun n => fs (ns n) x) atTop (𝓝 (u x))}
  have hLip : LipschitzOnWith L (u : X → ℝ) S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    exact le_of_tendsto ((hx : Tendsto (fun n => fs (ns n) x) atTop (𝓝 (u x))).dist hy)
      (Eventually.of_forall fun n => (hf (ns n)).dist_le_mul x y)
  obtain ⟨f,hf,hfe⟩ := hLip.extend_real
  refine ⟨f,hf,?_⟩
  exact H.mono fun x hx => (hfe hx).symm
end WeakHessian

end
end InlinedFile140

end OAI

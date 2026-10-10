import OAI.Geometry.HeilbronnTriangle.IntegerSampleMixtures
import OAI.Geometry.HeilbronnTriangle.IntegerSamplingGeometry

namespace OAI


namespace Problem355.IntegerSampleMixtures

noncomputable section
open LiftingProbability ConditionalSamples IntegerSamplingGeometry
attribute [local instance] Classical.propDecidable

lemma determinantMass_eq_liftedMixture
    {β Θ Ω : Type*} [Fintype β] [Fintype Θ] [Fintype Ω]
    (h q L : ℕ) (F : Θ → β → Fin 3 → ZMod h)
    (ρ : Θ → ℝ) (w : Ω → ℝ) (p : β → ℝ)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (O : (Fin 3 → β) → Finset (Fin 3 → Fin 3 → ZMod h)) (s : ℕ)
    (hpush : ∀ labels a,
      pushforwardMass ρ (fun θ i => F θ (labels i)) a = mainMass (O labels) a)
    (τ : ℤ) :
    determinantMass (fun a : Θ × Ω => ρ a.1 * w a.2)
      (mixedColumnLaw h q L F p V s) τ =
      ∑ labels : Fin 3 → β, productWeight p labels *
        ∑ x : Fin 3 → Column h q L,
          if BadDet τ x then
            liftedMass (fun x i => IntegerSampling.residue h (x i))
              (fun x i => IntegerSampling.residue q (x i))
              (O labels) w V s (L ^ 9) x
          else 0 := by
  classical
  let E : Finset (Fin 3 → Column h q L) := Finset.univ.filter (BadDet τ)
  have H := triple_event_law h q L F ρ w p V O s hpush E
  simp only [E, Finset.sum_filter] at H
  rw [← H]
  unfold determinantMass
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : BadDet τ x
  · simp only [hx, ite_true, sampleLaw]
  · simp only [hx, ite_false, Finset.sum_const_zero]

end
end Problem355.IntegerSampleMixtures

end OAI

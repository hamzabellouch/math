import OAI.Probability.InvariantIsing.Cavity.CavityLabeledProjectors

namespace OAI

/-! The joint Haar law of the labeled base projectors and their special
axes factors from the compression matrices. This statement keeps the
information used by the actual perturbation. -/

noncomputable section
open MeasureTheory
open scoped Matrix

namespace InvariantIsing

theorem cavity_labeled_projector_haar_factorization {N n m d : ℕ}
    (g : Fin (N+n) → Fin m) (k : Fin m → ℕ)
    (ek : ∀ a, {i : Fin (N+n) // g i = a} ≃ Fin (k a+n))
    (e : (((a : Fin m) × Fin (k a)) ⊕ Fin d) ≃ Fin N)
    (es : Fin (m*n) ≃ Fin (d+n))
    (B₀ : Matrix (Fin (d+n)) (Fin d) ℝ) (a₀ : Fin d → Fin m)
    (l u : Fin m → ℕ)
    (hg : ∀ a i, g i=a ↔ l a ≤ i.val ∧ i.val < u a)
    (hln : ∀ a, l a+n ≤ u a) (hu : ∀ a, u a ≤ N+n)
    (μ : Measure (Orthogonal (N+n))) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (ν : Measure (Orthogonal N)) [IsProbabilityMeasure ν] [ν.IsMulRightInvariant]
    (f : CavityProjectorFrame N m d → ℝ)
    (q : (Fin m → Matrix (Fin n) (Fin n) ℝ) → ℝ)
    (hf : Measurable f) (hq : Measurable q)
    (Cf Cq : ℝ) (hCq : 0 ≤ Cq)
    (hfb : ∀ p, ‖f p‖ ≤ Cf) (hqb : ∀ M, ‖q M‖ ≤ Cq) :
    (∫ U, q (cavityCompressionGrams g U) *
      f (cavityPhysicalLabeledProjectors g (cavityConcreteComplement es B₀) a₀ U) ∂μ) =
      (∫ U, q (cavityCompressionGrams g U) ∂μ) *
        ∫ V, f (cavityLabeledProjectorAction V (cavityCanonicalProjectorFrame k e a₀)) ∂ν := by
  let : BorelSpace (CavityProjectorFrame N m d) := inferInstanceAs
    (BorelSpace ((Fin m → Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ)))
  let : OpensMeasurableSpace (Orthogonal N × CavityProjectorFrame N m d) := inferInstanceAs
    (OpensMeasurableSpace (Orthogonal N × ((Fin m → Fin N → Fin N → ℝ) × (Fin N → Fin d → ℝ))))
  let B := cavityConcreteComplement es B₀
  have hBm : Measurable B := measurable_cavityConcreteComplement es B₀
  apply cavity_orbit_factorization_right_ae μ ν
    (fun V => cavityReservoirRotation (n := n) V⁻¹)
    (cavityPhysicalLabeledProjectors g B a₀) (cavityCompressionGrams g)
    (measurable_cavityPhysicalLabeledProjectors g B hBm a₀)
    (measurable_cavityCompressionGrams g) cavityLabeledProjectorAction
    (continuous_cavityLabeledProjectorAction N m d).measurable cavityLabeledProjectorAction_mul
    _ _ (cavityCanonicalProjectorFrame k e a₀) _ f q hf hq Cf Cq hCq hfb hqb
  · intro V
    exact ae_of_all _ (fun U => cavityPhysicalLabeledProjectors_reservoir g B a₀ U V)
  · intro V
    exact ae_of_all _ (fun U => cavityCompressionGrams_reservoir g U V⁻¹)
  · filter_upwards [cavityCompressionGrams_posDef_ae g l u hg hln hu μ] with U hU
    exact cavityPhysicalLabeledProjectors_mem_orbit g k ek e a₀ U B
      (cavityConcreteComplement_gram g es B₀ U)
      (cavityConcreteComplement_perp g es B₀ U) hU

end InvariantIsing

end

end OAI

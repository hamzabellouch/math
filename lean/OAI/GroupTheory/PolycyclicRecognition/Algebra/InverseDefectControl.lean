import OAI.GroupTheory.PolycyclicRecognition.Analysis.InverseCompactControl
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CouplingTransfer

namespace OAI

/-! # Controlling inverse oscillations by the original defects

This is the compact-region estimate in the inverse-coupling argument. All
three integrations are over whole fibers. Their bound is a fixed product
of Haar masses times the original section error.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [SecondCountableTopology W] [MeasurableSpace W] [BorelSpace W]

/-- Joint measurability of the actual stationary coboundary defect. -/
theorem measurable_pairTransferDefect (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : Measurable φ) :
    Measurable (fun q : G × NormalizedPair G Λ => pairTransferDefect π l φ q.1 q.2) := by
  have hT : Continuous (fun q : G × NormalizedPair G Λ => normalizedTranslate q.1 q.2) := by
    apply Continuous.subtype_mk
    exact continuous_translatePair.comp (continuous_fst.prodMk continuous_snd.subtype_val)
  have hb : Continuous (fun q : G × NormalizedPair G Λ => pairHeight π q.1 q.2) := by
    unfold pairHeight
    exact hπ.comp (by fun_prop)
  exact ((hb.measurable.add (hφ.comp hT.measurable)).sub
    (hφ.comp measurable_snd)).sub (hl.measurable.comp measurable_fst)

/-- The inverse oscillation integral over bounded regions is bounded by the
original section defect, with constants independent of the translating
center. -/
theorem inverse_defect_oscillation_bound
    (m : Measure G) [SFinite m] [m.IsMulLeftInvariant]
    (μ ν : Measure (NormalizedPair G Λ)) [SFinite μ] [SFinite ν]
    (hprod : inversePairCoupling m μ = ν.prod m)
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : Measurable φ)
    {B C T : Set G} (hB : MeasurableSet B) (hTm : MeasurableSet T)
    (hT : ∀ x₂ ∈ B, ∀ x₁ ∈ C, x₂⁻¹ * x₁ ∈ T)
    (y : G) (hC : ∀ p : NormalizedPair G Λ, ∀ x ∈ B, p.val.1 y * x ∈ C)
    {c : ℝ≥0∞}
    (hc : ∀ t ∈ T, (∫⁻ p, ‖pairTransferDefect π l φ t p‖ₑ ^ 2 ∂μ) ≤ c) :
    (∫⁻ p, ∫⁻ x₁ in B, ∫⁻ x₂ in B,
      ‖pairTransferDefect π l φ (x₂⁻¹ * (p.val.1 y * x₁))
        (pairChartTransition.symm (p, x₂)).2‖ₑ ^ 2 ∂m ∂m ∂ν) ≤
      (m (inverseStripBase (Λ := Λ) B) * c) * m T := by
  let f := fun (p : NormalizedPair G Λ) (x t : G) =>
    ‖pairTransferDefect π l φ t (pairChartTransition.symm (p, x)).2‖ₑ ^ 2
  have hd := measurable_pairTransferDefect π l hπ hl hφ
  have hf : Measurable (fun q : NormalizedPair G Λ × G × G => f q.1 q.2.1 q.2.2) := by
    have hm : Measurable (fun q : NormalizedPair G Λ × G × G =>
        (q.2.2, (pairChartTransition.symm (q.1, q.2.1)).2)) :=
      measurable_snd.snd.prodMk ((pairChartTransition.symm.continuous.measurable.comp
        (measurable_fst.prodMk measurable_snd.fst)).snd)
    exact (hd.comp hm).enorm.pow_const 2
  apply fiber_translated_increment_uniform_le ν m hB hTm hT
    (fun p : NormalizedPair G Λ => p.val.1 y) hC f hf
  intro t ht
  have htmeas : Measurable (fun p : NormalizedPair G Λ => ‖pairTransferDefect π l φ t p‖ₑ ^ 2) :=
    (hd.comp (measurable_const.prodMk measurable_id)).enorm.pow_const 2
  exact (inverse_strip_lintegral_le m μ ν hprod B _ htmeas).trans
    (mul_le_mul_right (hc t ht) _)

end PolycyclicRecognition

end

end OAI

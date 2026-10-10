import OAI.GroupTheory.PolycyclicRecognition.Algebra.CouplingTransfer
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace OAI

/-! # Local square integrability of the coupling transfers

A square-integrable section transfer becomes locally square integrable after
adding the continuous target height. This property is preserved by the
actual change to inverse coordinates.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace PolycyclicRecognition

variable {G W : Type*} [Group G] [MetricSpace G] [ProperSpace G]
  [SecondCountableTopology G] [IsTopologicalGroup G] [IsIsometricSMul G G]
  {Λ : ℝ≥0} [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [NormedAddCommGroup W] [SecondCountableTopology W]

omit [IsIsometricSMul G G] in
/-- The lifted transfer is square integrable on every compact subset of the
first product chart. -/
theorem pairTransferLift_memLp_compact
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    (π : G →* Multiplicative W) (hπ : Continuous fun g => (π g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {K : Set (G × NormalizedPair G Λ)} (hK : IsCompact K) :
    MemLp (pairTransferLift π φ) 2 ((m.prod μ).restrict K) := by
  have hc : Continuous (fun q : G × NormalizedPair G Λ => (π q.1).toAdd) :=
    hπ.comp continuous_fst
  have hh : MemLp (fun q : G × NormalizedPair G Λ => (π q.1).toAdd) 2
      ((m.prod μ).restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    exact ContinuousOn.integrableOn_compact hK (hc.norm.pow 2).continuousOn
  have hC : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  let : IsFiniteMeasure (m.restrict (Prod.fst '' K)) :=
    isFiniteMeasure_restrict.mpr hC.measure_ne_top
  have hs := hφ.comp_snd (m.restrict (Prod.fst '' K))
  rw [Measure.restrict_prod_eq_prod_univ] at hs
  have hsub : K ⊆ (Prod.fst '' K) ×ˢ univ := by
    intro q hq
    exact ⟨⟨q, hq, rfl⟩, mem_univ _⟩
  exact hh.add (hs.mono_measure (Measure.restrict_mono_set _ hsub))

/-- The corrected transfer in the inverse chart is locally square
integrable for the coupling measure. -/
theorem inverseFiberTransfer_memLp_compact
    (m : Measure G) [IsFiniteMeasureOnCompacts m]
    (μ : Measure (NormalizedPair G Λ)) [IsFiniteMeasure μ]
    (π l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    {φ : NormalizedPair G Λ → W} (hφ : MemLp φ 2 μ)
    {K : Set (NormalizedPair G Λ × G)} (hK : IsCompact K) :
    MemLp (inverseFiberTransfer π l φ) 2 ((inversePairCoupling m μ).restrict K) := by
  let e : (G × NormalizedPair G Λ) ≃ₜ (NormalizedPair G Λ × G) := pairChartTransition
  have he : MeasurePreserving e.symm (inversePairCoupling m μ) (m.prod μ) :=
    MeasurableEquiv.measurePreserving_symm (m.prod μ) e.toMeasurableEquiv
  have hr := he.restrict_image_emb e.symm.measurableEmbedding K
  have hLift := (pairTransferLift_memLp_compact m μ π hπ hφ
    (hK.image e.symm.continuous)).comp_measurePreserving hr
  have hc : Continuous (fun q : NormalizedPair G Λ × G => (l q.2).toAdd) :=
    hl.comp continuous_snd
  have hh : MemLp (fun q : NormalizedPair G Λ × G => (l q.2).toAdd) 2
      ((inversePairCoupling m μ).restrict K) := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    exact ContinuousOn.integrableOn_compact hK (hc.norm.pow 2).continuousOn
  exact hLift.sub hh

end PolycyclicRecognition

end

end OAI

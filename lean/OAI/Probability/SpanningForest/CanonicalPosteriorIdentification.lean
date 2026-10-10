import OAI.Probability.SpanningForest.ObservationPosterior
import OAI.Probability.SpanningForest.PosteriorDrift

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem336.Observation

abbrev historySigma {Ω I T : Type*} (Y : I → T → Ω → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (p : I × T) => Y p.1 p.2 ω) inferInstance

theorem historySigma_eq_iSup {Ω I T : Type*} (Y : I → T → Ω → ℝ) :
    historySigma Y =
      ⨆ i, MeasurableSpace.comap (fun ω s => Y i s ω) inferInstance := by
  simp only [historySigma, MeasurableSpace.comap_process_pi, iSup_prod]

theorem historySigma_finset_eq {Ω I T : Type*} (Y : I → T → Ω → ℝ)
    (S : Finset I) :
    historySigma (fun (i : S) s ω => Y i s ω) =
      ⨆ i ∈ S, MeasurableSpace.comap (fun ω s => Y i s ω) inferInstance := by
  rw [historySigma_eq_iSup]
  simp only [iSup_subtype]

theorem historySigma_le {Ω I T : Type*} [mΩ : MeasurableSpace Ω]
    (Y : I → T → Ω → ℝ) (hY : ∀ i s, Measurable (Y i s)) :
    historySigma Y ≤ mΩ :=
  (Measurable.of_eval (f := fun ω (p : I × T) => Y p.1 p.2 ω)
    (fun p => hY p.1 p.2)).comap_le

theorem drift_eq_condExp_of_finite_history
    {Ω I : Type*} [mΩ : MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) [IsFiniteMeasure P] (μ : ProbabilityMeasure (I → Bool))
    (S : I → ℕ → Finset I) (e : I)
    (hS : Monotone (S e)) (hcover : ∀ i, ∃ n, i ∈ S e n)
    (Y : I → ℝ≥0 → Ω → ℝ) (hY : ∀ i s, Measurable (Y i s))
    (X : Ω → ℝ) (t : ℝ≥0)
    (hfinite : ∀ n,
      (fun ω => TiltLimit.finiteTiltMean μ (S e n)
        (fun i => Y i t ω - (t : ℝ) / 2) e) =ᵐ[P]
        P[X | historySigma (fun (i : S e n) (s : Set.Iic t) ω => Y i s ω)]) :
    (fun ω => PosteriorDrift.drift μ S (t : ℝ) (fun i => Y i t ω) e) =ᵐ[P]
      P[X | historySigma (fun i (s : Set.Iic t) ω => Y i s ω)] := by
  let coordinate : I → MeasurableSpace Ω := fun i =>
    MeasurableSpace.comap (fun ω (s : Set.Iic t) => Y i s ω) inferInstance
  have hcoordinate : ∀ i, coordinate i ≤ mΩ := fun i =>
    (Measurable.of_eval (f := fun ω (s : Set.Iic t) => Y i s ω)
      (fun s => hY i s)).comap_le
  have hfinite' : ∀ n,
      (fun ω => TiltLimit.finiteTiltMean μ (S e n)
        (fun i => Y i t ω - (t : ℝ) / 2) e) =ᵐ[P]
        P[X | ⨆ i ∈ S e n, coordinate i] := by
    intro n
    have hn := hfinite n
    rw [historySigma_finset_eq (fun i (s : Set.Iic t) ω => Y i s ω) (S e n)] at hn
    exact hn
  have h := limsup_posterior_all_coordinates P coordinate hcoordinate (S e)
    hS hcover X _ hfinite'
  simpa only [PosteriorDrift.drift, CanonicalDrift.outerLimit,
    PosteriorDrift.finiteStage, historySigma_eq_iSup] using h

end Problem336.Observation

end

end OAI

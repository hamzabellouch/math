import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkDiagonalLimit
import OAI.Probability.Perceptron.Variational.MarkedGraphLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

theorem bulk_marked_rpc_coupling (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ)
    (hv : ∀ n p,1≤v n p) {C : ℝ} (hC : 0≤C) (hvC : ∀ n p,|v n (p+1)|≤C)
    (hdO : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
    (hdF : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n+2) g.f p (v n)) atTop (𝓝 0))
    (s : ℕ→ℕ) (hs : StrictMono s) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n=>((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (ho : Tendsto (fun n=>bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (K : ℝ) (hK0 : 0≤K) (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖g.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hf : Tendsto (fun n=>bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    ∃ d : ℝ, ∃ hd0 : 0 ≤ d, ∃ hdK : d ≤ K,
      d ≤ α*‖g.d1‖^2 ∧
      let η := markedTimePair K μ
      let q := boundedQuantile η
      let hq := boundedQuantile_monotone η
      let B := (α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)
      Tendsto (fun j => cavityLabelMarkedLaw
        (fun i => continuousCavityProfile η B hd0 hdK (roundTimeValue (unitQuantileField q hq) j i))
        (cavityTrueDiagonal hd0 hdK)
        (stepCumulative (strictRoundModel (unitQuantileField q hq) j).weight)) atTop (𝓝 μ) := by
  obtain ⟨a,ham,hab,hag,hsc,hbound⟩ :=
    bulk_marked_self_consistency M g v hv hC hvC hdO hdF s hs α hα hd ν ho K hK0 hK μ hf
  obtain ⟨d,hd0,hdK,hdA,hD2,hBd⟩ :=
    bulkMarkedArray_diagonal_producer M g v (Eventually.of_forall hv) hdO s hs α hα hd ν ho K hK μ hf
  refine ⟨d,hd0,hdK,hdA,?_⟩
  let η := markedTimePair K μ
  let q := boundedQuantile η
  let hq := boundedQuantile_monotone η
  let B := (α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)
  have hA : 0 ≤ α*‖g.d1‖^2 := mul_nonneg hα (sq_nonneg _)
  have hB : B < 1 := (div_lt_one (by linarith : 0 < 1+α*‖g.d1‖^2)).mpr (by linarith)
  have he e := compact_exchangeability_limit hf e
    (fun n => bulkMarkedArray_exchangeable (s n) (M (s n)+2) g (v (s n)) K (hK n) e)
  have hp := bulkMarkedArray_limit_overlap (fun n => M n+2) g v s K hK hf
  have hg := bulk_limit_geometry (fun n => M n+2) g.f v (Eventually.of_forall hv) hdF hs hp
  have hgeom := marked_overlap_geometry K μ he hg.1 hg.2.1
  have hD1 := ae_of_ae_map (compactMapArray_continuous (show Continuous
    (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst)).measurable.aemeasurable
    (bulkGibbsArray_limit_diagonal g.f (fun n => M n+2) v s hp)
  have hgraph := marked_graph_law μ hB hd0 hdK he hgeom.2.2 hD1 hD2 hBd a
    (fun r => (hab r).1) hag hsc hbound
  obtain ⟨hGG,hGe,hEx⟩ := bulk_marked_time_inputs (fun n => M n+2) g v
    (Eventually.of_forall hv) hdF s hs K hK μ hf
  have hpair : (markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q => Q 0 1) = timeLaw.map q :=
    (boundedQuantile_law η).symm
  have ht := cavityLabelMarkedLaw_tendsto_graph (markedTimeLaw K μ) q hq hpair hGG hGe hEx
    (continuousCavityProfile η B hd0 hdK) (continuousCavityProfile_continuous η hB hd0 hdK)
    (cavityTrueDiagonal hd0 hdK)
  rw [hgraph] at ht
  exact ht

end SphericalPerceptronFreeEnergy

end

end OAI

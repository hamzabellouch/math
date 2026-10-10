import OAI.GroupTheory.PolycyclicRecognition.Analysis.DifferentCellDomination
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CellProfileRestriction
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IndependentSupportedSampling

namespace OAI

/-! # Comparison of independently sampled cells at distinct scales -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A difference cover with bounded target volume ratio passes suffix
concentration to independent samples from two possibly different cells. -/
theorem mixed_cell_concentration
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (A C D : ℕ → Set G) (hA : ∀ n, MeasurableSet (A n))
    (hC : ∀ n, MeasurableSet (C n)) (hD : ∀ n, MeasurableSet (D n))
    (hA0 : ∀ n, μ (A n) ≠ 0) (hAfin : ∀ n, μ (A n) ≠ ∞)
    (hC0 : ∀ n, μ (C n) ≠ 0) (hCfin : ∀ n, μ (C n) ≠ ∞)
    (hD0 : ∀ n, μ (D n) ≠ 0) (hDfin : ∀ n, μ (D n) ≠ ∞)
    (hcover : ∀ n a, a ∈ A n → ∀ b ∈ C n, a⁻¹ * b ∈ D n)
    {K : ℝ≥0∞} (hK : K ≠ ∞) (hratio : ∀ n, μ (D n) / μ (C n) ≤ K)
    (B : ℕ → Set (G × G)) (hB : ∀ n, MeasurableSet (B n))
    (hp : ∀ k : ℕ → G, (∀ n, k n ∈ D n) →
      Tendsto (fun n => (cellProbabilityMeasure μ (A n) (hA0 n) (hAfin n) : Measure G)
        {a | (a, a * k n) ∈ B n}) atTop (𝓝 0)) :
    Tendsto (fun n => (cellProbabilityMeasure μ (A n) (hA0 n) (hAfin n) : Measure G).prod
      (cellProbabilityMeasure μ (C n) (hC0 n) (hCfin n) : Measure G) (B n))
      atTop (𝓝 0) := by
  let μA n := cellProbabilityMeasure μ (A n) (hA0 n) (hAfin n)
  let μD n := cellProbabilityMeasure μ (D n) (hD0 n) (hDfin n)
  let P n := (fun p : G × G => (p.1, p.1 * p.2)) ⁻¹' B n
  have hmap : Measurable (fun p : G × G => (p.1, p.1 * p.2)) :=
    measurable_fst.prodMk (measurable_fst.mul measurable_snd)
  have hprob := independent_supported_bad_probability_tendsto_zero μA μD D
    (fun n => nonempty_of_measure_ne_zero (hD0 n))
    (fun n => ae_mem_cellProbabilityMeasure μ (D n) (hD n) (hD0 n) (hDfin n))
    P (fun n => hmap (hB n)) hp
  have hbound n := different_cell_pair_domination (μA n) (A n)
    (ae_mem_cellProbabilityMeasure μ (A n) (hA n) (hA0 n) (hAfin n))
    μ (C n) (D n) (hC n) (hC0 n) (hCfin n) (hD0 n) (hDfin n)
    (fun a k => a * k) (fun a _ => measurePreserving_mul_left μ a) (by
      intro a ha k hk
      have hb : a * k ∈ C n := hk
      simpa only [inv_mul_cancel_left] using hcover n a ha (a * k) hb)
    hmap (B n) (hB n)
  have hlim := ENNReal.Tendsto.const_mul hprob (Or.inr hK)
  simp only [mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le)
  intro n
  exact (hbound n).trans (mul_le_mul' (hratio n) le_rfl)

end PolycyclicRecognition

end

end OAI

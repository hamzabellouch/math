import OAI.Probability.InvariantIsing.Spectral.SpectralBallPartition

namespace OAI

/-! The actual finite quantizer attached to the null-boundary ball cover. -/

noncomputable section
open MeasureTheory Set Metric
open scoped Topology Classical Function

namespace InvariantIsing

def spectralBallQuantizer {n : ℕ} (c r : Fin n → ℝ) (fallback : ℝ) (x : ℝ) : ℝ :=
  (spectralPartitionIndex (spectralBallCell (fun i => ball (c i) (r i)))
    (spectralBallCell_cover _) x).elim fallback c

lemma measurable_spectralBallQuantizer {n : ℕ} (c r : Fin n → ℝ) (fallback : ℝ) :
    Measurable (spectralBallQuantizer c r fallback) := by
  let : MeasurableSpace (Option (Fin n)) := ⊤
  exact (measurable_of_countable (fun i : Option (Fin n) => i.elim fallback c)).comp
    (measurable_spectralPartitionIndex _ (spectralBallCell_cover _) (spectralBallCell_disjoint _)
      (spectralBallCell_measurable _ (fun _ => measurableSet_ball)))

lemma spectralBallQuantizer_close {n : ℕ} (c r : Fin n → ℝ) (fallback δ x : ℝ)
    (hr : ∀ i, r i ≤ δ) (hx : x∈⋃ i, ball (c i) (r i)) :
    dist (spectralBallQuantizer c r fallback x) x ≤ δ := by
  let B := fun i => ball (c i) (r i)
  let j := spectralPartitionIndex (spectralBallCell B) (spectralBallCell_cover B) x
  have hj : x∈spectralBallCell B j := spectralPartitionIndex_mem _ _ x
  cases h : j with
  | none =>
    have hh : x ∉ ⋃ i, B i := by simpa only [h,spectralBallCell, Set.mem_compl_iff] using hj
    exact False.elim (hh hx)
  | some i =>
    have hxi : x∈B i := disjointed_subset B i (by simpa only [h,spectralBallCell] using hj)
    have hd : dist x (c i) < r i := hxi
    have he : spectralBallQuantizer c r fallback x=c i := by
      change j.elim fallback c=c i
      rw [h]
      rfl
    rw [he,dist_comm]
    exact hd.le.trans (hr i)

lemma spectralBallQuantizer_mem {n : ℕ} (c r : Fin n → ℝ) (fallback : ℝ) (K : Set ℝ)
    (hc : ∀ i, c i∈K) (hf : fallback∈K) (x : ℝ) : spectralBallQuantizer c r fallback x∈K := by
  unfold spectralBallQuantizer
  cases spectralPartitionIndex (spectralBallCell (fun i => ball (c i) (r i)))
      (spectralBallCell_cover _) x with
  | none => exact hf
  | some i => exact hc i

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Spectral.PositiveSpectralPartition
import OAI.Probability.InvariantIsing.Spectral.SpectralBallQuantizer

namespace OAI

/-! One-sided spectral rounding remains valid on the zero-mass cells. -/

noncomputable section
open MeasureTheory Set Metric
open scoped Topology Classical Function

namespace InvariantIsing

lemma positive_spectral_rounding_bounds {ι : Type*} [Fintype ι]
    (μ : Measure ℝ) (S : ι → Set ℝ) (hcover : ∀ x, ∃ i, x∈S i)
    (lam : ι → ℝ) (a b δ : ℝ)
    (lo hi : {i // 0 < μ.real (S i)})
    (hlo : lam lo-δ ≤ a) (hhi : b ≤ lam hi+δ)
    (hcell : ∀ i, 0 < μ.real (S i) → ∀ x∈S i, dist (lam i) x ≤ δ)
    (x : ℝ) (hx : x∈Icc a b) :
    lam (positiveSpectralLabel (fun i => μ.real (S i)) lo
      (spectralPartitionIndex S hcover x))-δ ≤ x ∧
    x ≤ lam (positiveSpectralLabel (fun i => μ.real (S i)) hi
      (spectralPartitionIndex S hcover x))+δ := by
  let j := spectralPartitionIndex S hcover x
  by_cases hp : 0 < μ.real (S j)
  · have hc := hcell j hp x (spectralPartitionIndex_mem S hcover x)
    rw [Real.dist_eq,abs_le] at hc
    simp only [show spectralPartitionIndex S hcover x=j from rfl,
      positiveSpectralLabel,dite_eq_left hp]
    constructor <;> linarith
  · simp only [show spectralPartitionIndex S hcover x=j from rfl,
      positiveSpectralLabel,dite_eq_right hp]
    exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩

lemma positive_spectral_ball_cell_close {n : ℕ}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (c r : Fin n → ℝ)
    (a δ : ℝ) (hr : ∀ i, r i ≤ δ)
    (hzero : μ (spectralBallCell (fun i => ball (c i) (r i)) none)=0)
    (i : Option (Fin n)) (hi : 0 < μ.real (spectralBallCell (fun i => ball (c i) (r i)) i))
    (x : ℝ) (hx : x∈spectralBallCell (fun i => ball (c i) (r i)) i) :
    dist (i.elim a c) x ≤ δ := by
  cases i with
  | none =>
    have hz : μ.real (spectralBallCell (fun i => ball (c i) (r i)) none)=0 :=
      (measureReal_eq_zero_iff).mpr hzero
    exact (not_lt_of_ge hz.le hi).elim
  | some i =>
    have hh : x∈ball (c i) (r i) := disjointed_subset (fun i => ball (c i) (r i)) i hx
    simpa only [Option.elim_some,dist_comm] using (show dist x (c i) ≤ δ from hh.le.trans (hr i))

end InvariantIsing

end

end OAI

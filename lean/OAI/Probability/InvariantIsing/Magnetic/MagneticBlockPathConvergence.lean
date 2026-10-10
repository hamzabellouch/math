import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockPath

namespace OAI

/-! Uniform replacement of the entire original constrained overlap path,
with no bound on the number of covariance levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

theorem magneticBlockPath_l1_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNlim : Tendsto N atTop atTop)
    (group : ∀ n, Fin (N n) → A) (k : ℕ → A → ℕ)
    (hk : ∀ n a, k n a ≤ spinGroupSize (group n) a) (m : ℕ → A → ℝ)
    {r H : ℝ} (hr : r < 1) (hm : ∀ n a, |m n a| ≤ r)
    (hc : ∀ n a, (k n a : ℝ) = spinGroupSize (group n) a * ((1 + m n a) / 2))
    (h : ℕ → FieldStep) (hH : ∀ n, (h n).height (Fin.last (h n).depth) ≤ H) :
    Tendsto (fun n => ∫ s, |restrictedBlockOverlapPath (hN n)
      (spinGroupSlice (group n) (k n)) (spinGroupSlice_nonempty (group n) (k n) (hk n)) (h n) s -
        magneticBlockPath (hN n) (h n) (fun j => m n (group n j)) s| ∂pathMeasure)
      atTop (𝓝 0) := by
  apply tendsto_zero_of_pair_entropy _
    (fun n => (N n : ℝ)⁻¹ * (∑ j, constrainedFieldValue (h n) (m n (group n j))) -
      constrainedBlockValue (spinGroupSlice (group n) (k n)) (h n))
    (fun n => integral_nonneg (fun _ => abs_nonneg _))
    (magneticBlockGap_tendsto N hN hNlim group k hk m hr hm hc h hH)
  intro t ht n
  exact magneticBlockPath_l1_comparison (hN n) (group n) (k n) (hk n) (m n)
    (fun a => (hm n a).trans_lt hr) (hc n) (h n) ht

end InvariantIsing

end

end OAI

import OAI.Probability.InvariantIsing.Magnetic.MagneticPairComparison
import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockConvergence

namespace OAI

/-! Uniform two-spin replacement along arbitrary bounded-height field
partitions, including partitions of increasing depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

lemma tendsto_zero_of_pair_entropy (f g : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (hg : Tendsto g atTop (𝓝 0))
    (hb : ∀ t : ℝ, 0 < t → ∀ n, f n ≤ 2 * g n / t + t / 2) :
    Tendsto f atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (hf n))
  · intro a ha
    have ht : Tendsto (fun n => 2 * g n / a) atTop (𝓝 0) := by
      simpa using (hg.const_mul 2).div_const a
    filter_upwards [ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < a / 2))] with n hn
    have he := hb a ha n
    linarith

theorem magneticBlockPairGap_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNlim : Tendsto N atTop atTop)
    (group : ∀ n, Fin (N n) → A) (k : ℕ → A → ℕ)
    (hk : ∀ n a, k n a ≤ spinGroupSize (group n) a) (m : ℕ → A → ℝ)
    {r H : ℝ} (hr : r < 1) (hm : ∀ n a, |m n a| ≤ r)
    (hc : ∀ n a, (k n a : ℝ) = spinGroupSize (group n) a * ((1 + m n a) / 2))
    (h : ℕ → FieldStep) (hH : ∀ n, (h n).height (Fin.last (h n).depth) ≤ H)
    (i : ∀ n, Fin ((h n).depth + 1)) :
    Tendsto (fun n => |restrictedBlockPairMean (hN n) (spinGroupSlice (group n) (k n))
      (spinGroupSlice_nonempty (group n) (k n) (hk n)) (h n)
      (fun j => magneticBias (h n) (m n (group n j))) (i n) -
        (N n : ℝ)⁻¹ * ∑ j, magneticFieldLevel (h n) (m n (group n j)) (i n)|)
      atTop (𝓝 0) := by
  let g := fun n => (N n : ℝ)⁻¹ * (∑ j, constrainedFieldValue (h n) (m n (group n j))) -
    constrainedBlockValue (spinGroupSlice (group n) (k n)) (h n)
  apply tendsto_zero_of_pair_entropy _ g (fun n => abs_nonneg _)
    (magneticBlockGap_tendsto N hN hNlim group k hk m hr hm hc h hH)
  intro t ht n
  have he := restrictedBlockPairMean_comparison (hN n) (spinGroupSlice (group n) (k n))
    (spinGroupSlice_nonempty (group n) (k n) (hk n)) (h n)
    (fun j => magneticBias (h n) (m n (group n j))) (i n) ht
  rw [← magneticBlockGap_eq_biasedGap (hN n) (group n) (k n) (hk n) (m n)
    (fun a => (hm n a).trans_lt hr) (hc n) (h n)] at he
  exact he

end InvariantIsing

end

end OAI

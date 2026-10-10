import OAI.Probability.InvariantIsing.Magnetic.MagneticBlockError

namespace OAI

/-! Actual equivalence of constrained and canonical block values along
arbitrarily deep field partitions in a fixed bounded-height region. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

theorem magneticBlockGap_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNlim : Tendsto N atTop atTop)
    (group : ∀ n, Fin (N n) → A) (k : ℕ → A → ℕ)
    (hk : ∀ n a, k n a ≤ spinGroupSize (group n) a) (m : ℕ → A → ℝ)
    {r H : ℝ} (hr : r < 1) (hm : ∀ n a, |m n a| ≤ r)
    (hc : ∀ n a, (k n a : ℝ) = spinGroupSize (group n) a * ((1 + m n a) / 2))
    (h : ℕ → FieldStep) (hH : ∀ n, (h n).height (Fin.last (h n).depth) ≤ H) :
    Tendsto (fun n => (N n : ℝ)⁻¹ * (∑ i, constrainedFieldValue (h n) (m n (group n i))) -
      constrainedBlockValue (spinGroupSlice (group n) (k n)) (h n)) atTop (𝓝 0) := by
  let B := magneticUniformBiasBound H r
  let C := 2 * Real.exp (2 * B + 4 * H)
  have hC : 0 < C := mul_pos (by norm_num) (Real.exp_pos _)
  have hB (n : ℕ) (i : Fin (N n)) : |magneticBias (h n) (m n (group n i))| ≤ B :=
    magneticBias_uniform_bound (h n) hr (hm n _) (hH n)
  have hmi (n : ℕ) (a : A) : |m n a| < 1 := (hm n a).trans_lt hr
  let f := fun n => (N n : ℝ)⁻¹ * (∑ i, constrainedFieldValue (h n) (m n (group n i))) -
    constrainedBlockValue (spinGroupSlice (group n) (k n)) (h n)
  have hf (n : ℕ) : 0 ≤ f n :=
    (magneticBlockGap_estimate (hN n) (group n) (k n) (hk n) (m n)
      (hmi n) (hc n) (h n) (hB n) (hH n) (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 0)).1
  apply tendsto_zero_of_magneticBlockError N hNlim f hf C (Fintype.card A) hC
  intro ε hε t ht n
  have he := (magneticBlockGap_estimate (hN n) (group n) (k n) (hk n) (m n)
    (hmi n) (hc n) (h n) (hB n) (hH n) hε ht).2
  rw [normalized_magneticBlockError (hN n)] at he
  exact he

end InvariantIsing

end

end OAI

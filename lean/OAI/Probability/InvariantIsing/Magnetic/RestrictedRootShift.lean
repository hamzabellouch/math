import OAI.Probability.InvariantIsing.Magnetic.RestrictedKernelShift
import OAI.Probability.InvariantIsing.Magnetic.MagneticPairConvergence

namespace OAI

/-! Removal of the optimizing group biases from the actual shared-root
constrained spin-pair law. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped NNReal BigOperators Topology

namespace InvariantIsing

lemma kernel_gaussian_root_shift {N : ℕ} {X : Type*} [MeasurableSpace X]
    (κ : Kernel (Fin N → ℝ) X) [IsMarkovKernel κ] (v : ℝ≥0) (d : Fin N → ℝ)
    (hκ : ∀ z, κ (z + d) = κ z) :
    κ ∘ₘ Measure.pi (fun j => gaussianReal (d j) v) =
      κ ∘ₘ (vectorGaussianLaw N v : Measure (Fin N → ℝ)) := by
  ext T hT
  rw [Measure.bind_apply hT κ.aemeasurable, Measure.bind_apply hT κ.aemeasurable,
    ← (vectorGaussian_shift v d).map_eq, lintegral_map (g := fun w : Fin N → ℝ => d + w) (κ.measurable_coe hT)
      (measurable_const.add measurable_id)]
  apply lintegral_congr
  intro z
  rw [add_comm d z, hκ]

lemma restrictedLevelSpinPair_group_bias {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ)
    (h : FieldStep) (i : Fin (h.depth + 1)) :
    restrictedLevelSpinPair hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      h (fun j => bias (group j)) i =
    restrictedLevelSpinPair hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      h (fun _ => 0) i := by
  unfold restrictedLevelSpinPair
  exact kernel_gaussian_root_shift _ _ (fun j => bias (group j))
    (fun z => restrictedPairSpinKernel_group_shift hN group k hk bias _ _ _ _ i z)

lemma restrictedBlockPairMean_group_bias {N : ℕ} (hN : 0 < N)
    {A : Type*} [Fintype A] [DecidableEq A] (group : Fin N → A) (k : A → ℕ)
    (hk : ∀ a, k a ≤ spinGroupSize group a) (bias : A → ℝ)
    (h : FieldStep) (i : Fin (h.depth + 1)) :
    restrictedBlockPairMean hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      h (fun j => bias (group j)) i =
    restrictedBlockPairMean hN (spinGroupSlice group k) (spinGroupSlice_nonempty group k hk)
      h (fun _ => 0) i := by
  unfold restrictedBlockPairMean
  rw [restrictedLevelSpinPair_group_bias hN group k hk bias]

theorem magneticBlockPairGap_unbiased_tendsto {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (hNlim : Tendsto N atTop atTop)
    (group : ∀ n, Fin (N n) → A) (k : ℕ → A → ℕ)
    (hk : ∀ n a, k n a ≤ spinGroupSize (group n) a) (m : ℕ → A → ℝ)
    {r H : ℝ} (hr : r < 1) (hm : ∀ n a, |m n a| ≤ r)
    (hc : ∀ n a, (k n a : ℝ) = spinGroupSize (group n) a * ((1 + m n a) / 2))
    (h : ℕ → FieldStep) (hH : ∀ n, (h n).height (Fin.last (h n).depth) ≤ H)
    (i : ∀ n, Fin ((h n).depth + 1)) :
    Tendsto (fun n => |restrictedBlockPairMean (hN n) (spinGroupSlice (group n) (k n))
      (spinGroupSlice_nonempty (group n) (k n) (hk n)) (h n) (fun _ => 0) (i n) -
        (N n : ℝ)⁻¹ * ∑ j, magneticFieldLevel (h n) (m n (group n j)) (i n)|)
      atTop (𝓝 0) := by
  have he := magneticBlockPairGap_tendsto N hN hNlim group k hk m hr hm hc h hH i
  have hEq (n : ℕ) := restrictedBlockPairMean_group_bias (hN n) (group n) (k n) (hk n)
    (fun a => magneticBias (h n) (m n a)) (h n) (i n)
  simp_rw [hEq] at he
  exact he

end InvariantIsing

end

end OAI

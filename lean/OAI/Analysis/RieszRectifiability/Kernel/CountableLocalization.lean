import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.PartitionSecondMoments

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

theorem exists_common_localized_L2_limits {X : Type*} [MeasurableSpace X]
    (μ : ℕ → ℕ → Measure X) (ν : ℕ → Measure X)
    [∀ H j, IsFiniteMeasure (μ H j)] [∀ H, IsFiniteMeasure (ν H)]
    (ι : ℕ → ℕ → Type*) [∀ H k, Fintype (ι H k)]
    (s : ∀ H k, ι H k → Set X)
    (hs : ∀ H k i, MeasurableSet (s H k i))
    (hd : ∀ H k, Pairwise (Disjoint on s H k))
    (w : ℕ → ℕ → X → ℝ) (hw : ∀ H j, MemLp (w H j) 2 (μ H j))
    (B : ℕ → ℝ) (hB : ∀ H j, (∫ x, w H j x ^ 2 ∂μ H j) ≤ B H)
    (hm : ∀ H k i, Tendsto (fun j => (μ H j).real (s H k i)) atTop
      (𝓝 ((ν H).real (s H k i))))
    (hmpos : ∀ H k i, 0 < (ν H).real (s H k i))
    (hinter : ∀ H k l i t, Tendsto (fun j => (μ H j).real (s H k i ∩ s H l t)) atTop
      (𝓝 ((ν H).real (s H k i ∩ s H l t))))
    (δ : ℕ → ℕ → ℝ) (hδ : ∀ H, Tendsto (δ H) atTop (𝓝 0))
    (happrox : ∀ H k, ∀ᶠ j in atTop,
      (∫ x, (w H j x - partitionMean (μ H j) (s H k) (w H j) x) ^ 2 ∂μ H j) ≤ δ H k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ b : ∀ H k, ι H k → ℝ,
      (∀ H k i, Tendsto (fun j => cellMean ((μ H (φ j)).restrict (s H k i)) (w H (φ j)))
        atTop (𝓝 (b H k i))) ∧
      ∃ v : ∀ H, Lp ℝ 2 (ν H),
        (∀ H, Tendsto (fun k => (finiteStep_memLp (ν H) (s H k) (hs H k) (b H k)).toLp
          (finiteStep (s H k) (b H k))) atTop (𝓝 (v H))) ∧
        ∀ H, Tendsto (fun j => ∫ x, w H (φ j) x ^ 2 ∂μ H (φ j)) atTop (𝓝 (‖v H‖ ^ 2)) := by
  classical
  let A : Type _ := Σ H : ℕ, Σ k : ℕ, ι H k
  have hbounded : ∀ a : A, ∃ Z : ℝ, ∀ᶠ j in atTop,
      |cellMean ((μ a.1 j).restrict (s a.1 a.2.1 a.2.2)) (w a.1 j)| ≤ Z := by
    intro a
    let c := (ν a.1).real (s a.1 a.2.1 a.2.2) / 2
    have hc : 0 < c := half_pos (hmpos a.1 a.2.1 a.2.2)
    have hmass : ∀ᶠ j in atTop, c ≤ (μ a.1 j).real (s a.1 a.2.1 a.2.2) :=
      ((hm a.1 a.2.1 a.2.2).eventually
        (lt_mem_nhds (half_lt_self (hmpos a.1 a.2.1 a.2.2)))).mono (fun _ h => h.le)
    refine ⟨B a.1 / c + 1, ?_⟩
    filter_upwards [hmass] with j hj
    apply cellMean_abs_bound ((μ a.1 j).restrict (s a.1 a.2.1 a.2.2)) (w a.1 j)
      ((hw a.1 j).restrict _) c (B a.1) hc
    · simpa only [Measure.real, Measure.restrict_apply_univ] using! hj
    · exact (setIntegral_le_integral (hw a.1 j).integrable_sq
        (Filter.Eventually.of_forall fun x => sq_nonneg (w a.1 j x))).trans (hB a.1 j)
  obtain ⟨b, φ, hφ, hcoeff⟩ := exists_common_subsequence_of_eventual_bounds
    (fun j (a : A) => cellMean ((μ a.1 j).restrict (s a.1 a.2.1 a.2.2)) (w a.1 j)) hbounded
  let b' : ∀ H k, ι H k → ℝ := fun H k i => b ⟨H, k, i⟩
  have hb : ∀ H k i, Tendsto
      (fun j => cellMean ((μ H (φ j)).restrict (s H k i)) (w H (φ j))) atTop (𝓝 (b' H k i)) :=
    fun H k i => hcoeff ⟨H, k, i⟩
  have hL2 : ∀ H, ∃ v : Lp ℝ 2 (ν H),
      Tendsto (fun k => (finiteStep_memLp (ν H) (s H k) (hs H k) (b' H k)).toLp
        (finiteStep (s H k) (b' H k))) atTop (𝓝 v) := by
    intro H
    apply exists_L2_limit_of_partition_approximations (fun j => μ H (φ j)) (ν H)
      (ι H) (s H) (hs H) (hd H) (fun j => w H (φ j)) (fun j => hw H (φ j))
      (fun j k i => cellMean ((μ H (φ j)).restrict (s H k i)) (w H (φ j)))
      (b' H) (hb H) (fun k i => (hm H k i).comp hφ.tendsto_atTop)
      (fun k l i t => (hinter H k l i t).comp hφ.tendsto_atTop) (δ H) (hδ H)
    intro k
    simpa only [partitionMean_eq_finiteStep] using! hφ.tendsto_atTop.eventually (happrox H k)
  choose v hv using hL2
  refine ⟨φ, hφ, b', hb, v, hv, ?_⟩
  intro H
  apply partition_approximation_second_moments_tendsto (fun j => μ H (φ j)) (ν H)
    (ι H) (s H) (hs H) (hd H) (fun j => w H (φ j)) (fun j => hw H (φ j))
    (fun j k i => cellMean ((μ H (φ j)).restrict (s H k i)) (w H (φ j)))
    (b' H) (hb H) (fun k i => (hm H k i).comp hφ.tendsto_atTop)
    (δ H) (hδ H) _ (v H) (hv H)
  intro k
  simpa only [partitionMean_eq_finiteStep] using! hφ.tendsto_atTop.eventually (happrox H k)

end

end RieszRectifiability

end OAI

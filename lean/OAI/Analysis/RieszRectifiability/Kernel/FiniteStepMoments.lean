import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CellMeanSubsequence

namespace OAI

/-!
# Moments of finite-step functions

Finite sums of cell indicators reduce first and second moments to weighted cell masses.
For disjoint cells, convergence of the coefficients and masses gives convergence of the
second moments and vanishing squared approximation error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]

def finiteStep (s : ι → Set X) (a : ι → ℝ) : X → ℝ := by
  classical
  exact fun x => ∑ i, (s i).indicator (fun _ => a i) x

omit [MeasurableSpace X] in
theorem finiteStep_eq_cell (s : ι → Set X) (a : ι → ℝ)
    (hd : Pairwise (Disjoint on s)) (i : ι) (x : X) (hx : x ∈ s i) :
    finiteStep s a x = a i := by
  classical
  unfold finiteStep
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    have hxj : x ∉ s j := fun hj => (Set.disjoint_left.mp (hd hji)) hj hx
    exact indicator_of_notMem hxj _
  · simp

theorem partitionMean_eq_finiteStep (μ : Measure X) (s : ι → Set X) (w : X → ℝ) :
    partitionMean μ s w = finiteStep s (fun i => cellMean (μ.restrict (s i)) w) := rfl

omit [MeasurableSpace X] in
theorem finiteStep_sq (s : ι → Set X) (a : ι → ℝ)
    (hd : Pairwise (Disjoint on s)) :
    (fun x => finiteStep s a x ^ 2) = finiteStep s (fun i => a i ^ 2) := by
  classical
  funext x
  by_cases hx : ∃ i, x ∈ s i
  · obtain ⟨i, hi⟩ := hx
    rw [finiteStep_eq_cell s a hd i x hi, finiteStep_eq_cell s _ hd i x hi]
  · have hi : ∀ i, x ∉ s i := fun i h => hx ⟨i, h⟩
    simp [finiteStep, hi]

omit [MeasurableSpace X] in
theorem finiteStep_sub (s : ι → Set X) (a b : ι → ℝ) :
    finiteStep s a - finiteStep s b = finiteStep s (fun i => a i - b i) := by
  classical
  funext x
  change (∑ i, (s i).indicator (fun _ => a i) x) -
    (∑ i, (s i).indicator (fun _ => b i) x) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hx : x ∈ s i <;> simp [hx]

theorem integral_finiteStep (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i)) (a : ι → ℝ) :
    (∫ x, finiteStep s a x ∂μ) = ∑ i, μ.real (s i) * a i := by
  classical
  unfold finiteStep
  rw [integral_finsetSum _ (fun i _ => (integrable_const (a i)).indicator (hs i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (hs i), setIntegral_const, smul_eq_mul]

theorem integral_finiteStep_sq (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (a : ι → ℝ) :
    (∫ x, finiteStep s a x ^ 2 ∂μ) = ∑ i, μ.real (s i) * a i ^ 2 := by
  rw [finiteStep_sq s a hd]
  exact integral_finiteStep μ s hs _

theorem integral_finiteStep_sub_sq (μ : Measure X) [IsFiniteMeasure μ]
    (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (a b : ι → ℝ) :
    (∫ x, (finiteStep s a x - finiteStep s b x) ^ 2 ∂μ) =
      ∑ i, μ.real (s i) * (a i - b i) ^ 2 := by
  have heq : (fun x => finiteStep s a x - finiteStep s b x) =
      finiteStep s (fun i => a i - b i) := finiteStep_sub s a b
  simp_rw [congrFun heq]
  exact integral_finiteStep_sq μ s hs hd _

theorem finiteStep_second_moment_tendsto (μ : ℕ → Measure X)
    [∀ j, IsFiniteMeasure (μ j)] (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (a : ℕ → ι → ℝ) (b M : ι → ℝ)
    (ha : ∀ i, Tendsto (fun j => a j i) atTop (𝓝 (b i)))
    (hm : ∀ i, Tendsto (fun j => (μ j).real (s i)) atTop (𝓝 (M i))) :
    Tendsto (fun j => ∫ x, finiteStep s (a j) x ^ 2 ∂μ j) atTop
      (𝓝 (∑ i, M i * b i ^ 2)) := by
  simp_rw [integral_finiteStep_sq _ s hs hd]
  exact tendsto_finsetSum _ fun i _ => (hm i).mul ((ha i).pow 2)

theorem finiteStep_squared_error_tendsto_zero (μ : ℕ → Measure X)
    [∀ j, IsFiniteMeasure (μ j)] (s : ι → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (a : ℕ → ι → ℝ) (b M : ι → ℝ)
    (ha : ∀ i, Tendsto (fun j => a j i) atTop (𝓝 (b i)))
    (hm : ∀ i, Tendsto (fun j => (μ j).real (s i)) atTop (𝓝 (M i))) :
    Tendsto (fun j => ∫ x, (finiteStep s (a j) x - finiteStep s b x) ^ 2 ∂μ j)
      atTop (𝓝 0) := by
  simp_rw [integral_finiteStep_sub_sq _ s hs hd]
  have h := tendsto_finsetSum Finset.univ
    (fun i _ => (hm i).mul (((ha i).sub (tendsto_const_nhds (x := b i))).pow 2))
  simpa only [sub_self, zero_pow two_ne_zero, mul_zero, Finset.sum_const_zero] using! h

end

end RieszRectifiability

end OAI

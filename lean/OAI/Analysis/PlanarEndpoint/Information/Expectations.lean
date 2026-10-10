import OAI.Analysis.PlanarEndpoint.Extension
import OAI.Analysis.PlanarEndpoint.Fourier

namespace OAI

/-! Finite information laws, entropy and convergence of probability measures. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace PlanarEndpoint.TransverseInformation

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω]

def informationClip (A : ℝ) (x : ℝ) : ℝ := min (max x 0) (max A 0)

lemma informationClip_nonneg (A x : ℝ) : 0 ≤ informationClip A x :=
  le_min (le_max_right _ _) (le_max_right _ _)

lemma informationClip_le_bound (A x : ℝ) : informationClip A x ≤ max A 0 :=
  min_le_right _ _

lemma informationClip_eq {A x : ℝ} (hx : 0 ≤ x) (hA : x ≤ A) :
    informationClip A x = x := by
  simp [informationClip, max_eq_left hx, max_eq_left (hx.trans hA), min_eq_left hA]

lemma continuous_informationClip (A : ℝ) : Continuous (informationClip A) :=
  (continuous_id.max continuous_const).min continuous_const

def clippedInformation (A : ℝ) (f : Ω → ℝ) (hf : Continuous f) : Ω →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => informationClip A (f x), (continuous_informationClip A).comp hf⟩
    (2 * max A 0) (by
      intro x y
      rw [Real.dist_eq, abs_le]
      have hx0 := informationClip_nonneg A (f x)
      have hy0 := informationClip_nonneg A (f y)
      have hxb := informationClip_le_bound A (f x)
      have hyb := informationClip_le_bound A (f y)
      change -(2 * max A 0) ≤ informationClip A (f x) - informationClip A (f y) ∧
        informationClip A (f x) - informationClip A (f y) ≤ 2 * max A 0
      constructor <;> linarith [le_max_right A 0])

lemma informationClip_error_le {A x : ℝ} (hA : 0 ≤ A) (hx : 0 ≤ x) :
    |x - informationClip A x| ≤ if A < x then x else 0 := by
  classical
  by_cases h : A < x
  · simp only [h, ↓reduceIte, informationClip, max_eq_left hx, max_eq_left hA,
      min_eq_right h.le]
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [informationClip_eq hx (le_of_not_gt h)]
    simp only [sub_self, abs_zero, h, ↓reduceIte, le_refl]

lemma integral_informationClip_error_le {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : Continuous f) (hfi : Integrable f μ)
    (hfn : 0 ≤ᵐ[μ] f) {A : ℝ} (hA : 0 ≤ A) :
    |(∫ x, f x ∂μ) - ∫ x, clippedInformation A f hf x ∂μ| ≤
      ∫ x, if A < f x then f x else 0 ∂μ := by
  have hc := (clippedInformation A f hf).integrable (μ := μ)
  have ht : Integrable (fun x => if A < f x then f x else 0) μ := by
    exact hfi.indicator (isOpen_lt continuous_const hf).measurableSet
  rw [← integral_sub hfi hc, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  apply integral_mono_ae (hfi.sub hc).norm ht
  filter_upwards [hfn] with x hx
  exact informationClip_error_le hA hx

theorem expected_information_tendsto {μ : ProbabilityMeasure Ω}
    {μs : ℕ → ProbabilityMeasure Ω} (hμ : Tendsto μs atTop (𝓝 μ))
    {f : Ω → ℝ} (hf : Continuous f)
    (hfi : ∀ n, Integrable f (μs n : Measure Ω))
    (hfn : ∀ n, 0 ≤ᵐ[(μs n : Measure Ω)] f)
    (hfμ : 0 ≤ᵐ[(μ : Measure Ω)] f)
    {C : ℝ} (hC : ∀ᵐ x ∂(μ : Measure Ω), f x ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → ∀ n,
      (∫ x, if A < f x then f x else 0 ∂(μs n : Measure Ω)) < ε) :
    Integrable f (μ : Measure Ω) ∧
    Tendsto (fun n => ∫ x, f x ∂(μs n : Measure Ω)) atTop
      (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  have heq : ∀ A : ℝ, C ≤ A →
      (fun x => clippedInformation A f hf x) =ᵐ[(μ : Measure Ω)] f := by
    intro A hA
    filter_upwards [hfμ, hC] with x hx0 hxC
    exact informationClip_eq hx0 (hxC.trans hA)
  refine ⟨((clippedInformation C f hf).integrable (μ := (μ : Measure Ω))).congr
    (heq C le_rfl), ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨A₀, hA₀⟩ := htail (ε/2) (half_pos hε)
  let A := max (max A₀ C) 0
  have hA0 : 0 ≤ A := le_max_right _ _
  have hAA : A₀ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hAC : C ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  have hc := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
    (clippedInformation A f hf)
  have hlim : (∫ x, clippedInformation A f hf x ∂(μ : Measure Ω)) =
      (∫ x, f x ∂(μ : Measure Ω)) := integral_congr_ae (heq A hAC)
  rw [hlim] at hc
  filter_upwards [hc.eventually (Metric.ball_mem_nhds _ (half_pos hε))] with n hn
  have hn' : dist (∫ x, clippedInformation A f hf x ∂(μs n : Measure Ω))
      (∫ x, f x ∂(μ : Measure Ω)) < ε/2 := hn
  have herr := integral_informationClip_error_le hf (hfi n) (hfn n) hA0
  have htailn := hA₀ A hAA n
  calc
    dist (∫ x, f x ∂(μs n : Measure Ω)) (∫ x, f x ∂(μ : Measure Ω)) ≤
        dist (∫ x, f x ∂(μs n : Measure Ω))
          (∫ x, clippedInformation A f hf x ∂(μs n : Measure Ω)) +
        dist (∫ x, clippedInformation A f hf x ∂(μs n : Measure Ω))
          (∫ x, f x ∂(μ : Measure Ω)) := dist_triangle _ _ _
    _ ≤ (∫ x, if A < f x then f x else 0 ∂(μs n : Measure Ω)) +
        dist (∫ x, clippedInformation A f hf x ∂(μs n : Measure Ω))
          (∫ x, f x ∂(μ : Measure Ω)) := by
      apply add_le_add
      · simpa only [Real.dist_eq] using herr
      · exact le_rfl
    _ < ε := by linarith

end PlanarEndpoint.TransverseInformation
end

end OAI

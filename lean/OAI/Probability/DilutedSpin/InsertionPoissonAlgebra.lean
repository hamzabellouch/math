import OAI.Probability.DilutedSpin.UpperInsertion

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

lemma poisson_average_bound (ρ : ℝ≥0) (f : ℕ → ℝ) {B D : ℝ}
    (h : ∀ k,|f k|≤B+D*k) : |∫ k,f k ∂poissonMeasure ρ|≤B+D*ρ := by
  have hg : Integrable (fun k : ℕ => B+D*k) (poissonMeasure ρ) :=
    (integrable_const _).add ((poisson_integrable_count ρ).const_mul D)
  have hh := norm_integral_le_of_norm_le (f := f) hg (ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs] using h k))
  simpa only [Real.norm_eq_abs,integral_add (integrable_const _) ((poisson_integrable_count ρ).const_mul D),
    integral_const,probReal_univ,smul_eq_mul,one_mul,integral_const_mul,poisson_mean] using hh

lemma poisson_average_integrable (ρ : ℝ≥0) (f : ℕ → ℝ) {B D : ℝ}
    (h : ∀ k,|f k|≤B+D*k) : Integrable f (poissonMeasure ρ) := by
  apply ((integrable_const B).add ((poisson_integrable_count ρ).const_mul D)).mono'
    (measurable_of_countable f).aestronglyMeasurable
  exact ae_of_all _ (fun k => by simpa only [Real.norm_eq_abs,Pi.add_apply] using h k)

lemma double_limit_two (a f g : ℕ → ℕ → ℝ) {B C : ℝ}
    (ha : ∀ L n,0≤a L n) (hf0 : ∀ L n,0≤f L n) (hg0 : ∀ L n,0≤g L n)
    (hf : ∀ L n,f L n≤B) (hg : ∀ L n,g L n≤C)
    (h : ∀ L n,a L n≤f L n+g L n)
    (hflim : Tendsto (fun L => limsup (f L) atTop) atTop (𝓝 0))
    (hglim : Tendsto (fun L => limsup (g L) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (a L) atTop) atTop (𝓝 0) := by
  have hfB L : IsBoundedUnder (·≤·) atTop (f L) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (hf L))
  have hgB L : IsBoundedUnder (·≤·) atTop (g L) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall (hg L))
  have haB L : IsBoundedUnder (·≤·) atTop (a L) :=
    isBoundedUnder_of_eventually_le (a := B+C) (Eventually.of_forall (fun n => (h L n).trans (add_le_add (hf L n) (hg L n))))
  apply squeeze_zero (fun L => le_limsup_of_frequently_le ((Eventually.of_forall (ha L)).frequently) (haB L))
    (fun L => ?_) (by simpa using hflim.add hglim)
  have hfLower := isBoundedUnder_of_eventually_ge (f := atTop) (Eventually.of_forall (hf0 L))
  have hgLower := isBoundedUnder_of_eventually_ge (f := atTop) (Eventually.of_forall (hg0 L))
  refine (limsup_le_limsup (Eventually.of_forall (h L))
    (isBoundedUnder_of_eventually_ge (Eventually.of_forall (ha L))).isCoboundedUnder_le
    (isBoundedUnder_of_eventually_le (a := B+C)
      (Eventually.of_forall (fun index => add_le_add (hf L index) (hg L index))))).trans ?_
  exact limsup_add_le hfLower (hfB L) hgLower.isCoboundedUnder_le (hgB L)

namespace UniversalDictionary
open ConcreteReservoir

noncomputable def insertionPoisson {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
    {p : ℕ} (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ)
    (μ : (k : ℕ) → Measure (X k)) (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) (ρ : ℝ≥0) : ℝ :=
  ∫ k, ∫ x,reservoirInsertionOn M C H N L u (F k x) ∂μ k ∂poissonMeasure ρ

noncomputable def trialPoisson {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
    (L : ℕ) (ζ : Hierarchy (L+1)) (μ : (k : ℕ) → Measure (X k))
    (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) (ρ : ℝ≥0) : ℝ :=
  ∫ k, ∫ x,trialLog L ζ (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F k x)) ∂μ k ∂poissonMeasure ρ

lemma insertionPoisson_comparison_bound
    {ι X : ℕ → Type} [∀ k,Fintype (ι k)] [∀ k,MeasurableSpace (X k)]
    {p : ℕ} (M : Model p) (C H : ℝ) (N L : ℕ) (u : Spec L×ℕ → ℝ)
    (μ : (k : ℕ) → Measure (X k)) [∀ k,IsProbabilityMeasure (μ k)]
    (F : (k : ℕ) → X k → (ι k → Spin) → ℝ) {B D : ℝ}
    (hF : ∀ k,∀ᵐ x ∂μ k,∀ s,|F k x s|≤B+D*k) (ρ : ℝ≥0) :
    |insertionPoisson M C H N L u μ F ρ-
      trialPoisson L (reservoirTrialLaw M C H N L u) μ F ρ| ≤
      ∫ k,|(∫ x,reservoirInsertionOn M C H N L u (F k x) ∂μ k)-
        (∫ x,trialLog L (reservoirTrialLaw M C H N L u)
          (fun i => gridExponents L i.castSucc) (FiniteLaw.spinLog (F k x)) ∂μ k)| ∂poissonMeasure ρ := by
  have h1 k := abs_integral_le_bound_ae (μ k) ((hF k).mono (fun x hx =>
    reservoirInsertionOn_bound M C H N L u (F k x) hx))
  have h2 k := abs_integral_le_bound_ae (μ k) ((hF k).mono (fun x hx =>
    (trialLog_continuous_bound L (FiniteLaw.spinLog (F k x)) (FiniteLaw.spinLog_continuous (F k x))
      (FiniteLaw.spinLog_bound (F k x) hx) _ (fun i => gridExponents_pos L i.castSucc)).2
        (reservoirTrialLaw M C H N L u)))
  unfold insertionPoisson trialPoisson
  rw [← integral_sub (poisson_average_integrable ρ _ h1) (poisson_average_integrable ρ _ h2)]
  exact abs_integral_le_integral_abs

end UniversalDictionary
end DilutedSpinGlass

end

end OAI

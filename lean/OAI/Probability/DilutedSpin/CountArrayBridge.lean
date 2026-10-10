import OAI.Probability.DilutedSpin.InsertionPoint

namespace OAI

section
namespace DilutedSpinGlass.PhysicalRoot
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory HeterogeneousMarks KernelTower SizeCoupling
open scoped BigOperators NNReal
variable {X Y I : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {A : I → Type} [∀ i,Fintype (A i)] {N p L k l : ℕ}

noncomputable def arrayRoot (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (a : Fin l → I) (x : Fin k → X) (h : RootPath Y N)
    (j : Fin k → Fin p → Fin N) (w : Fin l → Fin N) : ℝ :=
  spinRoot (fun t => Q (a t)) m (fun t => theta (x t))
    (fun t => field (rootArray N h t)) j w (fun t => ψ (a t))

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma arrayRoot_measurable (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθ : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hh : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    (a : Fin l → I) (j : Fin k → Fin p → Fin N) (w : Fin l → Fin N) :
    Measurable (fun z : (Fin k → X) × RootPath Y N => arrayRoot theta field Q m ψ a z.1 z.2 j w) := by
  apply measurable_spinRoot
  · intro t σ; exact (hθ σ).comp ((measurable_pi_apply t).comp measurable_fst)
  · intro t; exact hh.comp ((measurable_rootArray N t).comp measurable_snd)

omit [MeasurableSpace X] [MeasurableSpace Y] [Countable I]
  [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma arrayRoot_bound (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D)
    (a : Fin l → I) (x : Fin k → X) (h : RootPath Y N)
    (j : Fin k → Fin p → Fin N) (w : Fin l → Fin N) :
    |arrayRoot theta field Q m ψ a x h j w|≤H*N+C*k+D*l :=
  spinRoot_bound _ m hm _ _ j w _ (fun _ σ => hθ _ σ) (fun _ => hh _) (fun _ σ a => hψ _ σ a)

omit [Countable I] [MeasurableSingletonClass I] in
lemma countedMean_eq_arrays [NeZero N]
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (ν : Measure I) [IsProbabilityMeasure ν]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ) (k l : ℕ) :
    countedMean (N := N) μ ξ ν theta field Q m ψ k l =
      ∫ a : Fin l → I,∫ x : Fin k → X,∫ h : RootPath Y N,
        (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect (fun j =>
          (FiniteLaw.uniform : FiniteLaw (Fin l → Fin N)).expect
            (fun w => arrayRoot theta field Q m ψ a x h j w))
        ∂rootLaw N (fun _ => ξ) ∂Measure.pi (fun _ : Fin k => μ)
        ∂Measure.pi (fun _ : Fin l => ν) := by
  unfold countedMean spinMean
  simp only [FiniteLaw.pi_uniform]
  let F := fun (a : Fin l → I) (x : Fin k → X) => ∫ h : RootPath Y N,
    (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect (fun j =>
      (FiniteLaw.uniform : FiniteLaw (Fin l → Fin N)).expect
        (fun w => arrayRoot theta field Q m ψ a x h j w)) ∂rootLaw N (fun _ => ξ)
  change (∫ a : RootPath I l,∫ x : RootPath X k,F (rootArray l a) (rootArray k x)
    ∂rootLaw k (fun _ => μ) ∂rootLaw l (fun _ => ν)) =
    ∫ a : Fin l → I,∫ x : Fin k → X,F a x ∂Measure.pi (fun _ : Fin k => μ)
      ∂Measure.pi (fun _ : Fin l => ν)
  rw [integral_rootArray_eq_pi ν l (fun a => ∫ x : RootPath X k,F a (rootArray k x) ∂rootLaw k (fun _ => μ))]
  apply integral_congr_ae
  filter_upwards [] with a
  exact integral_rootArray_eq_pi μ k (F a)

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I] in
lemma arrayRoot_swap_expect [NeZero N]
    (μ : Measure X) [IsProbabilityMeasure μ] (ξ : Measure Y) [IsProbabilityMeasure ξ]
    (theta : X → InteractionSample p) (field : Y → ℝ)
    (hθm : ∀ σ,Measurable (fun x => (theta x).1 σ)) (hhm : Measurable field)
    (Q : (i : I) → Fin (L+1) → FiniteLaw (A i)) (m : Fin (L+1) → ℝ) (hm : ∀ i,0 < m i)
    (ψ : (i : I) → Spin → FinitePath (A i) (L+1) → ℝ)
    {C H D : ℝ} (hθ : ∀ x σ,|(theta x).1 σ|≤C) (hh : ∀ y,|field y|≤H)
    (hψ : ∀ i σ a,|Real.log (ψ i σ a)|≤D) (a : Fin l → I) :
    (FiniteLaw.uniform : FiniteLaw (Fin l → Fin N)).expect (fun w =>
      ∫ x : Fin k → X,(FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect
        (fun j => ∫ h : RootPath Y N,arrayRoot theta field Q m ψ a x h j w ∂rootLaw N (fun _ => ξ))
      ∂Measure.pi (fun _ : Fin k => μ)) =
    ∫ x : Fin k → X,∫ h : RootPath Y N,
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin p → Fin N)).expect (fun j =>
        (FiniteLaw.uniform : FiniteLaw (Fin l → Fin N)).expect (fun w => arrayRoot theta field Q m ψ a x h j w))
      ∂rootLaw N (fun _ => ξ) ∂Measure.pi (fun _ : Fin k => μ) := by
  exact FiniteLaw.expect_double_integral FiniteLaw.uniform FiniteLaw.uniform
    (Measure.pi (fun _ : Fin k => μ)) (rootLaw N (fun _ => ξ))
    (arrayRoot theta field Q m ψ a)
    (arrayRoot_measurable theta field hθm hhm Q m ψ a)
    (arrayRoot_bound theta field Q m hm ψ hθ hh hψ a)

end DilutedSpinGlass.PhysicalRoot

end

end OAI

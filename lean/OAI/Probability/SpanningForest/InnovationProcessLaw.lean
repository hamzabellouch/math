import OAI.Probability.SpanningForest.InnovationFiniteGaussian
import OAI.Probability.SpanningForest.BrownianFamilyIdentification
import OAI.Probability.SpanningForest.ContinuousPathLaw

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem336.InnovationProcessLaw

theorem identDistrib_nnInnovation
    {I Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (X : Ω → I → ℝ) (B : I → ℝ≥0 → Ω → ℝ) (b : I → ℝ → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P) (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (hb : ∀ i, Measurable (Function.uncurry (b i)))
    (hXrange : ∀ ω i, X ω i ∈ Set.Icc (0 : ℝ) 1)
    (hbrange : ∀ i t ω, b i t ω ∈ Set.Icc (0 : ℝ) 1)
    (hM : ∀ i, Martingale (Innovation.nnInnovation (fun ω => X ω i) (B i) (b i)) F P)
    (hF : ∀ u, F u ≤ MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance) :
    IdentDistrib
      (fun ω i t => Innovation.nnInnovation (fun ω => X ω i) (B i) (b i) t ω)
      (fun ω i t => B i t ω) P P := by
  classical
  let W := fun i => Innovation.nnInnovation (fun ω => X ω i) (B i) (b i)
  apply BrownianFamilyIdentification.identDistrib_brownian_family F W B
    (fun i t => (hM i).stronglyMeasurable t |>.measurable) hBm
  · intro i
    filter_upwards [(hB i).eval_zero_ae_eq_zero] with ω hω
    simpa [W, Innovation.nnInnovation_apply] using hω
  · exact hB
  · exact hI
  · intro S s t hst A hA θ
    let θ' : I → ℝ := fun i => if hi : i ∈ S then θ ⟨i, hi⟩ else 0
    have heval (i : S) : θ' i = θ i := by simp [θ', i.property]
    have hscalar := InnovationFiniteGaussian.restricted_characteristic_nnInnovation
      P F X B b hB hBm hI hX hXB hb hXrange hbrange hM hF S θ' s (s + (t - s))
      (InnovationPhaseRecurrence.timeGrid s (t - s))
      (InnovationPhaseRecurrence.timeGrid_mono s (t - s))
      (InnovationPhaseRecurrence.timeGrid_zero s (t - s))
      (InnovationPhaseRecurrence.timeGrid_finish s (t - s))
      ((t - s : ℝ≥0) : ℝ) (NNReal.coe_nonneg _)
      (fun n k _ => InnovationPhaseRecurrence.timeGrid_succ_sub s (t - s) n k) hA
    rw [add_tsub_cancel_of_le hst] at hscalar
    have hsum (ω : Ω) : (∑ i ∈ S, θ' i * (W i t ω - W i s ω)) =
        ∑ i : S, θ i * (W i t ω - W i s ω) := by
      rw [← Finset.sum_coe_sort S (fun i => θ' i * (W i t ω - W i s ω))]
      simp only [heval]
    have hsq : (∑ i ∈ S, θ' i ^ 2) = ‖θ‖ ^ 2 := by
      rw [← Finset.sum_coe_sort S (fun i => θ' i ^ 2), EuclideanSpace.real_norm_sq_eq]
      simp only [heval]
    change (∫ ω in A, Complex.exp (((∑ i ∈ S, θ' i *
      (W i t ω - W i s ω) : ℝ) : ℂ) * Complex.I) ∂P) = _ at hscalar
    simp_rw [hsum] at hscalar
    rw [hsq] at hscalar
    convert hscalar using 1
    simp only [BrownianFamilyIdentification.charFun_vectorGaussian,
      RCLike.real_smul_eq_coe_mul, Measure.real, mul_comm]
    rw [Complex.ofReal_exp]
    congr 2
    push_cast
    ring

theorem continuous_nnInnovation_ae
    {I Ω : Type*} [Countable I] [MeasurableSpace Ω]
    {P : Measure Ω} (X : Ω → I → ℝ) (B : I → ℝ≥0 → Ω → ℝ)
    (b : I → ℝ → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hb : ∀ i, Measurable (Function.uncurry (b i)))
    (hbrange : ∀ i t ω, b i t ω ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∀ i, Continuous
      (fun t => Innovation.nnInnovation (fun ω => X ω i) (B i) (b i) t ω) := by
  have hc := ae_all_iff.mpr (fun i => (hB i).cont)
  filter_upwards [hc] with ω hω
  intro i
  have hbound : ∀ t ω, ‖b i t ω‖ ≤ 1 := by
    intro t ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hbrange i t ω).1]
    exact (hbrange i t ω).2
  have hi : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, b i s ω) :=
    intervalIntegral.continuous_primitive
      (fun u v => Innovation.intervalIntegrable_field (hb i) hbound u v ω) 0
  simp only [Innovation.nnInnovation_apply]
  exact ((continuous_subtype_val.mul continuous_const).add (hω i)).sub
    (hi.comp continuous_subtype_val)

theorem exists_continuous_innovation_with_law
    {I Ω : Type*} [Countable I] [mΩ : MeasurableSpace Ω]
    [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]
    [StandardBorelSpace C(ℝ≥0, ℝ)]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ)
    (X : Ω → I → ℝ) (B : I → ℝ≥0 → Ω → ℝ) (b : I → ℝ → Ω → ℝ)
    (hB : ∀ i, IsBrownianReal (B i) P) (hBm : ∀ i t, Measurable (B i t))
    (hI : iIndepFun (fun i ω t => B i t ω) P) (hX : Measurable X)
    (hXB : IndepFun X (fun ω i t => B i t ω) P)
    (hb : ∀ i, Measurable (Function.uncurry (b i)))
    (hXrange : ∀ ω i, X ω i ∈ Set.Icc (0 : ℝ) 1)
    (hbrange : ∀ i t ω, b i t ω ∈ Set.Icc (0 : ℝ) 1)
    (hM : ∀ i, Martingale (Innovation.nnInnovation (fun ω => X ω i) (B i) (b i)) F P)
    (hF : ∀ u, F u ≤ MeasurableSpace.comap (fun ω (p : I × Set.Iic u) =>
      (p.2 : ℝ≥0) * X ω p.1 + B p.1 p.2 ω) inferInstance)
    (ν : Measure (I → C(ℝ≥0, ℝ)))
    (hBlaw : HasLaw (fun ω i t => B i t ω) (ν.map ContinuousPathLaw.raw) P) :
    ∃ W : Ω → I → C(ℝ≥0, ℝ), Measurable W ∧
      (fun ω => ContinuousPathLaw.raw (W ω)) =ᵐ[P]
        (fun ω i t => Innovation.nnInnovation (fun ω => X ω i) (B i) (b i) t ω) ∧
      HasLaw W ν P := by
  have hd := identDistrib_nnInnovation P F X B b (fun i => (hB i).toIsPreBrownianReal)
    hBm hI hX hXB hb hXrange hbrange hM hF
  obtain ⟨W, hW, heq, hlaw⟩ := ContinuousPathLaw.exists_measurable_lift_with_law
    (fun ω i t => Innovation.nnInnovation (fun ω => X ω i) (B i) (b i) t ω)
    (fun i t => (((hM i).stronglyMeasurable t).measurable.mono (F.le t) le_rfl).aemeasurable)
    (continuous_nnInnovation_ae X B b hB hb hbrange)
    (hd.map_eq.trans hBlaw.map_eq)
  exact ⟨W, hW, heq, ⟨hW.aemeasurable, hlaw⟩⟩

end Problem336.InnovationProcessLaw

end

end OAI

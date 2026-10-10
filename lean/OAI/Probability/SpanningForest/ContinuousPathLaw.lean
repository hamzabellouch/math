import Mathlib

namespace OAI

noncomputable section
open MeasureTheory

namespace Problem336.ContinuousPathLaw

variable {I T : Type*} [TopologicalSpace T]
  [TopologicalSpace.SeparableSpace T] [Nonempty T]
  [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
  [StandardBorelSpace C(T, ℝ)]

def raw (x : I → C(T, ℝ)) : I → T → ℝ := fun i t => x i t

def denseEval (x : I → C(T, ℝ)) : I → ℕ → ℝ :=
  fun i n => x i (TopologicalSpace.denseSeq T n)

omit [TopologicalSpace.SeparableSpace T] [Nonempty T]
  [StandardBorelSpace C(T, ℝ)] in
lemma measurable_raw : Measurable (raw (I := I) (T := T)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro t
  exact (show Continuous (fun x : C(T, ℝ) => x t) by fun_prop).measurable.comp
    (measurable_pi_apply i)

omit [StandardBorelSpace C(T, ℝ)] in
lemma measurable_denseEval : Measurable (denseEval (I := I) (T := T)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro n
  exact (show Continuous (fun x : C(T, ℝ) =>
    x (TopologicalSpace.denseSeq T n)) by fun_prop).measurable.comp (measurable_pi_apply i)

omit [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]
  [StandardBorelSpace C(T, ℝ)] in
lemma denseEval_injective : Function.Injective (denseEval (I := I) (T := T)) := by
  intro x y h
  funext i
  apply DFunLike.coe_injective
  apply (TopologicalSpace.denseRange_denseSeq T).equalizer (x i).continuous (y i).continuous
  funext n
  exact congrFun (congrFun h i) n

lemma measurableEmbedding_denseEval [Countable I] :
    MeasurableEmbedding (denseEval (I := I) (T := T)) :=
  measurable_denseEval.measurableEmbedding denseEval_injective

theorem measure_eq_of_raw [Countable I] {μ ν : Measure (I → C(T, ℝ))}
    (h : μ.map raw = ν.map raw) : μ = ν := by
  let r : (I → T → ℝ) → I → ℕ → ℝ :=
    fun x i n => x i (TopologicalSpace.denseSeq T n)
  have hr : Measurable r := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro n
    exact (measurable_pi_apply (TopologicalSpace.denseSeq T n)).comp (measurable_pi_apply i)
  apply measurableEmbedding_denseEval.map_injective
  calc
    μ.map denseEval = (μ.map raw).map r := (Measure.map_map hr measurable_raw).symm
    _ = (ν.map raw).map r := congrArg (Measure.map r) h
    _ = ν.map denseEval := Measure.map_map hr measurable_raw

theorem measurable_iff_evaluation [Countable I] {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → I → C(T, ℝ)} :
    Measurable X ↔ ∀ i t, Measurable (fun ω => X ω i t) := by
  constructor
  · intro h i t
    exact (measurable_pi_apply t).comp
      ((measurable_pi_apply i).comp (measurable_raw.comp h))
  · intro h
    apply measurableEmbedding_denseEval.measurable_comp_iff.mp
    exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun n =>
      h i (TopologicalSpace.denseSeq T n)

theorem law_eq_of_raw [Countable I] {Ω₁ Ω₂ : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ : Measure Ω₁} {ν : Measure Ω₂}
    {X : Ω₁ → I → C(T, ℝ)} {Y : Ω₂ → I → C(T, ℝ)}
    (hX : Measurable X) (hY : Measurable Y)
    (h : μ.map (fun ω => raw (X ω)) = ν.map (fun ω => raw (Y ω))) :
    μ.map X = ν.map Y := by
  apply measure_eq_of_raw
  rw [Measure.map_map measurable_raw hX, Measure.map_map measurable_raw hY]
  exact h

theorem decoder_law_eq_of_raw [Countable I] {Ω₁ Ω₂ A : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace A]
    {μ : Measure Ω₁} {ν : Measure Ω₂}
    {X : Ω₁ → I → C(T, ℝ)} {Y : Ω₂ → I → C(T, ℝ)}
    (hX : Measurable X) (hY : Measurable Y)
    (h : μ.map (fun ω => raw (X ω)) = ν.map (fun ω => raw (Y ω)))
    {D : (I → C(T, ℝ)) → A} (hD : Measurable D) :
    μ.map (fun ω => D (X ω)) = ν.map (fun ω => D (Y ω)) := by
  have hpath := law_eq_of_raw hX hY h
  simpa only [Measure.map_map hD hX, Measure.map_map hD hY, Function.comp_def] using
    congrArg (Measure.map D) hpath

theorem exists_measurable_lift [Countable I] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (U : Ω → I → T → ℝ)
    (hU : ∀ i t, Measurable (fun ω => U ω i t))
    (hc : ∀ᵐ ω ∂μ, ∀ i, Continuous (U ω i)) :
    ∃ X : Ω → I → C(T, ℝ), Measurable X ∧
      (fun ω => raw (X ω)) =ᵐ[μ] U := by
  classical
  obtain ⟨N, hsub, hNm, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hc)
  have hgood (ω : Ω) (hω : ω ∉ N) : ∀ i, Continuous (U ω i) := by
    by_contra h
    exact hω (hsub h)
  let X : Ω → I → C(T, ℝ) := fun ω i =>
    if h : ω ∈ N then 0 else ⟨U ω i, hgood ω h i⟩
  refine ⟨X, measurable_iff_evaluation.mpr ?_, ?_⟩
  · intro i t
    have heq : (fun ω => X ω i t) =
        (fun ω => if ω ∈ N then (0 : ℝ) else U ω i t) := by
      funext ω
      by_cases h : ω ∈ N <;> simp [X, h]
    rw [heq]
    exact Measurable.ite hNm measurable_const (hU i t)
  · have havoid : ∀ᵐ ω ∂μ, ω ∉ N := by
      apply ae_iff.mpr
      simpa only [not_not, Set.ofPred_mem_eq] using hNnull
    filter_upwards [havoid] with ω hω
    funext i t
    simp [raw, X, hω]

theorem exists_measurable_lift_of_aemeasurable [Countable I]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (U : Ω → I → T → ℝ)
    (hU : ∀ i t, AEMeasurable (fun ω => U ω i t) μ)
    (hc : ∀ᵐ ω ∂μ, ∀ i, Continuous (U ω i)) :
    ∃ X : Ω → I → C(T, ℝ), Measurable X ∧
      (fun ω => raw (X ω)) =ᵐ[μ] U := by
  classical
  let X : Ω → I → C(T, ℝ) := fun ω i =>
    if h : ∀ j, Continuous (U ω j) then ⟨U ω i, h i⟩ else 0
  have hraw : (fun ω => raw (X ω)) =ᵐ[μ] U := by
    filter_upwards [hc] with ω hω
    funext i t
    simp [X, raw, hω]
  have hd : AEMeasurable (denseEval ∘ X) μ := by
    apply aemeasurable_pi_iff.mpr
    intro i
    apply aemeasurable_pi_iff.mpr
    intro n
    apply (hU i (TopologicalSpace.denseSeq T n)).congr
    filter_upwards [hraw] with ω hω
    exact (congrFun (congrFun hω i) (TopologicalSpace.denseSeq T n)).symm
  have hX : AEMeasurable X μ :=
    measurableEmbedding_denseEval.aemeasurable_comp_iff.mp hd
  refine ⟨hX.mk X, hX.measurable_mk, ?_⟩
  filter_upwards [hX.ae_eq_mk, hraw] with ω heq hω
  rw [← heq]
  exact hω

theorem exists_measurable_lift_with_law [Countable I]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (U : Ω → I → T → ℝ)
    (hU : ∀ i t, AEMeasurable (fun ω => U ω i t) μ)
    (hc : ∀ᵐ ω ∂μ, ∀ i, Continuous (U ω i))
    {ν : Measure (I → C(T, ℝ))} (hlaw : μ.map U = ν.map raw) :
    ∃ X : Ω → I → C(T, ℝ), Measurable X ∧
      (fun ω => raw (X ω)) =ᵐ[μ] U ∧ μ.map X = ν := by
  obtain ⟨X, hX, heq⟩ := exists_measurable_lift_of_aemeasurable U hU hc
  refine ⟨X, hX, heq, measure_eq_of_raw ?_⟩
  rw [Measure.map_map measurable_raw hX]
  exact (Measure.map_congr heq).trans hlaw

end Problem336.ContinuousPathLaw

end

end OAI

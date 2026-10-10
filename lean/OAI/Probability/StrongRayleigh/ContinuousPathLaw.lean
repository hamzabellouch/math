import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13

noncomputable section

open MeasureTheory ProbabilityTheory Topology
open scoped NNReal

namespace Problem336AdditiveD139.ContinuousPathLaw

section DenseEvaluations

variable {T : Type u_1} {D : Type u_2} {I : Type u_3} [TopologicalSpace T]

def familySamples (e : D → T) (f : I → C(T, ℝ)) : I × D → ℝ :=
  fun p => f p.1 (e p.2)

theorem continuous_familySamples (e : D → T) : Continuous (familySamples (I := I) e) := by
  apply continuous_pi
  intro p
  exact (continuous_eval_const (e p.2)).comp (continuous_apply p.1)

theorem familySamples_injective {e : D → T} (he : DenseRange e) :
    Function.Injective (familySamples (I := I) e) := by
  intro f g h
  funext i
  apply ContinuousMap.coe_injective
  apply he.equalizer (f i).continuous (g i).continuous
  funext d
  exact congrFun h (i, d)

variable [Countable D] [Countable I]
variable [PolishSpace C(T, ℝ)] [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]

theorem measurableEmbedding_familySamples {e : D → T} (he : DenseRange e) :
    MeasurableEmbedding (familySamples (I := I) e) :=
  (continuous_familySamples e).measurableEmbedding (familySamples_injective he)

theorem measurable_iff_dense_evaluations {Ω : Type u_4} [MeasurableSpace Ω]
    {e : D → T} (he : DenseRange e) {X : Ω → I → C(T, ℝ)} :
    Measurable X ↔ ∀ i d, Measurable (fun ω => X ω i (e d)) := by
  rw [← (measurableEmbedding_familySamples (I := I) he).measurable_comp_iff]
  simp only [measurable_pi_iff, Function.comp_def, familySamples]
  exact ⟨fun h i d => h (i, d), fun h p => h p.1 p.2⟩

theorem measure_eq_of_dense_finiteDimensional {e : D → T} (he : DenseRange e)
    {μ ν : Measure (I → C(T, ℝ))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ S : Finset (I × D),
      μ.map (fun f => S.restrict (familySamples e f)) =
        ν.map (fun f => S.restrict (familySamples e f))) : μ = ν := by
  have hs := (measurableEmbedding_familySamples (I := I) he).measurable
  apply (measurableEmbedding_familySamples (I := I) he).map_injective
  apply (isProjectiveLimit_map hs.aemeasurable).unique
  intro S
  rw [Measure.map_map (Finset.measurable_restrict S) hs]
  exact (h S).symm

theorem aemeasurable_iff_dense_evaluations {Ω : Type u_5} [MeasurableSpace Ω]
    {P : Measure Ω} {e : D → T} (he : DenseRange e) {X : Ω → I → C(T, ℝ)} :
    AEMeasurable X P ↔ ∀ i d, AEMeasurable (fun ω => X ω i (e d)) P := by
  rw [← (measurableEmbedding_familySamples (I := I) he).aemeasurable_comp_iff]
  simp only [aemeasurable_pi_iff, Function.comp_def, familySamples]
  exact ⟨fun h i d => h (i, d), fun h p => h p.1 p.2⟩

def bundlePaths {Ω : Type u_6} (Z : Ω → I → T → ℝ) : Ω → I → C(T, ℝ) :=
  fun ω i => ContinuousMap.mkD (Z ω i) 0

theorem aemeasurable_bundlePaths {Ω : Type u_7} [MeasurableSpace Ω]
    {P : Measure Ω} {e : D → T} (he : DenseRange e) {Z : Ω → I → T → ℝ}
    (hm : ∀ i d, AEMeasurable (fun ω => Z ω i (e d)) P)
    (hc : ∀ i, ∀ᵐ ω ∂P, Continuous (Z ω i)) :
    AEMeasurable (bundlePaths Z) P := by
  apply (aemeasurable_iff_dense_evaluations he).2
  intro i d
  apply (hm i d).congr
  filter_upwards [hc i] with ω hω
  simp only [bundlePaths, ContinuousMap.mkD_apply_of_continuous hω]

omit [Countable I] [PolishSpace C(T, ℝ)] [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)] in

theorem bundlePaths_eval_ae_eq {Ω : Type u_8} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : Ω → I → T → ℝ}
    (hc : ∀ i, ∀ᵐ ω ∂P, Continuous (Z ω i)) (i : I) (t : T) :
    (fun ω => bundlePaths Z ω i t) =ᵐ[P] (fun ω => Z ω i t) := by
  filter_upwards [hc i] with ω hω
  simp only [bundlePaths, ContinuousMap.mkD_apply_of_continuous hω]

theorem exists_measurable_path_version {Ω : Type u_9} [MeasurableSpace Ω]
    {P : Measure Ω} {e : D → T} (he : DenseRange e) {Z : Ω → I → T → ℝ}
    (hm : ∀ i d, AEMeasurable (fun ω => Z ω i (e d)) P)
    (hc : ∀ i, ∀ᵐ ω ∂P, Continuous (Z ω i)) :
    ∃ X : Ω → I → C(T, ℝ), Measurable X ∧
      ∀ i t, (fun ω => X ω i t) =ᵐ[P] (fun ω => Z ω i t) := by
  have h := aemeasurable_bundlePaths he hm hc
  refine ⟨h.mk _, h.measurable_mk, ?_⟩
  intro i t
  refine Filter.EventuallyEq.trans ?_ (bundlePaths_eval_ae_eq hc i t)
  filter_upwards [h.ae_eq_mk] with ω hω
  exact congrArg (fun f : I → C(T, ℝ) => f i t) hω.symm

theorem identDistrib_of_dense_finiteDimensional
    {Ω : Type u_10} {Ω' : Type u_11} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {e : D → T} (he : DenseRange e)
    {X : Ω → I → C(T, ℝ)} {Y : Ω' → I → C(T, ℝ)}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (h : ∀ S : Finset (I × D),
      IdentDistrib (fun ω => S.restrict (familySamples e (X ω)))
        (fun ω => S.restrict (familySamples e (Y ω))) P Q) :
    IdentDistrib X Y P Q := by
  refine ⟨hX, hY, measure_eq_of_dense_finiteDimensional he ?_⟩
  intro S
  have hs : Measurable (fun f : I → C(T, ℝ) => S.restrict (familySamples e f)) :=
    (Finset.measurable_restrict S).comp (continuous_familySamples e).measurable
  rw [AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hX,
    AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hY]
  exact (h S).map_eq

end DenseEvaluations

def rationalTime (q : ℚ) : ℝ≥0 := Real.toNNReal (q : ℝ)

theorem denseRange_rationalTime : DenseRange rationalTime := by
  have hs : Function.Surjective Real.toNNReal := fun x => ⟨x, by simp⟩
  exact hs.denseRange.comp Rat.denseRange_cast continuous_real_toNNReal

section NonnegativeRealTime

variable {I : Type u_12} [Countable I]
variable [MeasurableSpace C(ℝ≥0, ℝ)] [BorelSpace C(ℝ≥0, ℝ)]

theorem measure_eq_of_rational_finiteDimensional
    {μ ν : Measure (I → C(ℝ≥0, ℝ))} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ S : Finset (I × ℚ),
      μ.map (fun f => S.restrict (familySamples rationalTime f)) =
        ν.map (fun f => S.restrict (familySamples rationalTime f))) : μ = ν :=
  measure_eq_of_dense_finiteDimensional denseRange_rationalTime h

theorem measurable_iff_rational_evaluations {Ω : Type u_13} [MeasurableSpace Ω]
    {X : Ω → I → C(ℝ≥0, ℝ)} :
    Measurable X ↔ ∀ i q, Measurable (fun ω => X ω i (rationalTime q)) :=
  measurable_iff_dense_evaluations denseRange_rationalTime

end NonnegativeRealTime

end Problem336AdditiveD139.ContinuousPathLaw

end

end OAI

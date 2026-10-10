import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Problem336.LabelNoCollision

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {U : ℕ → Ω → ℝ}

theorem probability (h : IsVertexIID P U) : IsProbabilityMeasure P := by
  constructor
  simpa using h.2 ∅ (fun _ => Set.univ) (by simp)

theorem marginal (h : IsVertexIID P U) (i : ℕ) {s : Set ℝ}
    (hs : MeasurableSet s) : P (U i ⁻¹' s) = uniform01 s := by
  change P {ω | U i ω ∈ s} = uniform01 s
  simpa using h.2 {i} (fun _ => s) (by simpa using hs)

theorem map_marginal (h : IsVertexIID P U) (i : ℕ) : P.map (U i) = uniform01 := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (h.1 i) hs]
  exact marginal h i hs

theorem independent (h : IsVertexIID P U) : iIndepFun U P := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hs
  calc
    P (⋂ i ∈ s, U i ⁻¹' sets i) = P {ω | ∀ i ∈ s, U i ω ∈ sets i} := by
      congr 1
      ext ω
      simp
    _ = ∏ i ∈ s, uniform01 (sets i) := h.2 s sets hs
    _ = ∏ i ∈ s, P (U i ⁻¹' sets i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (marginal h i (hs i hi)).symm

theorem map_pair (h : IsVertexIID P U) {i j : ℕ} (hij : i ≠ j) :
    P.map (fun ω => (U i ω, U j ω)) = uniform01.prod uniform01 := by
  let : IsProbabilityMeasure P := probability h
  rw [(independent h).indepFun hij |>.map_prod_eq_prod_map_map
    (h.1 i).aemeasurable (h.1 j).aemeasurable]
  rw [map_marginal h i, map_marginal h j]

theorem uniform01_noAtoms : NullSingletonClass uniform01 := by
  unfold uniform01
  infer_instance

theorem uniform01_finite : IsFiniteMeasure uniform01 := by
  unfold uniform01
  infer_instance

theorem diagonal_null : (uniform01.prod uniform01) (Set.diagonal ℝ) = 0 := by
  let : NullSingletonClass uniform01 := uniform01_noAtoms
  let : IsFiniteMeasure uniform01 := uniform01_finite
  rw [Measure.prod_apply measurableSet_diagonal]
  have hsection (x : ℝ) : Prod.mk x ⁻¹' Set.diagonal ℝ = {x} := by
    ext y
    simp [Set.diagonal, eq_comm]
  simp only [hsection, measure_singleton, lintegral_zero]

theorem pair_collision_null (h : IsVertexIID P U) {i j : ℕ} (hij : i ≠ j) :
    P {ω | U i ω = U j ω} = 0 := by
  have hm : Measurable (fun ω => (U i ω, U j ω)) := (h.1 i).prodMk (h.1 j)
  have heq := congrArg (fun μ : Measure (ℝ × ℝ) => μ (Set.diagonal ℝ)) (map_pair h hij)
  rw [Measure.map_apply hm measurableSet_diagonal, diagonal_null] at heq
  exact heq

theorem ae_ne (h : IsVertexIID P U) {i j : ℕ} (hij : i ≠ j) :
    ∀ᵐ ω ∂P, U i ω ≠ U j ω := by
  rw [ae_iff]
  simpa only [not_not] using pair_collision_null h hij

theorem ae_injective_labels (h : IsVertexIID P U) :
    ∀ᵐ ω ∂P, Function.Injective (fun i => U i ω) := by
  change ∀ᵐ ω ∂P, ∀ ⦃i j : ℕ⦄, U i ω = U j ω → i = j
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun _ _ => hij)
  · filter_upwards [ae_ne h hij] with ω hω
    exact fun heq => (hω heq).elim

end Problem336.LabelNoCollision

end

end OAI

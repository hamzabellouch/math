import OAI.NumberTheory.DukePrimeDegree.Geometry.RowLeafProduct
import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteCoordinateIndependence

namespace OAI

/-!
# Every row conditional is a product of its root coordinates

The neutral-holonomy splitting holds for each coordinate. This gives
mutual independence, not just pairwise independence, because each
coordinate is independent of the entire tuple of remaining coordinates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set

namespace DukePrimeDegree
open PrimeDegreePackets

abbrev RowCoordinate {n : ℕ} (i : Fin n) := {j : Fin n // j ≠ i}

def rowCoordinates {n : ℕ} (i : Fin n) (a : RowTime i) : RowCoordinate i → ℝ :=
  fun j => a.val j.val

lemma rowSplitMeasure_fst {n : ℕ} {i j : Fin n} (hij : i ≠ j) {k : Fin n}
    (ρ : Measure (RowRootSlice i k × RowTime i)) :
    (rowSplitMeasure hij ρ).fst = ρ.fst := by
  have H := fst_map_measurableEquiv ρ (MeasurableEquiv.refl _)
    (rowTimeSplit hij).toMeasurableEquiv
  change (rowSplitMeasure hij ρ).fst = ρ.fst.map id at H
  simpa only [Measure.map_id] using H

theorem rowBox_ae_mapped_conditional_eq_prod
    (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j) {k : Fin (d + 1)}
    (B : RowRootBox i k) {R : ℝ} (hR : 0 < R) (hT : B.time = rowCube i R)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      ((B.conditionalKernel μ s).map (rowTimeSplit hij)) =
        ((B.conditionalKernel μ s).map (rowTimeSplit hij)).fst.prod
          ((B.conditionalKernel μ s).map (rowTimeSplit hij)).snd := by
  have hp := rowBox_ae_conditional_eq_prod d hij B hR hT μ hA
  rw [rowSplitMeasure_fst] at hp
  have hc := condKernel_map_measurableEquiv (B.coordinateMeasure μ)
    (MeasurableEquiv.refl _) (rowTimeSplit hij).toMeasurableEquiv
  filter_upwards [hp, hc] with s hs hsc
  change (rowSplitMeasure hij (B.coordinateMeasure μ)).condKernel s =
    (B.conditionalKernel μ s).map (rowTimeSplit hij) at hsc
  simpa only [hsc] using hs

theorem rowCoordinates_independent_of_splittings {n : ℕ} {i : Fin n}
    (ν : Measure (RowTime i)) [IsProbabilityMeasure ν]
    (h : ∀ (j : Fin n) (hij : i ≠ j),
      (ν.map (rowTimeSplit hij)) = (ν.map (rowTimeSplit hij)).fst.prod
        (ν.map (rowTimeSplit hij)).snd) :
    iIndepFun (fun j : RowCoordinate i => fun a => rowCoordinates i a j) ν := by
  apply iIndepFun_of_independent_remaining ν
  intro j
  let E := rowTimeSplit j.prop.symm
  have he : IndepFun (fun a => (E a).1) (fun a => (E a).2) ν := by
    apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).mpr
    have hf := Measure.fst_map_prodMk (μ := ν)
      (E.continuous.fst.measurable) (E.continuous.snd.measurable)
    have hs := Measure.snd_map_prodMk (μ := ν)
      (E.continuous.fst.measurable) (E.continuous.snd.measurable)
    have hp : (fun a => ((E a).1, (E a).2)) = E := rfl
    rw [hp] at hf hs ⊢
    rw [← hf, ← hs]
    exact h j.val j.prop.symm
  let g : RowRemainingTime i j.val → ({l : RowCoordinate i // l ≠ j} → ℝ) :=
    fun w l => w.val.val l.val.val
  have hg : Measurable g := by
    apply Measurable.of_eval
    intro l
    exact (measurable_pi_apply l.val.val).comp
      (measurable_subtype_coe.comp measurable_subtype_coe)
  have hr : (fun a => g ((E a).1)) =
      (fun a (l : {l : RowCoordinate i // l ≠ j}) => rowCoordinates i a l.val) := by
    funext a l
    have hne : l.val.val ≠ j.val := fun hh => l.prop (Subtype.ext hh)
    simp [g, E, rowTimeSplit, rowUnit, rowCoordinates, hne]
  have H := he.symm.comp measurable_id hg
  have ht : (fun a => (E a).2) = (fun a => rowCoordinates i a j) := rfl
  simpa only [Function.comp_def, id_eq, hr, ht] using H

/-- The actual row leaf law in elementary-root coordinates is the
product of its one-root marginals. -/
theorem rowBox_ae_joint_law_eq_pi
    (d : ℕ) {i k : Fin (d + 1)} (B : RowRootBox i k)
    {R : ℝ} (hR : 0 < R) (hT : B.time = rowCube i R)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ) :
    ∀ᵐ s ∂(B.coordinateMeasure μ).fst,
      (B.conditionalKernel μ s).map (rowCoordinates i) =
        Measure.pi (fun j : RowCoordinate i =>
          (B.conditionalKernel μ s).map (fun a => a.val j.val)) := by
  have hall := ae_all_iff.mpr (fun j : RowCoordinate i =>
    rowBox_ae_mapped_conditional_eq_prod d j.prop.symm B hR hT μ hA)
  filter_upwards [hall] with s hs
  have hind := rowCoordinates_independent_of_splittings (B.conditionalKernel μ s) (by
    intro j hij
    exact hs ⟨j, hij.symm⟩)
  exact hind.map_fun_eq_pi_map (fun j =>
    ((measurable_pi_apply j.val).comp measurable_subtype_coe).aemeasurable)

end DukePrimeDegree

end

end OAI

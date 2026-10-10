import OAI.Analysis.LipschitzHilbert.Fourier.PositiveLineMaximal
import OAI.Analysis.LipschitzHilbert.Geometry.RectangleAuxiliary

namespace OAI

/-! Pointwise monotone positive-integral auxiliary maximal functions for
finite rectangle selection. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert
open DyadicLineGrid

theorem gridSquareSup_mono (qx qy : ℤ) {f g : ℝ × ℝ → ℝ≥0∞} (h : f ≤ g) :
    gridSquareSup qx qy f ≤ gridSquareSup qx qy g :=
  rankedMaximal_mono (volume.prod volume) (squareCell qx qy) h

theorem squareSup_mono {f g : ℝ × ℝ → ℝ≥0∞} (h : f ≤ g) : squareSup f ≤ squareSup g := by
  intro z
  apply Finset.sup_mono_fun
  intro q _
  exact gridSquareSup_mono q.1.val q.2.val h z

def positiveChartLine (e : Plane ≃ᵐ (ℝ × ℝ)) (f : Plane → ℝ≥0∞) (x : Plane) : ℝ≥0∞ :=
  positiveHorizontal (f ∘ e.symm) (e x)

def positivePlaneSquare (f : Plane → ℝ≥0∞) (x : Plane) : ℝ≥0∞ :=
  squareSup (f ∘ planeCoordinates) (planeCoordinates.symm x)

theorem positiveChartLine_measurable (e : Plane ≃ᵐ (ℝ × ℝ))
    {f : Plane → ℝ≥0∞} (hf : Measurable f) : Measurable (positiveChartLine e f) :=
  (positiveHorizontal_measurable (hf.comp e.symm.measurable)).comp e.measurable

theorem positivePlaneSquare_measurable (f : Plane → ℝ≥0∞) : Measurable (positivePlaneSquare f) :=
  (squareSup_measurable _).comp planeCoordinates.symm.measurable

theorem positiveChartLine_weak_L1 (e : Plane ≃ᵐ (ℝ × ℝ))
    (he : MeasurePreserving e volume (volume.prod volume)) {f : Plane → ℝ≥0∞}
    (hf : Measurable f) (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    volume {x | t < positiveChartLine e f x} ≤ 3 * t⁻¹ * ∫⁻ x, f x := by
  have hE : MeasurableSet {z | t < positiveHorizontal (f ∘ e.symm) z} :=
    measurableSet_lt measurable_const (positiveHorizontal_measurable (hf.comp e.symm.measurable))
  change volume (e ⁻¹' {z | t < positiveHorizontal (f ∘ e.symm) z}) ≤ _
  rw [he.measure_preimage hE.nullMeasurableSet]
  have h := positiveHorizontal_weak_L1 (hf.comp e.symm.measurable) t ht htop
  refine h.trans_eq ?_
  simp only [Function.comp_apply]
  rw [he.symm.lintegral_comp hf]

theorem positivePlaneSquare_weak_L1 {f : Plane → ℝ≥0∞} (hf : Measurable f)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    volume {x | t < positivePlaneSquare f x} ≤ 9 * t⁻¹ * ∫⁻ x, f x := by
  have hE : MeasurableSet {z | t < squareSup (f ∘ planeCoordinates) z} :=
    measurableSet_lt measurable_const (squareSup_measurable _)
  change volume (planeCoordinates.symm ⁻¹' {z | t < squareSup (f ∘ planeCoordinates) z}) ≤ _
  rw [planeCoordinates_measurePreserving.symm.measure_preimage hE.nullMeasurableSet]
  refine (squareSup_weak_L1 (f ∘ planeCoordinates) t ht htop).trans_eq ?_
  simp only [Function.comp_apply]
  rw [planeCoordinates_measurePreserving.lintegral_comp hf]

variable {ι : Type*} [Fintype ι]

def positiveAuxiliary (e : ι → Plane ≃ᵐ (ℝ × ℝ)) (f : Plane → ℝ≥0∞) (x : Plane) : ℝ≥0∞ :=
  positivePlaneSquare f x ⊔ Finset.univ.sup (fun i => positiveChartLine (e i) f x)

theorem positiveAuxiliary_measurable (e : ι → Plane ≃ᵐ (ℝ × ℝ))
    {f : Plane → ℝ≥0∞} (hf : Measurable f) : Measurable (positiveAuxiliary e f) := by
  have h (s : Finset ι) : Measurable (fun x => s.sup (fun i => positiveChartLine (e i) f x)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simpa only [Finset.sup_insert] using (positiveChartLine_measurable (e i) hf).max ih
  exact (positivePlaneSquare_measurable f).max (h Finset.univ)

theorem positiveAuxiliary_mono (e : ι → Plane ≃ᵐ (ℝ × ℝ))
    {f g : Plane → ℝ≥0∞} (h : f ≤ g) : positiveAuxiliary e f ≤ positiveAuxiliary e g := by
  intro x
  apply sup_le_sup
  · exact squareSup_mono (fun z => h (planeCoordinates z)) (planeCoordinates.symm x)
  · apply Finset.sup_mono_fun
    intro i _
    exact positiveHorizontal_mono (fun z => h ((e i).symm z)) (e i x)

theorem positiveAuxiliary_zero (e : ι → Plane ≃ᵐ (ℝ × ℝ)) (x : Plane) :
    positiveAuxiliary e (fun _ => 0) x = 0 := by
  simp [positiveAuxiliary,positivePlaneSquare,squareSup,gridSquareSup,
    positiveChartLine,positiveHorizontal,positiveGridHorizontal,positiveGridLine,rankedMaximal]

theorem positiveAuxiliary_weak_L1 (e : ι → Plane ≃ᵐ (ℝ × ℝ))
    (he : ∀ i, MeasurePreserving (e i) volume (volume.prod volume))
    {f : Plane → ℝ≥0∞} (hf : Measurable f) (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    volume {x | t < positiveAuxiliary e f x} ≤
      (9 + 3 * Fintype.card ι) * t⁻¹ * ∫⁻ x, f x := by
  classical
  have hsub : {x | t < positiveAuxiliary e f x} ⊆
      {x | t < positivePlaneSquare f x} ∪ ⋃ i : ι, {x | t < positiveChartLine (e i) f x} := by
    intro x hx
    change t < positivePlaneSquare f x ⊔ Finset.univ.sup (fun i => positiveChartLine (e i) f x) at hx
    rcases lt_sup_iff.mp hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨i,_,hi⟩ := Finset.lt_sup_iff.mp hx
      exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)
  calc
    _ ≤ volume ({x | t < positivePlaneSquare f x} ∪
        ⋃ i : ι, {x | t < positiveChartLine (e i) f x}) := measure_mono hsub
    _ ≤ volume {x | t < positivePlaneSquare f x} +
        ∑ i : ι, volume {x | t < positiveChartLine (e i) f x} :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
    _ ≤ 9 * t⁻¹ * (∫⁻ x, f x) + ∑ _i : ι, 3 * t⁻¹ * ∫⁻ x, f x :=
      add_le_add (positivePlaneSquare_weak_L1 hf t ht htop)
        (Finset.sum_le_sum (fun i _ => positiveChartLine_weak_L1 (e i) (he i) hf t ht htop))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

end LipschitzHilbert

end

end OAI

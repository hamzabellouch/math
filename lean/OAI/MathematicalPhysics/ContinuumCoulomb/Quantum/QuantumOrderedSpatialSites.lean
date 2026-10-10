import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedXZPipeline
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumMediatorGeometry

namespace OAI

/-! The literal early compiler places each mediator at the anchor of its
source word. These geometric statements retain the exact ordered word types. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSpatial
open QuantumOrderedSubdivision
open scoped Classical

variable {ι κ : Type} {rows width : ℕ}

def Near (xs : κ → List ι) (cell : ι → QMAGridCell rows width)
    (anchor : κ → QMAGridCell rows width) : Prop :=
  ∀ e, ∀ i ∈ xs e, QMAGridCellsNear (cell i) (anchor e)

theorem map_near (cell : ι → QMAGridCell rows width)
    (anchor : κ → QMAGridCell rows width) (e : κ) (xs : List ι)
    (h : ∀ i ∈ xs, QMAGridCellsNear (cell i) (anchor e)) :
    ∀ q ∈ xs.map (Sum.inl : ι → ι ⊕ κ),
      QMAGridCellsNear (qmaMediatorCell cell anchor q) (anchor e) := by
  intro q hq
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hq
  exact h i hi

theorem append_near (cell : ι → QMAGridCell rows width)
    (anchor : κ → QMAGridCell rows width) (e : κ) (xs : List ι)
    (h : ∀ i ∈ xs, QMAGridCellsNear (cell i) (anchor e)) :
    ∀ q ∈ appendMediator xs e,
      QMAGridCellsNear (qmaMediatorCell cell anchor q) (anchor e) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact map_near cell anchor e xs h q hq
  · have he : q = Sum.inr e := by simpa only [List.mem_singleton] using hq
    subst q
    exact qmaGridCellsNear_refl _

theorem subdivision_near (xs : κ → List ι) (d : ℕ)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    (h : Near xs cell anchor) :
    Near (QuantumOrderedSubdivision.outputSites xs d) (qmaMediatorCell cell anchor)
      (fun p => anchor p.1) := by
  rintro ⟨e,k⟩ q hq
  fin_cases k
  · exact False.elim (List.not_mem_nil hq)
  · change q ∈ [Sum.inr e] at hq
    have he : q = Sum.inr e := List.mem_singleton.mp hq
    subst q
    exact qmaGridCellsNear_refl _
  · exact append_near cell anchor e ((xs e).take d)
      (fun i hi => h e i (List.mem_of_mem_take hi)) q hq
  · exact append_near cell anchor e ((xs e).drop d)
      (fun i hi => h e i (List.mem_of_mem_drop hi)) q hq

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem third_near (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 3)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    (h : Near xs cell anchor) :
    Near (QuantumOrderedThird.outputSites xs w) (qmaMediatorCell cell anchor)
      (fun p => anchor p.1) := by
  rintro ⟨e,k⟩ q hq
  have hp : ∀ i ∈ (QuantumOrderedTriple.partition (xs e) (w e)).1,
      QMAGridCellsNear (cell i) (anchor e) := by
    intro i hi
    apply h e i
    exact (QuantumOrderedTriple.partition_spec (xs e) (w e) (hlen e)).1.mem_iff.mp
      (List.mem_append_left _ hi)
  have hr : ∀ i ∈ (QuantumOrderedTriple.partition (xs e) (w e)).2,
      QMAGridCellsNear (cell i) (anchor e) := by
    intro i hi
    apply h e i
    exact (QuantumOrderedTriple.partition_spec (xs e) (w e) (hlen e)).1.mem_iff.mp
      (List.mem_append_right _ hi)
  fin_cases k
  · exact False.elim (List.not_mem_nil hq)
  · change q ∈ [Sum.inr e] at hq
    have he : q = Sum.inr e := List.mem_singleton.mp hq
    subst q
    exact qmaGridCellsNear_refl _
  · exact map_near cell anchor e _ hp q hq
  · exact map_near cell anchor e _ hr q hq
  · exact append_near cell anchor e _ hr q hq
  · exact append_near cell anchor e _
      (fun i hi => hp i (List.mem_of_mem_take hi)) q hq
  · exact append_near cell anchor e _
      (fun i hi => hp i (List.mem_of_mem_drop hi)) q hq

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem yy_near (xs : κ → List ι)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    (h : Near xs cell anchor) :
    Near (QuantumOrderedYY.outputSites xs) (qmaMediatorCell cell anchor)
      (fun p => anchor p.1) := by
  rintro ⟨e,k⟩ q hq
  fin_cases k
  · exact False.elim (List.not_mem_nil hq)
  · change q ∈ [Sum.inr e] at hq
    have he : q = Sum.inr e := List.mem_singleton.mp hq
    subst q
    exact qmaGridCellsNear_refl _
  · exact append_near cell anchor e _ (h e) q hq
  · exact append_near cell anchor e _ (h e) q hq

end ContinuumCoulomb.QuantumOrderedSpatial

end

end OAI

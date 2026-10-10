import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedIncidence
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourSpatial

namespace OAI

/-! Spatial data for the literal ordered six-stage compiler. A mediator is
placed in its parent term's cell, and each emitted term retains that anchor. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSpatialComplete
open scoped Classical
variable {ι κ C : Type}

def extendCell (cell : ι → C) (anchor : κ → C) : ι ⊕ κ → C := Sum.elim cell anchor
def extendAnchor (d : ℕ) (anchor : κ → C) : κ × Fin d → C := fun p => anchor p.1

theorem extension_geometry {d : ℕ} (xs : κ → List ι)
    (ys : κ × Fin d → List (ι ⊕ κ)) (cell : ι → C) (anchor : κ → C)
    (R : C → C → Prop) (hR : ∀ p, R p p)
    (hx : ∀ e q, q ∈ xs e → R (cell q) (anchor e))
    (hy : ∀ e q, q ∈ ys e → QuantumOrderedIncidence.Origin xs e.1 q) :
    ∀ e q, q ∈ ys e → R (extendCell cell anchor q) (extendAnchor d anchor e) := by
  intro e q hq
  have ho := hy e q hq
  cases q with
  | inl q => exact hx e.1 q ho
  | inr q =>
    change q=e.1 at ho
    subst q
    exact hR _

theorem extendCell_density [Fintype ι] [Fintype κ] (cell : ι → C) (anchor : κ → C)
    {A B : ℕ} (hc : ∀ p, (Finset.univ.filter (fun q => cell q=p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun e => anchor e=p)).card ≤ B) (p : C) :
    (Finset.univ.filter (fun q => extendCell cell anchor q=p)).card ≤ A+B := by
  rw [qmaSumFilter_card]
  exact Nat.add_le_add (hc p) (ha p)

theorem extendAnchor_density [Fintype κ] (d : ℕ) (anchor : κ → C) {B : ℕ}
    (ha : ∀ p, (Finset.univ.filter (fun e => anchor e=p)).card ≤ B) (p : C) :
    (Finset.univ.filter (fun e => extendAnchor d anchor e=p)).card ≤ d*B := by
  change (Finset.univ.filter (fun e : κ × Fin d => anchor e.1=p)).card ≤ _
  rw [qmaProdFilter_card d (fun e : κ => anchor e=p)]
  exact Nat.mul_le_mul_left d (ha p)

def cell1 (cell : ι → C) (anchor : κ → C) := extendCell cell anchor
def anchor1 (anchor : κ → C) := extendAnchor 4 anchor
def cell2 (cell : ι → C) (anchor : κ → C) := extendCell (cell1 cell anchor) (anchor1 anchor)
def anchor2 (anchor : κ → C) := extendAnchor 4 (anchor1 anchor)
def cell3 (cell : ι → C) (anchor : κ → C) := extendCell (cell2 cell anchor) (anchor2 anchor)
def anchor3 (anchor : κ → C) := extendAnchor 7 (anchor2 anchor)
def cell4 (cell : ι → C) (anchor : κ → C) := extendCell (cell3 cell anchor) (anchor3 anchor)
def anchor4 (anchor : κ → C) := extendAnchor 4 (anchor3 anchor)
def cell5 (cell : ι → C) (anchor : κ → C) := extendCell (cell4 cell anchor) (anchor4 anchor)
def anchor5 (anchor : κ → C) := extendAnchor 7 (anchor4 anchor)
def cell6 (cell : ι → C) (anchor : κ → C) := extendCell (cell5 cell anchor) (anchor5 anchor)
def anchor6 (anchor : κ → C) := extendAnchor 4 (anchor5 anchor)

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem complete_geometry (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6) (cell : ι → C) (anchor : κ → C)
    (R : C → C → Prop) (hR : ∀ p, R p p)
    (hx : ∀ e q, q ∈ xs e → R (cell q) (anchor e)) :
    ∀ e q, q ∈ QuantumOrderedPrivate.outputSites (QuantumOrderedXZ.sites xs w) e →
      R (cell6 cell anchor q) (anchor6 anchor e) := by
  have h1 := extension_geometry xs _ cell anchor R hR hx
    (QuantumOrderedIncidence.subdivision_origin xs 3)
  have h2 := extension_geometry (QuantumOrderedSubdivision.outputSites xs 3) _
    (cell1 cell anchor) (anchor1 anchor) R hR h1
    (QuantumOrderedIncidence.subdivision_origin (QuantumOrderedSubdivision.outputSites xs 3) 2)
  have h3 := extension_geometry (QuantumOrderedXZ.threeSites xs) (QuantumOrderedXZ.twoSites xs w)
    (cell2 cell anchor) (anchor2 anchor) R hR h2
    (QuantumOrderedIncidence.third_origin (QuantumOrderedXZ.threeSites xs)
      (QuantumOrderedXZ.threeWord xs w) (QuantumOrderedXZ.threeSites_length xs hlen))
  have h4 := extension_geometry (QuantumOrderedXZ.twoSites xs w) _
    (cell3 cell anchor) (anchor3 anchor) R hR h3
    (QuantumOrderedIncidence.yy_origin _)
  have h5 := extension_geometry (QuantumOrderedXZ.xzThreeSites xs w) (QuantumOrderedXZ.sites xs w)
    (cell4 cell anchor) (anchor4 anchor) R hR h4
    (QuantumOrderedIncidence.third_origin (QuantumOrderedXZ.xzThreeSites xs w)
      (QuantumOrderedXZ.xzThreeWord xs w) (QuantumOrderedXZ.xzThreeSites_length xs w hlen))
  exact extension_geometry (QuantumOrderedXZ.sites xs w) _
    (cell5 cell anchor) (anchor5 anchor) R hR h5
    (QuantumOrderedIncidence.subdivision_origin _ 1)

omit [DecidableEq ι] [DecidableEq κ] in
theorem complete_density (cell : ι → C) (anchor : κ → C) {A B : ℕ}
    (hc : ∀ p, (Finset.univ.filter (fun q => cell q=p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun e => anchor e=p)).card ≤ B) :
    (∀ p, (Finset.univ.filter (fun q => cell6 cell anchor q=p)).card ≤ A+3717*B) ∧
    (∀ p, (Finset.univ.filter (fun e => anchor6 anchor e=p)).card ≤ 12544*B) := by
  have hc1 := extendCell_density cell anchor hc ha
  have ha1 := extendAnchor_density 4 anchor ha
  have hc2 := extendCell_density (cell1 cell anchor) (anchor1 anchor) hc1 ha1
  have ha2 := extendAnchor_density 4 (anchor1 anchor) ha1
  have hc3 := extendCell_density (cell2 cell anchor) (anchor2 anchor) hc2 ha2
  have ha3 := extendAnchor_density 7 (anchor2 anchor) ha2
  have hc4 := extendCell_density (cell3 cell anchor) (anchor3 anchor) hc3 ha3
  have ha4 := extendAnchor_density 4 (anchor3 anchor) ha3
  have hc5 := extendCell_density (cell4 cell anchor) (anchor4 anchor) hc4 ha4
  have ha5 := extendAnchor_density 7 (anchor4 anchor) ha4
  have hc6 := extendCell_density (cell5 cell anchor) (anchor5 anchor) hc5 ha5
  have ha6 := extendAnchor_density 4 (anchor5 anchor) ha5
  constructor
  · intro p
    exact (hc6 p).trans (by omega)
  · intro p
    exact (ha6 p).trans (by omega)

end ContinuumCoulomb.QuantumOrderedSpatialComplete

end

end OAI

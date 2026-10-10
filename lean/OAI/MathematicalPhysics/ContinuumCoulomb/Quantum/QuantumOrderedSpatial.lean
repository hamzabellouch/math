import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSpatialSites
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSpatialSubdivision

namespace OAI

/-! Exact cell maps for the five literal early stages. No vertex or term
enumeration is changed while assigning the mediator cells. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedSpatial
open QuantumOrderedXZ
open scoped Classical

variable {ι κ : Type} {rows width : ℕ}

def anchor1 (anchor : κ → QMAGridCell rows width) (p : κ × Fin 4) := anchor p.1
def anchor2 (anchor : κ → QMAGridCell rows width) (p : ThreeTerm κ) := anchor1 anchor p.1
def anchor3 (anchor : κ → QMAGridCell rows width) (p : TwoTerm κ) := anchor2 anchor p.1
def anchor4 (anchor : κ → QMAGridCell rows width) (p : XZThreeTerm κ) := anchor3 anchor p.1
def outputAnchor (anchor : κ → QMAGridCell rows width) (p : OutputTerm κ) := anchor4 anchor p.1

def cell1 (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width) :=
  qmaMediatorCell cell anchor
def cell2 (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width) :=
  qmaMediatorCell (cell1 cell anchor) (anchor1 anchor)
def cell3 (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width) :=
  qmaMediatorCell (cell2 cell anchor) (anchor2 anchor)
def cell4 (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width) :=
  qmaMediatorCell (cell3 cell anchor) (anchor3 anchor)
def outputCell (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width) :=
  qmaMediatorCell (cell4 cell anchor) (anchor4 anchor)

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem output_near (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    (h : Near xs cell anchor) :
    Near (QuantumOrderedXZ.sites xs w) (outputCell cell anchor) (outputAnchor anchor) := by
  have h1 : Near (QuantumOrderedTwoStage.firstSites xs) (cell1 cell anchor) (anchor1 anchor) :=
    subdivision_near xs 3 cell anchor h
  have h2 : Near (threeSites xs) (cell2 cell anchor) (anchor2 anchor) :=
    subdivision_near (QuantumOrderedTwoStage.firstSites xs) 2 _ _ h1
  have h3 : Near (twoSites xs w) (cell3 cell anchor) (anchor3 anchor) :=
    third_near (threeSites xs) (threeWord xs w) (threeSites_length xs hlen) _ _ h2
  have h4 : Near (xzThreeSites xs w) (cell4 cell anchor) (anchor4 anchor) :=
    yy_near (twoSites xs w) _ _ h3
  exact third_near (xzThreeSites xs w) (xzThreeWord xs w)
    (xzThreeSites_length xs w hlen) _ _ h4

omit [DecidableEq κ] in
private theorem anchor1_card (anchor : κ → QMAGridCell rows width)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun e : κ × Fin 4 => anchor1 anchor e = p)).card =
      4*(Finset.univ.filter (fun e : κ => anchor e = p)).card :=
  qmaProdFilter_card 4 (fun e => anchor e = p)

omit [DecidableEq κ] in
private theorem anchor2_card (anchor : κ → QMAGridCell rows width)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun e : ThreeTerm κ => anchor2 anchor e = p)).card =
      16*(Finset.univ.filter (fun e : κ => anchor e = p)).card := by
  calc
    _ = 4*(Finset.univ.filter (fun e : κ × Fin 4 => anchor1 anchor e = p)).card :=
      qmaProdFilter_card 4 (fun e => anchor1 anchor e = p)
    _ = _ := by rw [anchor1_card]; omega

omit [DecidableEq κ] in
private theorem anchor3_card (anchor : κ → QMAGridCell rows width)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun e : TwoTerm κ => anchor3 anchor e = p)).card =
      112*(Finset.univ.filter (fun e : κ => anchor e = p)).card := by
  calc
    _ = 7*(Finset.univ.filter (fun e : ThreeTerm κ => anchor2 anchor e = p)).card :=
      qmaProdFilter_card 7 (fun e => anchor2 anchor e = p)
    _ = _ := by rw [anchor2_card]; omega

omit [DecidableEq κ] in
private theorem anchor4_card (anchor : κ → QMAGridCell rows width)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun e : XZThreeTerm κ => anchor4 anchor e = p)).card =
      448*(Finset.univ.filter (fun e : κ => anchor e = p)).card := by
  calc
    _ = 4*(Finset.univ.filter (fun e : TwoTerm κ => anchor3 anchor e = p)).card :=
      qmaProdFilter_card 4 (fun e => anchor3 anchor e = p)
    _ = _ := by rw [anchor3_card]; omega

omit [DecidableEq κ] in
theorem outputAnchor_card (anchor : κ → QMAGridCell rows width)
    (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun e : OutputTerm κ => outputAnchor anchor e = p)).card =
      3136*(Finset.univ.filter (fun e : κ => anchor e = p)).card := by
  calc
    _ = 7*(Finset.univ.filter (fun e : XZThreeTerm κ => anchor4 anchor e = p)).card :=
      qmaProdFilter_card 7 (fun e => anchor4 anchor e = p)
    _ = _ := by rw [anchor4_card]; omega

omit [DecidableEq ι] [DecidableEq κ] in
theorem outputCell_card (cell : ι → QMAGridCell rows width)
    (anchor : κ → QMAGridCell rows width) (p : QMAGridCell rows width) :
    (Finset.univ.filter (fun q : OutputQubit ι κ => outputCell cell anchor q = p)).card =
      (Finset.univ.filter (fun q : ι => cell q = p)).card+
        581*(Finset.univ.filter (fun e : κ => anchor e = p)).card := by
  have h1 : (Finset.univ.filter (fun q => cell1 cell anchor q = p)).card =
      (Finset.univ.filter (fun q => cell q = p)).card+
        (Finset.univ.filter (fun e => anchor e = p)).card :=
    qmaSumFilter_card (fun q => cell1 cell anchor q = p)
  have h2 : (Finset.univ.filter (fun q => cell2 cell anchor q = p)).card =
      (Finset.univ.filter (fun q => cell1 cell anchor q = p)).card+
        (Finset.univ.filter (fun e => anchor1 anchor e = p)).card :=
    qmaSumFilter_card (fun q => cell2 cell anchor q = p)
  have h3 : (Finset.univ.filter (fun q => cell3 cell anchor q = p)).card =
      (Finset.univ.filter (fun q => cell2 cell anchor q = p)).card+
        (Finset.univ.filter (fun e => anchor2 anchor e = p)).card :=
    qmaSumFilter_card (fun q => cell3 cell anchor q = p)
  have h4 : (Finset.univ.filter (fun q => cell4 cell anchor q = p)).card =
      (Finset.univ.filter (fun q => cell3 cell anchor q = p)).card+
        (Finset.univ.filter (fun e => anchor3 anchor e = p)).card :=
    qmaSumFilter_card (fun q => cell4 cell anchor q = p)
  calc
    _ = (Finset.univ.filter (fun q => cell4 cell anchor q = p)).card+
        (Finset.univ.filter (fun e => anchor4 anchor e = p)).card :=
      qmaSumFilter_card (fun q => outputCell cell anchor q = p)
    _ = _ := by rw [h4,h3,h2,h1,anchor1_card,anchor2_card,anchor3_card,anchor4_card]; omega

omit [DecidableEq ι] [DecidableEq κ] in
theorem output_density (cell : ι → QMAGridCell rows width)
    (anchor : κ → QMAGridCell rows width) {A B : ℕ}
    (hc : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B) :
    (∀ p, (Finset.univ.filter (fun q : OutputQubit ι κ => outputCell cell anchor q = p)).card
      ≤ A+581*B) ∧
    (∀ p, (Finset.univ.filter (fun e : OutputTerm κ => outputAnchor anchor e = p)).card
      ≤ 3136*B) := by
  constructor
  · intro p
    rw [outputCell_card]
    exact Nat.add_le_add (hc p) (Nat.mul_le_mul_left _ (ha p))
  · intro p
    rw [outputAnchor_card]
    exact Nat.mul_le_mul_left _ (ha p)

end ContinuumCoulomb.QuantumOrderedSpatial

end

end OAI

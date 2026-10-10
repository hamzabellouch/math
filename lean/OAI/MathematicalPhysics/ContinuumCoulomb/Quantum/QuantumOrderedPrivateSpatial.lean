import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedPrivate
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedSpatial

namespace OAI

/-! The literal private-pair stage retains neighboring cells and bounded
density, including the exact five-stage output as its input. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedPrivate
open scoped Classical
variable {ι κ : Type} {rows width : ℕ}

def outputAnchor (anchor : κ → QMAGridCell rows width) (p : κ × Fin 4) := anchor p.1

theorem output_near (xs : κ → List ι)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    (h : QuantumOrderedSpatial.Near xs cell anchor) :
    QuantumOrderedSpatial.Near (outputSites xs) (qmaMediatorCell cell anchor)
      (outputAnchor anchor) :=
  QuantumOrderedSpatial.subdivision_near xs 1 cell anchor h

variable [Fintype ι] [Fintype κ]

theorem output_density (cell : ι → QMAGridCell rows width)
    (anchor : κ → QMAGridCell rows width) {A B : ℕ}
    (hc : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B) :
    (∀ p, (Finset.univ.filter (fun q : ι ⊕ κ => qmaMediatorCell cell anchor q = p)).card
      ≤ A+B) ∧
    (∀ p, (Finset.univ.filter (fun e : κ × Fin 4 => outputAnchor anchor e = p)).card
      ≤ 4*B) := by
  constructor
  · intro p
    rw [qmaSumFilter_card]
    exact Nat.add_le_add (hc p) (ha p)
  · intro p
    change (Finset.univ.filter (fun e : κ × Fin 4 => anchor e.1 = p)).card ≤ _
    exact (qmaProdFilter_card 4 (fun e => anchor e = p)).trans_le
      (Nat.mul_le_mul_left _ (ha p))

variable [DecidableEq ι] [DecidableEq κ]

theorem pipeline_near (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hlen : ∀ e, (xs e).length ≤ 6)
    (cell : ι → QMAGridCell rows width) (anchor : κ → QMAGridCell rows width)
    (h : QuantumOrderedSpatial.Near xs cell anchor) :
    QuantumOrderedSpatial.Near (outputSites (QuantumOrderedXZ.sites xs w))
      (qmaMediatorCell (QuantumOrderedSpatial.outputCell cell anchor)
        (QuantumOrderedSpatial.outputAnchor anchor))
      (outputAnchor (QuantumOrderedSpatial.outputAnchor anchor)) :=
  output_near _ _ _ (QuantumOrderedSpatial.output_near xs w hlen cell anchor h)

omit [DecidableEq ι] [DecidableEq κ] in
theorem pipeline_density (cell : ι → QMAGridCell rows width)
    (anchor : κ → QMAGridCell rows width) {A B : ℕ}
    (hc : ∀ p, (Finset.univ.filter (fun q => cell q = p)).card ≤ A)
    (ha : ∀ p, (Finset.univ.filter (fun e => anchor e = p)).card ≤ B) :
    (∀ p, (Finset.univ.filter (fun q => qmaMediatorCell
      (QuantumOrderedSpatial.outputCell cell anchor)
      (QuantumOrderedSpatial.outputAnchor anchor) q = p)).card ≤ A+3717*B) ∧
    (∀ p, (Finset.univ.filter (fun e =>
      outputAnchor (QuantumOrderedSpatial.outputAnchor anchor) e = p)).card ≤ 12544*B) := by
  obtain ⟨h1,h2⟩ := QuantumOrderedSpatial.output_density cell anchor hc ha
  obtain ⟨h3,h4⟩ := output_density _ _ h1 h2
  constructor
  · intro p
    exact (h3 p).trans_eq (by omega)
  · intro p
    exact (h4 p).trans_eq (by omega)

end ContinuumCoulomb.QuantumOrderedPrivate

end

end OAI

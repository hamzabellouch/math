import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSubdivisionSites

namespace OAI

/-! The literal rational six-to-four-to-three-local compiler.  Every
intermediate word retains its ordered site list, and the estimate compares
the ordinary full Hilbert-space ground energies. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedTwoStage
open QuantumOrderedSubdivision
open scoped Classical
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def firstWord (xs : κ → List ι) (w : κ → ι → Fin 4) := outputWord xs 3 w
def firstSites (xs : κ → List ι) := outputSites xs 3
def firstCoefficient (J : κ → ℚ) (N : ℕ) := outputCoefficient J N

def word (xs : κ → List ι) (w : κ → ι → Fin 4) :=
  outputWord (firstSites xs) 2 (firstWord xs w)

def sites (xs : κ → List ι) := outputSites (firstSites xs) 2

def coefficient (J : κ → ℚ) (N : ℕ) :=
  outputCoefficient (firstCoefficient J N) N

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem sites_nodup (xs : κ → List ι) (hx : ∀ e, (xs e).Nodup)
    (p : (κ × Fin 4) × Fin 4) : (sites xs p).Nodup :=
  outputSites_nodup _ _ (outputSites_nodup xs 3 hx) p

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem sites_length (xs : κ → List ι) (hx : ∀ e, (xs e).length ≤ 6)
    (p : (κ × Fin 4) × Fin 4) : (sites xs p).length ≤ 3 := by
  apply outputSites_length _ 2
  intro e
  exact outputSites_length xs 3 hx e

theorem support_cover (xs : κ → List ι) (w : κ → ι → Fin 4)
    (p : (κ × Fin 4) × Fin 4) : qmaPauliSupport (word xs w p) ⊆ (sites xs p).toFinset :=
  outputSites_cover _ _ _ p

theorem support (xs : κ → List ι) (hx : ∀ e, (xs e).length ≤ 6)
    (w : κ → ι → Fin 4) (p : (κ × Fin 4) × Fin 4) :
    (qmaPauliSupport (word xs w p)).card ≤ 3 :=
  (Finset.card_le_card (support_cover xs w p)).trans
    ((List.toFinset_card_le _).trans (sites_length xs hx p))

theorem even (xs : κ → List ι) (w : κ → ι → Fin 4)
    (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (he : ∀ e, Even (qmaPauliYCount (w e))) (p : (κ × Fin 4) × Fin 4) :
    Even (qmaPauliYCount (word xs w p)) :=
  output_even _ _ _ (outputSites_nodup xs 3 hx) (outputSites_cover xs 3 w)
    (output_even xs 3 w hx hcover he) p

theorem accuracy (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hx : ∀ e, (xs e).Nodup)
    (hcover : ∀ e, qmaPauliSupport (w e) ⊆ (xs e).toFinset)
    (N : ℕ) (hN : 1 ≤ N) :
    |MediatorGraph.normalizedBottom (qmaPauliFamily (word xs w)
        (fun p => (coefficient J N p:ℝ)))-
      MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| ≤ 2/(N:ℝ) := by
  have hfirst := output_accuracy xs 3 w J hx hcover N hN
  have hsecond := output_accuracy (firstSites xs) 2 (firstWord xs w)
    (firstCoefficient J N) (outputSites_nodup xs 3 hx) (outputSites_cover xs 3 w) N hN
  calc
    _ ≤ |MediatorGraph.normalizedBottom (qmaPauliFamily (word xs w)
          (fun p => (coefficient J N p:ℝ)))-
        MediatorGraph.normalizedBottom (qmaPauliFamily (firstWord xs w)
          (fun p => (firstCoefficient J N p:ℝ)))|+
        |MediatorGraph.normalizedBottom (qmaPauliFamily (firstWord xs w)
          (fun p => (firstCoefficient J N p:ℝ)))-
        MediatorGraph.normalizedBottom (qmaPauliFamily w (fun e => (J e:ℝ)))| :=
      abs_sub_le _ _ _
    _ ≤ 1/(N:ℝ)+1/(N:ℝ) := add_le_add hsecond hfirst
    _ = 2/(N:ℝ) := by ring

end ContinuumCoulomb.QuantumOrderedTwoStage

end

end OAI

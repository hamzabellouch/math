import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedLabelCorrectness

namespace OAI

/-! The complete literal sparse-label compiler equals the actual ordered
six-to-four-to-three-to-two-to-XZ construction and private-pair stage. -/

noncomputable section
namespace ContinuumCoulomb.QuantumOrderedLabelTable
open scoped Classical

variable {ι κ : Type} {m n : ℕ}

def terms1 (e : Fin m ≃ κ) := nextTerm e 4
def terms2 (e : Fin m ≃ κ) := nextTerm (terms1 e) 4
def terms3 (e : Fin m ≃ κ) := nextTerm (terms2 e) 7
def terms4 (e : Fin m ≃ κ) := nextTerm (terms3 e) 4
def terms5 (e : Fin m ≃ κ) := nextTerm (terms4 e) 7
def terms6 (e : Fin m ≃ κ) := nextTerm (terms5 e) 4

def qubits1 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit q e
def qubits2 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit (qubits1 q e) (terms1 e)
def qubits3 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit (qubits2 q e) (terms2 e)
def qubits4 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit (qubits3 q e) (terms3 e)
def qubits5 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit (qubits4 q e) (terms4 e)
def qubits6 (q : Fin n ≃ ι) (e : Fin m ≃ κ) := nextQubit (qubits5 q e) (terms5 e)

def finalCount (n m : ℕ) : ℕ :=
  n+m+m*4+m*4*4+m*4*4*7+m*4*4*7*4+m*4*4*7*4*7

theorem finalCount_eq (n m : ℕ) : finalCount n m=n+3717*m := by
  unfold finalCount
  omega

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem output_table (q : Fin n ≃ ι) (e : Fin m ≃ κ)
    (xs : κ → List ι) (w : κ → ι → Fin 4) (J : κ → ℚ)
    (hlen : ∀ a, (xs a).length ≤ 6) (hx : ∀ a, (xs a).Nodup) (N : ℕ) :
    QuantumOrderedLabelPipeline.output (N,n,table e (index q) xs w J) =
      (finalCount n m,table (terms6 e) (index (qubits6 q e))
        (QuantumOrderedPrivate.outputSites (QuantumOrderedXZ.sites xs w))
        (QuantumOrderedPrivate.outputWord (QuantumOrderedXZ.sites xs w)
          (QuantumOrderedXZ.word xs w))
        (QuantumOrderedPrivate.outputCoefficient (QuantumOrderedXZ.coefficient J N) N)) := by
  have h1 := subdivision_table q e xs w J hx N 3
  have h2 := subdivision_table (qubits1 q e) (terms1 e)
    (QuantumOrderedSubdivision.outputSites xs 3)
    (QuantumOrderedSubdivision.outputWord xs 3 w)
    (QuantumOrderedSubdivision.outputCoefficient J N)
    (QuantumOrderedSubdivision.outputSites_nodup xs 3 hx) N 2
  have h3 := third_table (qubits2 q e) (terms2 e)
    (QuantumOrderedXZ.threeSites xs) (QuantumOrderedXZ.threeWord xs w)
    (QuantumOrderedXZ.threeCoefficient J N)
    (QuantumOrderedXZ.threeSites_length xs hlen) (QuantumOrderedXZ.threeSites_nodup xs hx) N
  have h4 := yy_table (qubits3 q e) (terms3 e)
    (QuantumOrderedXZ.twoSites xs w) (QuantumOrderedXZ.twoWord xs w)
    (QuantumOrderedXZ.twoCoefficient J N)
    (QuantumOrderedXZ.twoSites_nodup xs w hlen hx) N
  have h5 := third_table (qubits4 q e) (terms4 e)
    (QuantumOrderedXZ.xzThreeSites xs w) (QuantumOrderedXZ.xzThreeWord xs w)
    (QuantumOrderedXZ.xzThreeCoefficient J N)
    (QuantumOrderedXZ.xzThreeSites_length xs w hlen)
    (QuantumOrderedXZ.xzThreeSites_nodup xs w hlen hx) N
  have h6 := private_table (qubits5 q e) (terms5 e)
    (QuantumOrderedXZ.sites xs w) (QuantumOrderedXZ.word xs w)
    (QuantumOrderedXZ.coefficient J N) N
  change _ = (N,n+m,table (terms1 e) (index (qubits1 q e))
    (QuantumOrderedSubdivision.outputSites xs 3)
    (QuantumOrderedSubdivision.outputWord xs 3 w)
    (QuantumOrderedSubdivision.outputCoefficient J N)) at h1
  change _ = (N,n+m+m*4,table (terms2 e) (index (qubits2 q e))
    (QuantumOrderedXZ.threeSites xs) (QuantumOrderedXZ.threeWord xs w)
    (QuantumOrderedXZ.threeCoefficient J N)) at h2
  change _ = (N,n+m+m*4+m*4*4,table (terms3 e) (index (qubits3 q e))
    (QuantumOrderedXZ.twoSites xs w) (QuantumOrderedXZ.twoWord xs w)
    (QuantumOrderedXZ.twoCoefficient J N)) at h3
  change _ = (N,n+m+m*4+m*4*4+m*4*4*7,table (terms4 e) (index (qubits4 q e))
    (QuantumOrderedXZ.xzThreeSites xs w) (QuantumOrderedXZ.xzThreeWord xs w)
    (QuantumOrderedXZ.xzThreeCoefficient J N)) at h4
  change _ = (N,n+m+m*4+m*4*4+m*4*4*7+m*4*4*7*4,
    table (terms5 e) (index (qubits5 q e))
    (QuantumOrderedXZ.sites xs w) (QuantumOrderedXZ.word xs w)
    (QuantumOrderedXZ.coefficient J N)) at h5
  unfold QuantumOrderedLabelPipeline.output
  rw [h1,h2,h3,h4,h5,h6]
  rfl

end ContinuumCoulomb.QuantumOrderedLabelTable

end

end OAI

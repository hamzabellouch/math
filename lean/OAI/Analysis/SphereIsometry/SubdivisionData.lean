import OAI.Analysis.SphereIsometry.BarycentricFlags

namespace OAI

/-! # The concrete recursively iterated subdivision of a finite simplex -/

noncomputable section

namespace Tingley

structure CarrierComplex (I : Type) [DecidableEq I] where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  [vertexDecidableEq : DecidableEq Vertex]
  complex : FiniteComplex Vertex
  carrier : Vertex → Finset I

attribute [instance] CarrierComplex.vertexFintype CarrierComplex.vertexDecidableEq

namespace CarrierComplex

variable {I : Type} [DecidableEq I]

def sd (D : CarrierComplex I) : CarrierComplex I where
  Vertex := FiniteComplex.FaceVertex D.complex
  complex := D.complex.sd
  carrier := D.complex.sdCarrier D.carrier

def initial (I : Type) [Fintype I] [DecidableEq I] : CarrierComplex I where
  Vertex := I
  complex := FiniteComplex.full
  carrier := fun i => {i}

end CarrierComplex

def iterData (I : Type) [Fintype I] [DecidableEq I] : ℕ → CarrierComplex I
  | 0 => CarrierComplex.initial I
  | n + 1 => (iterData I n).sd

abbrev IterVertex (m k : ℕ) := (iterData (Fin (m + 1)) k).Vertex

def iterComplex (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.faces

def iterCarrier (m k : ℕ) : IterVertex m k → Finset (Fin (m + 1)) :=
  (iterData (Fin (m + 1)) k).carrier

def topCells (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.topCells m

def codimFaces (m k : ℕ) : Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.codimFaces m

def faceCarrier (m k : ℕ) (s : Finset (IterVertex m k)) : Finset (Fin (m + 1)) :=
  FiniteComplex.faceCarrier (iterCarrier m k) s

def incidentTop (m k : ℕ) (s : Finset (IterVertex m k)) :
    Finset (Finset (IterVertex m k)) :=
  (iterData (Fin (m + 1)) k).complex.incidentTop m s

@[simp] theorem mem_topCells {m k : ℕ} {s : Finset (IterVertex m k)} :
    s ∈ topCells m k ↔ s ∈ iterComplex m k ∧ s.card = m + 1 :=
  FiniteComplex.mem_topCells

@[simp] theorem mem_codimFaces {m k : ℕ} {s : Finset (IterVertex m k)} :
    s ∈ codimFaces m k ↔ s ∈ iterComplex m k ∧ s.card = m :=
  FiniteComplex.mem_codimFaces

@[simp] theorem mem_incidentTop {m k : ℕ} {s t : Finset (IterVertex m k)} :
    t ∈ incidentTop m k s ↔
      t ∈ iterComplex m k ∧ t.card = m + 1 ∧ s ⊆ t :=
  FiniteComplex.mem_incidentTop

theorem iterComplex_empty_mem (m k : ℕ) : ∅ ∈ iterComplex m k :=
  (iterData (Fin (m + 1)) k).complex.empty_mem

theorem iterComplex_down_closed {m k : ℕ} {s t : Finset (IterVertex m k)}
    (hs : s ∈ iterComplex m k) (ht : t ⊆ s) : t ∈ iterComplex m k :=
  (iterData (Fin (m + 1)) k).complex.down_closed hs ht

theorem iterData_carrier_nonempty (I : Type) [Fintype I] [DecidableEq I] (k : ℕ) :
    ∀ v : (iterData I k).Vertex, ((iterData I k).carrier v).Nonempty := by
  induction k with
  | zero => intro v; exact Finset.singleton_nonempty v
  | succ k ih => exact FiniteComplex.sdCarrier_nonempty ih

theorem iterData_card_le_carrier (I : Type) [Fintype I] [DecidableEq I] (k : ℕ) :
    ∀ s ∈ (iterData I k).complex.faces,
      s.card ≤ (FiniteComplex.faceCarrier (iterData I k).carrier s).card := by
  induction k with
  | zero =>
      intro s hs
      simp [iterData, CarrierComplex.initial, FiniteComplex.faceCarrier]
      exact (congrArg (fun t : Finset I => t.card)
        (Finset.biUnion_singleton_eq_self (s := s))).ge
  | succ k ih =>
      intro s hs
      exact FiniteComplex.sd_card_le_carrier ih hs

theorem iter_card_le_carrier {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ iterComplex m k) : s.card ≤ (faceCarrier m k s).card :=
  iterData_card_le_carrier (Fin (m + 1)) k s hs

theorem iter_card_le {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ iterComplex m k) : s.card ≤ m + 1 := by
  have h := (iter_card_le_carrier hs).trans (Finset.card_le_univ (faceCarrier m k s))
  simpa using h

theorem top_faceCarrier {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ topCells m k) : faceCarrier m k s = Finset.univ := by
  obtain ⟨hs, hcard⟩ := mem_topCells.mp hs
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa [hcard] using iter_card_le_carrier hs

theorem codim_faceCarrier_card {m k : ℕ} {s : Finset (IterVertex m k)}
    (hs : s ∈ codimFaces m k) :
    (faceCarrier m k s).card = m ∨ (faceCarrier m k s).card = m + 1 := by
  obtain ⟨hs, hcard⟩ := mem_codimFaces.mp hs
  have hlo := iter_card_le_carrier hs
  have hhi : (faceCarrier m k s).card ≤ m + 1 := by
    simpa using Finset.card_le_univ (faceCarrier m k s)
  omega

end Tingley

end

end OAI

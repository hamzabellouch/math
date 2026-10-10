import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

namespace OAI

/-!
# Finite complexes and their actual face-chain subdivision

The empty face is included. A subdivision vertex is always a nonempty old
face, and a subdivision face is an actual finite inclusion-chain.
-/

noncomputable section

namespace Tingley

universe u v

structure FiniteComplex (V : Type u) [Fintype V] [DecidableEq V] where
  faces : Finset (Finset V)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces

namespace FiniteComplex

variable {V : Type u} [Fintype V] [DecidableEq V]

def full : FiniteComplex V where
  faces := Finset.univ
  empty_mem := Finset.mem_univ _
  down_closed := fun _ _ => Finset.mem_univ _

@[simp] theorem mem_full (s : Finset V) : s ∈ (full : FiniteComplex V).faces :=
  Finset.mem_univ _

abbrev FaceVertex (K : FiniteComplex V) :=
  {s : Finset V // s ∈ K.faces ∧ s.Nonempty}

instance (K : FiniteComplex V) : Fintype (FaceVertex K) := by
  classical
  unfold FaceVertex
  infer_instance

def chain (K : FiniteComplex V) (c : Finset (FaceVertex K)) : Prop :=
  ∀ a ∈ c, ∀ b ∈ c, a.val ⊆ b.val ∨ b.val ⊆ a.val

theorem chain_mono {K : FiniteComplex V} {c d : Finset (FaceVertex K)}
    (hc : K.chain c) (hd : d ⊆ c) : K.chain d :=
  fun a ha b hb => hc a (hd ha) b (hd hb)

def sd (K : FiniteComplex V) : FiniteComplex (FaceVertex K) := by
  classical
  exact
    { faces := Finset.univ.filter K.chain
      empty_mem := by simp [chain]
      down_closed := by
        intro s t hs hts
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, K.chain_mono (Finset.mem_filter.mp hs).2 hts⟩ }

@[simp] theorem mem_sd_iff {K : FiniteComplex V} {c : Finset (FaceVertex K)} :
    c ∈ K.sd.faces ↔ K.chain c := by
  classical
  simp [sd]

def topCells (K : FiniteComplex V) (m : ℕ) : Finset (Finset V) :=
  K.faces.filter (fun s => s.card = m + 1)

def codimFaces (K : FiniteComplex V) (m : ℕ) : Finset (Finset V) :=
  K.faces.filter (fun s => s.card = m)

def incidentTop (K : FiniteComplex V) (m : ℕ) (s : Finset V) : Finset (Finset V) :=
  (K.topCells m).filter (fun t => s ⊆ t)

@[simp] theorem mem_topCells {K : FiniteComplex V} {m : ℕ} {s : Finset V} :
    s ∈ K.topCells m ↔ s ∈ K.faces ∧ s.card = m + 1 :=
  Finset.mem_filter

@[simp] theorem mem_codimFaces {K : FiniteComplex V} {m : ℕ} {s : Finset V} :
    s ∈ K.codimFaces m ↔ s ∈ K.faces ∧ s.card = m :=
  Finset.mem_filter

@[simp] theorem mem_incidentTop {K : FiniteComplex V} {m : ℕ}
    {s t : Finset V} :
    t ∈ K.incidentTop m s ↔ t ∈ K.faces ∧ t.card = m + 1 ∧ s ⊆ t := by
  simp [incidentTop, and_assoc]

def CardBound (K : FiniteComplex V) (m : ℕ) : Prop :=
  ∀ s ∈ K.faces, s.card ≤ m + 1

def Pure (K : FiniteComplex V) (m : ℕ) : Prop :=
  ∀ s ∈ K.faces, ∃ t ∈ K.topCells m, s ⊆ t

theorem Pure.cardBound {K : FiniteComplex V} {m : ℕ} (h : K.Pure m) :
    K.CardBound m := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := h s hs
  exact (Finset.card_le_card hst).trans_eq (mem_topCells.mp ht).2

variable {I : Type v} [DecidableEq I]

def faceCarrier (carrier : V → Finset I) (s : Finset V) : Finset I :=
  s.biUnion carrier

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_faceCarrier {carrier : V → Finset I} {s : Finset V} {i : I} :
    i ∈ faceCarrier carrier s ↔ ∃ v ∈ s, i ∈ carrier v :=
  Finset.mem_biUnion

omit [Fintype V] [DecidableEq V] in
theorem faceCarrier_mono (carrier : V → Finset I) {s t : Finset V} (h : s ⊆ t) :
    faceCarrier carrier s ⊆ faceCarrier carrier t :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

omit [Fintype V] [DecidableEq V] in
@[simp] theorem faceCarrier_empty (carrier : V → Finset I) :
    faceCarrier carrier ∅ = ∅ := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem faceCarrier_singleton (carrier : V → Finset I) (v : V) :
    faceCarrier carrier {v} = carrier v := by
  simp [faceCarrier]

def sdCarrier (K : FiniteComplex V) (carrier : V → Finset I) :
    FaceVertex K → Finset I := fun s => faceCarrier carrier s.val

theorem sdCarrier_nonempty {K : FiniteComplex V} {carrier : V → Finset I}
    (h : ∀ v, (carrier v).Nonempty) (s : FaceVertex K) :
    (K.sdCarrier carrier s).Nonempty := by
  obtain ⟨v, hv⟩ := s.property.2
  obtain ⟨i, hi⟩ := h v
  exact ⟨i, mem_faceCarrier.mpr ⟨v, hv, hi⟩⟩

end FiniteComplex

end Tingley

end

end OAI

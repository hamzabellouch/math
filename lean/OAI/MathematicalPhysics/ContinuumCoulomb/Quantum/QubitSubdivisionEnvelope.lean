import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionHermitian

namespace OAI

/-! Explicit small supports for each subdivision piece remain inside its source envelope. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def qmaMediatorSupport (S : Finset ι) (e : κ) : Finset (ι ⊕ κ) :=
  S.map Function.Embedding.inl ∪ ({e} : Finset κ).map Function.Embedding.inr

omit [Fintype ι] [Fintype κ] in
theorem qmaMediatorSupport_card (S : Finset ι) (e : κ) :
    (qmaMediatorSupport S e).card ≤ S.card+1 := by
  have h := Finset.card_union_le (S.map (Function.Embedding.inl : ι ↪ ι ⊕ κ))
    (({e} : Finset κ).map Function.Embedding.inr)
  simpa only [qmaMediatorSupport,Finset.card_map,Finset.card_singleton] using h

omit [Fintype ι] [Fintype κ] in
theorem qmaMediatorSupport_mono {S T : Finset ι} (h : S ⊆ T) (e : κ) :
    qmaMediatorSupport S e ⊆ qmaMediatorSupport T e :=
  Finset.union_subset_union (Finset.map_subset_map.mpr h) (Finset.Subset.refl _)

def qmaSubdivisionPieceSites (SA SB : Finset ι) (e : κ) : Fin 4 → Finset (ι ⊕ κ) :=
  ![qmaMediatorSupport ∅ e,∅,qmaMediatorSupport SA e,qmaMediatorSupport SB e]

theorem qmaSubdivisionPieceSites_local (A B : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) {SA SB : Finset ι}
    (hA : QMALocalOn SA A) (hB : QMALocalOn SB B) (k : Fin 4) :
    QMALocalOn (qmaSubdivisionPieceSites SA SB e k) (qmaSubdivisionLocalPiece A B e R j m k) := by
  fin_cases k
  · exact ((qmaLocal_identity (∅ : Finset ι)).join (qmaOccupation_local e)).real_smul (R^2)
  · exact (qmaLocal_identity (∅ : Finset (ι ⊕ κ))).real_smul (1+(j/2)^2)
  · exact (hA.join (qmaPolarizedFlip_local m e)).real_smul R
  · exact (hB.join (qmaPolarizedFlip_local m e)).real_smul (-R*j/2)

omit [Fintype ι] [Fintype κ] in
theorem qmaSubdivisionPieceSites_card {SA SB : Finset ι} {d : ℕ}
    (hA : SA.card ≤ d) (hB : SB.card ≤ d) (e : κ) (k : Fin 4) :
    (qmaSubdivisionPieceSites SA SB e k).card ≤ d+1 := by
  fin_cases k
  · exact (qmaMediatorSupport_card ∅ e).trans (by simp)
  · simp [qmaSubdivisionPieceSites]
  · exact (qmaMediatorSupport_card SA e).trans (Nat.add_le_add_right hA 1)
  · exact (qmaMediatorSupport_card SB e).trans (Nat.add_le_add_right hB 1)

omit [Fintype ι] [Fintype κ] in
theorem qmaSubdivisionPieceSites_subset {SA SB S : Finset ι}
    (hA : SA ⊆ S) (hB : SB ⊆ S) (e : κ) (k : Fin 4) :
    qmaSubdivisionPieceSites SA SB e k ⊆ qmaMediatorSupport S e := by
  fin_cases k
  · exact qmaMediatorSupport_mono (Finset.empty_subset S) e
  · exact Finset.empty_subset _
  · exact qmaMediatorSupport_mono hA e
  · exact qmaMediatorSupport_mono hB e

end ContinuumCoulomb

end

end OAI

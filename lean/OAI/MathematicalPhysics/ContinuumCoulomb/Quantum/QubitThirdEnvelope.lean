import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitThirdPhasedLocal
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitSubdivisionEnvelope

namespace OAI

/-! Explicit two-site supports for the seven third-order pieces. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped Classical
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def qmaThirdPieceSites (SA SB SC : Finset ι) (e : κ) : Fin 7 → Finset (ι ⊕ κ) :=
  ![qmaMediatorSupport ∅ e,∅,(SA ∪ SB).map Function.Embedding.inl,
    SC.map Function.Embedding.inl,qmaMediatorSupport SC e,
    qmaMediatorSupport SA e,qmaMediatorSupport SB e]

theorem qmaThirdPieceSites_local (A B C : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (e : κ) (R j : ℝ) (m : κ → Bool) {SA SB SC : Finset ι}
    (hA : QMALocalOn SA A) (hB : QMALocalOn SB B) (hC : QMALocalOn SC C) (k : Fin 7) :
    QMALocalOn (qmaThirdPieceSites SA SB SC e k) (qmaThirdPhasedLocalPiece A B C e R j m k) := by
  rw [qmaThirdPhasedLocalPiece_eq]
  fin_cases k
  · exact ((qmaLocal_identity (∅ : Finset ι)).join (qmaOccupation_local e)).real_smul (R^3)
  · exact (qmaLocal_identity (∅ : Finset (ι ⊕ κ))).real_smul (R*(1+(j/2)^2))
  · exact ((hA.mono Finset.subset_union_left).mul
      (hB.mono Finset.subset_union_right)).joinLeft.real_smul (R*j)
  · exact hC.joinLeft.real_smul (-(1+(j/2)^2))
  · exact (hC.join (qmaOccupation_local e)).real_smul (R^2)
  · exact (hA.join (qmaPolarizedFlip_local m e)).real_smul (R^2)
  · exact (hB.join (qmaPolarizedFlip_local m e)).real_smul (R^2*j/2)

omit [Fintype ι] [Fintype κ] in
theorem qmaThirdPieceSites_card {SA SB SC : Finset ι}
    (hA : SA.card ≤ 1) (hB : SB.card ≤ 1) (hC : SC.card ≤ 1) (e : κ) (k : Fin 7) :
    (qmaThirdPieceSites SA SB SC e k).card ≤ 2 := by
  fin_cases k
  · exact (qmaMediatorSupport_card ∅ e).trans (by simp)
  · simp [qmaThirdPieceSites]
  · change ((SA ∪ SB).map (Function.Embedding.inl : ι ↪ ι ⊕ κ)).card ≤ 2
    rw [Finset.card_map]
    exact (Finset.card_union_le SA SB).trans (by omega)
  · change (SC.map (Function.Embedding.inl : ι ↪ ι ⊕ κ)).card ≤ 2
    rw [Finset.card_map]
    omega
  · exact (qmaMediatorSupport_card SC e).trans (by omega)
  · exact (qmaMediatorSupport_card SA e).trans (by omega)
  · exact (qmaMediatorSupport_card SB e).trans (by omega)

omit [Fintype ι] [Fintype κ] in
theorem qmaThirdPieceSites_subset {SA SB SC S : Finset ι}
    (hA : SA ⊆ S) (hB : SB ⊆ S) (hC : SC ⊆ S) (e : κ) (k : Fin 7) :
    qmaThirdPieceSites SA SB SC e k ⊆ qmaMediatorSupport S e := by
  have hm {T : Finset ι} (hT : T ⊆ S) :
      T.map (Function.Embedding.inl : ι ↪ ι ⊕ κ) ⊆ qmaMediatorSupport S e :=
    (Finset.map_subset_map.mpr hT).trans Finset.subset_union_left
  fin_cases k
  · exact qmaMediatorSupport_mono (Finset.empty_subset S) e
  · exact Finset.empty_subset _
  · exact hm (Finset.union_subset hA hB)
  · exact hm hC
  · exact qmaMediatorSupport_mono hC e
  · exact qmaMediatorSupport_mono hA e
  · exact qmaMediatorSupport_mono hB e

end ContinuumCoulomb

end

end OAI

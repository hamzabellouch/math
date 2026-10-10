import OAI.Analysis.LipschitzHilbert.Packets.PacketDataMaskedBand
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceMasked

namespace OAI

/-! Recentring an entire already-selected top family preserves its
physical length bands. Only the literal short-cone membership is needed. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem referenceFamily_physicalMaskedBand_all (P : PacketLatticeData N κ Label Item)
    (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (hcondition : ∀ u : P.PacketIndex,
      P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ) (j : Fin N) :
    let Q := P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
    let orig := P.referenceOriginalLabel oldSlope newSlope R cone w
    Q.physicalMaskedBand (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l))
      L A (z.2-newSlope*z.1) j z.1 =
    P.physicalMaskedBand alt hAlt oldSlope b v f T L A (z.2-oldSlope*z.1) j z.1 := by
  intro Q orig
  have hpoint (s : ℝ) : (z.1,z.2-s*z.1+s*z.1) = z := by
    apply Prod.ext
    · rfl
    · dsimp
      ring
  have hQ := Q.physicalMaskedValue_length_sum (fun j l => alt j (orig j l))
    (fun j l => hAlt j (orig j l)) newSlope (fun j l => b j (orig j l)) v f
    (fun j l => T j (orig j l)) L A (z.2-newSlope*z.1) z.1 j
  rw [hpoint newSlope] at hQ
  have hP := P.physicalMaskedValue_length_sum alt hAlt oldSlope b v f T L A
    (z.2-oldSlope*z.1) z.1 j
  rw [hpoint oldSlope] at hP
  apply hQ.symm.trans
  apply Eq.trans _ hP
  have h := P.sum_referenceFamily_selected oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency Finset.univ
    (fun u => if u.1 = j then P.physicalMaskedValue alt hAlt oldSlope b v f T L A z u else 0)
    (fun u _ => hcondition u)
  simp only [Finset.sum_filter,Finset.mem_univ,ite_true] at h
  simp only [Finset.sum_filter]
  calc
    _ = ∑ q : Q.PacketIndex, if q.1 = j then
        P.physicalMaskedValue alt hAlt oldSlope b v f T L A z
          ⟨q.1,⟨orig q.1 q.2.1,q.2.2⟩⟩ else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      split_ifs
      · exact P.referenceFamily_physicalMaskedValue oldSlope newSlope R cone w F
          hw hcone hF hwide hfrequency alt hAlt b v f T L A z q
      · rfl
    _ = _ := by convert h using 1

end LipschitzHilbert.PacketLatticeData

end

end OAI

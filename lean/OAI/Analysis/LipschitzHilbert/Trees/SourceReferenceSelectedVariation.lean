import OAI.Analysis.LipschitzHilbert.Trees.SourceReferencePhysicalIdentity
import OAI.Analysis.LipschitzHilbert.Trees.SourceSelectedGoodEvent

namespace OAI

/-! A good event in recentered reference coordinates bounds the original
selected stopping prefix exactly, including its clamped variation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w
variable (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
  (f : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)

theorem referenceFamily_selectedPhysicalPrefix
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (stop : Fin N → ℕ) (z : ℝ×ℝ) :
    (Q).selectedPhysicalPrefix (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l)) L A
      ((Finset.univ : Finset (Q).PacketIndex).filter
        (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)) stop z =
      P.selectedPhysicalPrefix alt hAlt oldSlope b v f T L A S stop z := by
  unfold selectedPhysicalPrefix
  congr 1
  funext k
  have hs := P.sum_referenceFamily_selected oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency S
    (fun u => if stop u.1 = k then P.physicalMaskedValue alt hAlt oldSlope b v f T L A z u
      else 0) hS
  simp only [Finset.sum_filter] at hs ⊢
  simp_rw [P.referenceFamily_physicalMaskedValue oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f T L A z]
  exact hs

/-- The reference good event controls every original selected prefix
after recentering, with no angular-horizon or label-count factor. -/
theorem referenceFamily_selected_good_bound
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (stop : Fin N → ℕ) (hstop : Antitone stop) (a e s r : ℝ) (z : ℝ×ℝ)
    (hgood : z ∉ ((Q).restrictPackets ((Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S))).physicalReferenceBad
      ((Q).restrictedAlternate (fun j l => alt j (orig j l)) _)
      ((Q).restrictedAlternate_bound (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l)) _)
      newSlope a (fun j l => b j (orig j l)) v f (fun j l u => T j (orig j l) u.val)
      L A e s r) (H : ℕ) :
    finiteCubicVariation (fun k => P.selectedPhysicalPrefix alt hAlt oldSlope b v f T L A
      S stop z (min k H)) (2*H) ≤ (L^r)^3 := by
  have h := (Q).selectedPhysicalPrefix_good_event_bound
    (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l)) newSlope a
    (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l)) L A e s r
    ((Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S)) stop hstop z hgood H
  simpa only [P.referenceFamily_selectedPhysicalPrefix oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f T L A S hS stop z] using h

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

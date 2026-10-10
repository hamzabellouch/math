import OAI.Analysis.LipschitzHilbert.Packets.PacketLatticeRestriction
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataReferenceConditions

namespace OAI

/-! The physical selector centers are invariant under recentering.
Restricting to the reference cone can only decrease their local count. -/

noncomputable section
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physical_center (j : Fin N) (l : (Q).labels j) :
    newSlope+(Q).rowSlope j l = oldSlope+P.rowSlope j (orig j l) := by
  change newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) = _
  ring

theorem referenceFamily_localMultiplicity (j : Fin N) (d : ℝ) (M : ℕ)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) d M) :
    SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : (Q).labels j => newSlope+(Q).rowSlope j l) d M := by
  intro a
  apply (Finset.card_le_card_of_injOn (orig j) ?_ ?_).trans (hlocal a)
  · intro l hl
    obtain ⟨_,hlo,hhi⟩ := Finset.mem_filter.mp hl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · change a ≤ newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) at hlo
      change a ≤ oldSlope+P.rowSlope j (orig j l)
      linarith
    · change newSlope+(P.rowSlope j (orig j l)+(oldSlope-newSlope)) < a+d at hhi
      change oldSlope+P.rowSlope j (orig j l) < a+d
      linarith
  · intro l _ m _ heq
    apply Subtype.ext
    exact congrArg (fun u : P.labels j => u.val) heq

theorem referenceFamily_selector_support
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (radius d : Fin N → ℝ)
    (hsupport : ∀ j l k s, b j l k s ≠ 0 →
      |s-(oldSlope+P.rowSlope j l)| ≤ radius j*d j) :
    ∀ j (l : (Q).labels j) k s, b j (orig j l) k s ≠ 0 →
      |s-(newSlope+(Q).rowSlope j l)| ≤ radius j*d j := by
  intro j l k s hb
  rw [P.referenceFamily_physical_center oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l]
  exact hsupport j (orig j l) k s hb

theorem referenceFamily_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l)) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u :=
  P.referenceFamily_multiplier_coefficient oldSlope newSlope R cone w F hw hcone hF hwide hfrequency b v f j l u

theorem referenceFamily_alternate_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) :
    ((Q).withProfile (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))).physicalPacket
      newSlope j l u k = (P.withProfile alt hAlt).physicalPacket oldSlope j (orig j l) u k :=
  (P.withProfile alt hAlt).referenceFamily_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l u k

theorem referenceFamily_spectrum (cStar cEta CEta : ℝ)
    (hspectrum : ∀ j (l : P.labels j) (u : Item j l) k ξ η,
      planarAngularFourier (P.physicalPacket oldSlope j l u k) (ξ,η) ≠ 0 →
        |ξ+(oldSlope+P.rowSlope j l)*η| ≤ cStar/P.length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta) :
    ∀ j (l : (Q).labels j) (u : Item j l) k ξ η,
      planarAngularFourier ((Q).physicalPacket newSlope j l u k) (ξ,η) ≠ 0 →
        |ξ+(newSlope+(Q).rowSlope j l)*η| ≤ cStar/(Q).length j ∧
          cEta ≤ w*η ∧ w*η ≤ CEta := by
  intro j l u k ξ η hξ
  rw [P.referenceFamily_physicalPacket oldSlope newSlope R cone w F hw hcone hF hwide hfrequency j l u k] at hξ
  have h := hspectrum j (P.referenceOriginalLabel oldSlope newSlope R cone w j l) u k ξ η hξ
  have hs : newSlope+(P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope R cone w j l)+
      (oldSlope-newSlope)) = oldSlope+P.rowSlope j (P.referenceOriginalLabel oldSlope newSlope R cone w j l) := by ring
  change |ξ+(newSlope+(P.rowSlope j
    (P.referenceOriginalLabel oldSlope newSlope R cone w j l)+(oldSlope-newSlope)))*η| ≤
      cStar/P.length j ∧ cEta≤w*η ∧ w*η≤CEta
  rw [hs]
  exact h

/-- A selected set supported in the reference cone has the identical
sum after the literal label restriction, including empty item fibers. -/
theorem sum_referenceFamily_selected {E : Type*} [AddCommMonoid E]
    (S : Finset P.PacketIndex) (f : P.PacketIndex → E)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1) :
    (∑ u ∈ (Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S),
      f ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) = ∑ u ∈ S, f u := by
  have hs : (Finset.univ.filter fun u : P.PacketIndex => u ∈ S) = S := by
    ext u
    simp
  conv_rhs => rw [← hs,Finset.sum_filter]
  simp only [Finset.sum_filter,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  exact P.sum_referenceLabels_of_zero oldSlope newSlope R cone w j
    (fun l u => if (⟨j,⟨l,u⟩⟩ : P.PacketIndex) ∈ S then f ⟨j,⟨l,u⟩⟩ else 0)
    (by
      intro l hl u
      rw [ite_eq_right]
      exact fun hu => hl (hS ⟨j,⟨l,u⟩⟩ hu))

end LipschitzHilbert.PacketLatticeData

end

end OAI

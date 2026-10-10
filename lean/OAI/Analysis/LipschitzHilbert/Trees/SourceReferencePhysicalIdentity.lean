import OAI.Analysis.LipschitzHilbert.Packets.SourceLabeledPacketRestriction
import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceMainRestriction
import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceAmplitude

namespace OAI

/-! Recentring a selected packet family changes its reference coordinates,
while retaining the original physical analyzing coefficient, alternate
synthesis packet and assigned top mask exactly. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (oldSlope newSlope R cone w F : ℝ) (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
  (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)

local notation "Q" => P.referenceFamily oldSlope newSlope R cone w F hw hcone hF hwide hfrequency
local notation "orig" => P.referenceOriginalLabel oldSlope newSlope R cone w

theorem referenceFamily_physicalMultiplierCoefficient
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) :
    (Q).physicalMultiplierCoefficient newSlope (fun j l => b j (orig j l)) v f j l u =
      P.physicalMultiplierCoefficient oldSlope b v f j (orig j l) u := by
  ext k
  simp only [physicalMultiplierCoefficient,analyzingCoefficient,WithLp.ofLp_toLp]
  change ((↑(P.length j*P.width):ℂ)⁻¹)*
    (∫ z, f z k*conj (b j (orig j l) k (v z)*(Q).physicalPacket newSlope j l u k z)
      ∂volume.prod volume) = _
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  have hp := congrArg (fun p : SchwartzMap (ℝ×ℝ) ℂ => p z)
    (P.referenceFamily_physicalPacket oldSlope newSlope R cone w F
      hw hcone hF hwide hfrequency j l u k)
  exact congrArg (fun a : ℂ => f z k*conj (b j (orig j l) k (v z)*a)) hp

theorem referenceFamily_alternate_physicalPacket
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (j : Fin N) (l : (Q).labels j) (u : Item j l) (k : κ) :
    ((Q).withProfile (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))).physicalPacket
      newSlope j l u k = (P.withProfile alt hAlt).physicalPacket oldSlope j (orig j l) u k :=
  (P.withProfile alt hAlt).referenceFamily_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency j l u k

theorem referenceFamily_physicalMaskedValue
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (z : ℝ×ℝ)
    (u : (Q).PacketIndex) :
    (Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
      newSlope (fun j l => b j (orig j l)) v f (fun j l => T j (orig j l)) L A z u =
    P.physicalMaskedValue alt hAlt oldSlope b v f T L A z ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ := by
  ext k
  simp only [physicalMaskedValue,WithLp.ofLp_toLp]
  rw [P.referenceFamily_physicalMultiplierCoefficient oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]
  rw [P.referenceFamily_alternate_physicalPacket oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency]

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

/-- Angular amplitudes are invariant under the selected reference
change of coordinates; no top or packet multiplicity is introduced. -/
theorem referenceFamily_packetAmplitude_selected {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (grid : AngularGrid) (slope : P.PacketIndex → ℝ) (stop : P.PacketIndex → ℕ)
    (base : P.PacketIndex → E) (transition : ℕ → ℤ → ℂ) (level : ℕ) (cell : ℤ) :
    grid.packetAmplitude ((Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S))
      (fun u => slope ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩)
      (fun u => stop ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩)
      (fun u => base ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) transition level cell =
      grid.packetAmplitude S slope stop base transition level cell := by
  have h := P.sum_referenceFamily_selected oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency S
    (fun u => if grid.index level (slope u) = cell ∧ level ≤ stop u then
      grid.packetPathProduct transition level (stop u) (slope u) • base u else 0) hS
  simpa only [AngularGrid.packetAmplitude,AngularGrid.packetSet,Finset.sum_filter] using h

theorem referenceFamily_packetResidual_selected {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (grid : AngularGrid) (slope : P.PacketIndex → ℝ) (stop : P.PacketIndex → ℕ)
    (base : P.PacketIndex → E) (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) :
    grid.packetResidual ((Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S))
      (fun u => slope ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩)
      (fun u => stop ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩)
      (fun u => base ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) transition lower upper cell =
      grid.packetResidual S slope stop base transition lower upper cell := by
  have h := P.sum_referenceFamily_selected oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency S
    (fun u => if grid.index lower (slope u) = cell ∧ lower ≤ stop u then
      if stop u < upper then
        grid.packetPathProduct transition lower (stop u) (slope u) • base u else 0
      else 0) hS
  simpa only [AngularGrid.packetResidual,AngularGrid.packetSet,Finset.sum_filter] using h

/-- The physical residual identity includes the exact stopping mass and
each original top mask, after recentering at the reference direction. -/
theorem referenceFamily_physicalSourceResidual_selected {τ : Type*}
    (S : Finset P.PacketIndex)
    (hS : ∀ u ∈ S, P.referenceCondition oldSlope newSlope R cone w u.1 u.2.1)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ)
    (cutoff : ℝ) (weight : τ → (ℝ×ℝ) → ℝ) (assigned : P.PacketIndex → τ)
    (stop : Fin N → ℕ) (T : τ → SlopeBox) (L A alpha : ℝ) (z : ℝ×ℝ)
    (transition : ℕ → ℤ → ℂ) (lower upper : ℕ) (cell : ℤ) :
    grid.packetResidual ((Finset.univ : Finset (Q).PacketIndex).filter
      (fun u => (⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ : P.PacketIndex) ∈ S))
      (fun u => slope (assigned ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight
        (fun u => assigned ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) (fun u => stop u.1)
        ((Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
          newSlope (fun j l => b j (orig j l)) v f
          (fun j l u => T (assigned ⟨j,⟨orig j l,u⟩⟩)) L A z) alpha z)
      transition lower upper cell =
    grid.packetResidual S (fun u => slope (assigned u)) (fun u => stop u.1)
      (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
        (P.physicalMaskedValue alt hAlt oldSlope b v f
          (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z) alpha z)
      transition lower upper cell := by
  let value := P.physicalMaskedValue alt hAlt oldSlope b v f
    (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z
  have hvalue (u : (Q).PacketIndex) :
      (Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
        newSlope (fun j l => b j (orig j l)) v f
        (fun j l u => T (assigned ⟨j,⟨orig j l,u⟩⟩)) L A z u =
      value ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ :=
    P.referenceFamily_physicalMaskedValue oldSlope newSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A z u
  have hbase :
      grid.sourcePacketBase tops slope precision cutoff weight
        (fun u : (Q).PacketIndex => assigned ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩) (fun u => stop u.1)
        ((Q).physicalMaskedValue (fun j l => alt j (orig j l)) (fun j l => hAlt j (orig j l))
          newSlope (fun j l => b j (orig j l)) v f
          (fun j l u => T (assigned ⟨j,⟨orig j l,u⟩⟩)) L A z) alpha z =
      fun u => grid.sourcePacketBase tops slope precision cutoff weight assigned
        (fun u => stop u.1) value alpha z ⟨u.1,⟨orig u.1 u.2.1,u.2.2⟩⟩ := by
    funext u
    dsimp only [AngularGrid.sourcePacketBase]
    rw [hvalue]
  rw [hbase]
  exact P.referenceFamily_packetResidual_selected (E := EuclideanSpace ℂ κ) oldSlope newSlope R cone w F
    hw hcone hF hwide hfrequency S hS grid (fun u => slope (assigned u)) (fun u => stop u.1)
    (grid.sourcePacketBase tops slope precision cutoff weight assigned (fun u => stop u.1)
      value alpha z) transition lower upper cell

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

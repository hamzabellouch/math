import OAI.Analysis.LipschitzHilbert.Packets.SourceSupportedLinearEnvelope
import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedVertexPath

namespace OAI

/-! The arbitrary-phase linear envelope for the original assigned
packet amplitudes. Recentring, masks and original analyzing coefficients
are retained exactly. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable

theorem assigned_original_linear_envelope (C L : ℝ) (hC : 1 ≤ C) :
    ∀ (τ : Type) (tops : Finset τ) (T : τ → SlopeBox)
      (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
      (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
      (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F) (hwide : cone*w ≤ P.width)
      (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
      (f : ℝ×ℝ → EuclideanSpace ℂ κ)
      (grid : AngularGrid) (cut Kw D : ℝ), 0 < Kw →
      (∀ u ∈ packets, assigned u ∈ tops) →
      (∀ u ∈ packets, P.length u.1 ≤ (T (assigned u)).length) →
      (∀ u ∈ packets, P.referenceCondition oldSlope (T (assigned u)).slope
        (R (assigned u)) cone w u.1 u.2.1) →
      (∀ j, grid.eligible cut (w/P.length j) 0) →
    ∀ (Kb : ℕ), 0 < Kb →
    ∀ (gap : ℕ → ℝ) (phase : ℕ → ℂ) (M : τ → ℕ),
      (∀ t ∈ tops, grid.eligible cut (w/(T t).length) (M t)) →
      (∀ t ∈ tops, ∀ j, grid.eligible cut (w/(T t).length) j → j ≤ M t) →
    ∀ (a Z A maskExponent : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → 0 ≤ A →
      (∀ t ∈ tops, ∀ j < M t, 0 ≤ (phase j).re) →
      (∀ t ∈ tops, ∀ j < M t, ‖phase j‖ ≤ Z) →
    ∀ (z : ℝ×ℝ),
      (∀ t ∈ tops, (T t).weight Kw D z ≤ C) →
      let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency
      let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency
      let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt
      let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
        hw hcone hF hwide hfrequency alt hAlt
      (∀ t ∈ tops, ∀ lower upper, lower ≤ upper → upper ≤ N →
        ‖((Q t).withProfile (alts t) (halt t)).rawInterval
          (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f
            j (orig t j l) u.val) 0 lower upper z.1 (z.2-(T t).slope*z.1)‖ ≤
            A*((T t).weight Kw D z)^8) →
      ∀ level cell,
        ‖grid.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
          cut (fun t zz => (T t).weight Kw D zz) Kb gap packets assigned
          (fun u => grid.lastEligible cut (w/P.length u.1) (div_pos hw (P.length_pos u.1)))
          (P.physicalMaskedValue alt hAlt oldSlope b v f
            (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L maskExponent z)
          phase a z level cell‖ ≤
            (C^8*A*(1+(a+Z*Kb)*
              (Real.log (max 1 (∑ t ∈ tops, (T t).weight Kw D z))+1))*C^3)*grid.mass tops (fun t => (T t).slope) (fun t => w/(T t).length)
              cut (fun t zz => (T t).weight Kw D zz) level cell z := by
  have hbound := AngularGrid.source_supported_selector_linear_envelope C L hC
  intro τ tops T N κ Label Item _ _ P packets assigned oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f grid cut Kw D hKw
    hassigned hshort hcondition hzero Kb hKb gap phase M hM hMmax
    a Z A maskExponent ha0 ha1 hZ hA hz0 hz z hweight
  dsimp only
  intro hinterval level cell
  let Q := P.assignedReferenceFamily packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency
  let orig := P.assignedReferenceOriginalLabel packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency
  let alts := P.assignedReferenceAlternate packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt
  let halt := P.assignedReferenceAlternate_bound packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt
  let selector := P.assignedReferenceSelector packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency b
  have hcoeff t : (Q t).physicalMultiplierCoefficient (T t).slope (selector t) v f =
      (fun j l u => P.physicalMultiplierCoefficient oldSlope b v f j (orig t j l) u.val) := by
    funext j l u
    exact P.assignedTopReference_physicalMultiplierCoefficient packets assigned t
      oldSlope (T t).slope (R t) cone w F hw hcone hF hwide hfrequency b v f j l u
  have hi t (ht : t ∈ tops) (lower upper : ℕ) (hlu : lower ≤ upper) (hu : upper ≤ N) :
      ‖((Q t).withProfile (alts t) (halt t)).rawInterval
        ((Q t).physicalMultiplierCoefficient (T t).slope (selector t) v f)
        0 lower upper z.1 (z.2-(T t).slope*z.1)‖ ≤ A*((T t).weight Kw D z)^8 := by
    rw [hcoeff t]
    exact hinterval t ht lower upper hlu hu
  have hb := hbound τ tops T N κ (fun j => τ×P.labels j)
    (P.AssignedTopItem packets assigned) Q alts halt selector v f grid w cut Kw D hw hKw
    (fun t _ j l u => P.assignedTopReference_supported_length packets assigned t
      oldSlope (R t) cone w F hw hcone hF hwide hfrequency T hshort j l u)
    (fun _ _ => hzero) Kb hKb gap phase M hM hMmax
    a Z A maskExponent ha0 ha1 hZ hA hz0 hz z hweight hi level cell
  have heq := P.assignedReference_packetAmplitude_original packets assigned T oldSlope R cone w F
    hw hcone hF hwide hfrequency alt hAlt b v f grid tops (fun t => w/(T t).length)
    cut (fun t zz => (T t).weight Kw D zz) Kb gap hassigned hcondition
    (fun _ j => grid.lastEligible cut (w/P.length j) (div_pos hw (P.length_pos j)))
    phase a L maskExponent z level cell
  exact (congrArg norm heq).le.trans hb


end LipschitzHilbert.SourceLabeledLattice

end

end OAI

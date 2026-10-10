import OAI.Analysis.LipschitzHilbert.Trees.SourceAssignedPathIntegral

namespace OAI

/-! The marked product is invariant under the exact regrouping of the
original selected packets into inhabited assigned-top reference bands. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N Kb : ℕ} {κ τ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem assignedInhabitedMarkedProduct_original
    (P : SourceLabeledLattice N κ Label Item)
    (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (T : τ → SlopeBox) (oldSlope : ℝ) (R : τ → ℝ) (cone w F : ℝ)
    (hw : 0 < w) (hcone : 0 ≤ cone) (hF : 0 ≤ F)
    (hwide : cone*w ≤ P.width) (hfrequency : ∀ k, |P.frequency k| ≤ F/w)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (b : ∀ j, P.labels j → κ → ℝ → ℂ) (v : ℝ×ℝ → ℝ)
    (f : ℝ×ℝ → EuclideanSpace ℂ κ) (L A : ℝ)
    (grid : AngularGrid) (tops : Finset τ) (precision : τ → ℝ) (cut : ℝ)
    (weight : τ → (ℝ×ℝ) → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (hassigned : ∀ q ∈ packets, assigned q ∈ tops)
    (hcondition : ∀ q ∈ packets,
      P.referenceCondition oldSlope (T (assigned q)).slope (R (assigned q)) cone w q.1 q.2.1)
    (stop : τ → Fin N → ℕ) (phase : ℕ → ℂ) (a p μ : ℝ)
    (shift : Fin Kb) (top : τ) (count : ℕ)
    (line : FiniteLineGrid) (level : ℕ → ℕ) (marked : ℕ → ℕ → Prop) (y x : ℝ) :
    let original := P.physicalMaskedValue alt hAlt oldSlope b v f
      (fun j l u => T (assigned ⟨j,⟨l,u⟩⟩)) L A
    let bands := P.assignedInhabitedBand packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f L A
    (∏ j ∈ Finset.range count, reverseMarkedValue line level count marked
      (fun j xx => grid.sourceShiftedPathPrediction tops (fun t => (T t).slope) precision cut weight
        K gap packets assigned (fun q => stop (assigned q) q.1) original
        phase a p μ shift top (xx,y+(T top).slope*xx) j) j x) =
    (∏ j ∈ Finset.range count, reverseMarkedValue line level count marked
      (fun j xx => grid.sourceShiftedPathPrediction tops (fun t => (T t).slope) precision cut weight
        K gap (tops ×ˢ (Finset.univ : Finset (Fin N))) Prod.fst (fun q => stop q.1 q.2) bands
        phase a p μ shift top (xx,y+(T top).slope*xx) j) j x) := by
  dsimp only
  apply Finset.prod_congr rfl
  intro j _
  unfold reverseMarkedValue FiniteLineGrid.markedValue
  split_ifs
  · exact P.assignedInhabitedPrediction_original packets assigned T oldSlope R cone w F
      hw hcone hF hwide hfrequency alt hAlt b v f L A grid tops precision cut weight K gap
      hassigned hcondition stop phase a p μ shift top j (x,y+(T top).slope*x)
  · rfl

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

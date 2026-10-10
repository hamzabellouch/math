import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedCoefficient
import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketContinuity

namespace OAI

/-! Actual labeled cross-profile top sums in physical slope coordinates.
Their continuity needs no spectral or coefficient-size hypothesis. -/

noncomputable section
open MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem rawInterval_continuous (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (i : Fin 3) (lower upper : ℕ) :
    Continuous (fun z : ℝ × ℝ => P.rawInterval coeff i lower upper z.2 z.1) := by
  unfold rawInterval
  apply planarPacketInterval_continuous
  intro j p k
  rcases p with ⟨l,u⟩
  exact modulatedPlanarJet_continuous (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u) (P.length j) P.width (-P.rowSlope j l) (P.frequency k)
    P.scale (P.length_pos j).ne' i

theorem rawInterval_slope_continuous (P : SourceLabeledLattice N κ Label Item)
    (coeff : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (i : Fin 3) (lower upper : ℕ) (slope : ℝ) :
    Continuous (fun z : ℝ × ℝ => P.rawInterval coeff i lower upper z.1 (z.2 - slope * z.1)) := by
  have hs : Continuous (fun z : ℝ × ℝ => (z.2 - slope * z.1, z.1)) := by fun_prop
  have hc := (P.rawInterval_continuous coeff i lower upper).comp hs
  exact hc

def crossTopSum (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound)
    (T : SlopeBox) (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) (z : ℝ × ℝ) : EuclideanSpace ℂ κ :=
  (P.withProfile alt hAlt).rawInterval (P.physicalCoefficient T.slope cutoff v g)
    0 0 N z.1 (z.2 - T.slope * z.1)

theorem crossTopSum_continuous (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ × ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2 * P.order) ≤ P.profileBound)
    (T : SlopeBox) (cutoff : Fin N → ℝ) (v : ℝ × ℝ → ℝ)
    (g : ℝ × ℝ → EuclideanSpace ℂ κ) :
    Continuous (P.crossTopSum alt hAlt T cutoff v g) := by
  exact (P.withProfile alt hAlt).rawInterval_slope_continuous
    (P.physicalCoefficient T.slope cutoff v g) 0 0 N T.slope

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

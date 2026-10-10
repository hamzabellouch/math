import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledStoppingVariation
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathIntegrand

namespace OAI

/-! The original selected coefficients are fixed integrals. Spatial
regularity of the masked packets therefore requires no regularity of
the selecting direction field beyond that used to define them. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

theorem physicalMaskedValue_continuous (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ) (q : P.PacketIndex) :
    Continuous (fun z => P.physicalMaskedValue alt hAlt t b v f T L A z q) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    ((T q.1 q.2.1 q.2.2).mask_continuous L A))).mul
    ((P.withProfile alt hAlt).physicalPacket t q.1 q.2.1 q.2.2 k).continuous

theorem physicalMaskedPath_measurable {τ : Type*} {Kb : ℕ}
    (P : SourceLabeledLattice N κ Label Item)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (Tpacket : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A : ℝ)
    (g : AngularGrid) (tops : Finset τ) (T : τ → SlopeBox)
    (w cutoff Kw D : ℝ) (hKw : 0 < Kw)
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
    (stop : P.PacketIndex → ℕ) (phase : ℕ → ℂ) (a alpha p M : ℝ)
    (shift : Fin Kb) (top : τ) (count : ℕ) :
    Measurable (g.sourceActivePathValue tops (fun u => (T u).slope) (fun u => w/(T u).length)
      cutoff (fun u z => (T u).weight Kw D z) K gap packets assigned stop
      (P.physicalMaskedValue alt hAlt t b v f Tpacket L A) phase a alpha p M shift top count) := by
  apply g.sourceActivePathValue_measurable
  · intro u
    exact ((T u).continuous_weight hKw D).measurable
  · intro q
    exact (P.physicalMaskedValue_continuous alt hAlt t b v f Tpacket L A q).measurable

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

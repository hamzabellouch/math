import OAI.Analysis.LipschitzHilbert.Packets.PacketDataStoppingPrefix
import OAI.Analysis.LipschitzHilbert.Trees.SourcePropagatedTailBound

namespace OAI

/-! Propagated residuals for the original masked physical packets use
exactly the fixed-subset prefix controlled by the reference event. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert.PacketLatticeData

/-- The path's propagated unary residuals are controlled by the original
physical prefix of its one deterministic residual subset. -/
theorem eventually_selected_physical_propagated_tail_bound
    (Cmass : ℝ) (hCmass : 0 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : PacketLatticeData N κ Label Item)
      (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
      (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
      (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
      (v : ℝ×ℝ → ℝ) (test : ℝ×ℝ → EuclideanSpace ℂ κ)
      (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (A : ℝ)
      (τ : Type*) (grid : AngularGrid) (tops : Finset τ)
      (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → ℝ×ℝ → ℝ),
      (∀ top ∈ tops, 0 ≤ precision top) → (∀ top z, 0 < weight top z) →
    ∀ (K : ℕ), 0 < K → (K:ℝ) ≤ L^2 →
    ∀ (gap : ℕ → ℝ) (packets : Finset P.PacketIndex) (assigned : P.PacketIndex → τ)
      (stop : Fin N → ℕ) (phase : ℕ → ℂ) (a Z Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (z : ℝ×ℝ) (level : ℕ → ℕ), StrictMono level →
    ∀ (count : ℕ) (top : τ), top ∈ tops →
    ∀ (e f H : ℕ), e < f → f ≤ count → level f ≤ H →
      grid.eligible cutoff (precision top) (level f) →
      1 ≤ grid.mass tops slope precision cutoff weight (level f)
        (grid.index (level f) (slope top)) z →
      grid.mass tops slope precision cutoff weight 0 (grid.index 0 (slope top)) z ≤
        L^Cmass*Nmass →
      (∀ k < level f, 0 ≤ (phase k).re) → (∀ k < level f, ‖phase k‖ ≤ Z) →
    let value := P.physicalMaskedValue alt hAlt t b v test T L A z
    let transition := grid.sourceTransition tops slope precision cutoff weight K gap phase z
    let base := grid.sourcePacketBase tops slope precision cutoff weight assigned
      (fun q => stop q.1) value a z
    let Q := grid.fixedPathResidualPackets tops slope precision cutoff packets assigned
      (fun q => stop q.1) level count (slope top)
    ∀ j ∈ Finset.Icc e f,
      ‖∑ k ∈ Finset.Ico j f,
        unaryPropagator (fun k => grid.packetPathProduct transition
          (level k) (level (k+1)) (slope top)) j k •
          grid.packetResidual (grid.sourceContinuingPackets tops slope precision cutoff
            packets assigned (level (k+1)) (slope top))
            (fun q => slope (assigned q)) (fun q => stop q.1) base transition
            (level k) (level (k+1)) (grid.index (level k) (slope top))‖ ≤
        L^6*intervalOscillation
          (P.selectedPhysicalPrefix alt hAlt t b v test T L A Q stop z)
          H (level e) (level f) := by
  filter_upwards [AngularGrid.eventually_source_propagated_tail_bound Cmass hCmass] with L htail
  intro N κ Label Item _ _ P alt hAlt t b v test T A τ grid tops slope precision cutoff weight
    hp hw K hK hKL gap packets assigned stop phase a Z Nmass ha0 ha1 hZ0 hZ hN hlogN
    z level hlevel count top htop e finish H hef hfc hH he hnend hnroot hz0 hz
  dsimp only
  simpa only [selectedPhysicalPrefix] using htail τ P.PacketIndex (ℝ×ℝ) (EuclideanSpace ℂ κ)
    grid tops slope precision cutoff weight hp hw K hK hKL gap packets assigned
    (fun q => stop q.1) (P.physicalMaskedValue alt hAlt t b v test T L A z)
    phase a Z Nmass ha0 ha1 hZ0 hZ hN hlogN z level hlevel count top htop
    e finish H hef hfc hH he hnend hnroot hz0 hz

end LipschitzHilbert.PacketLatticeData

end

end OAI

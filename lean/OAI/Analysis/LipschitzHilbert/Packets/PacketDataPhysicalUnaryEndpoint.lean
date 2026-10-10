import OAI.Analysis.LipschitzHilbert.Packets.PacketDataPhysicalPropagatedTail
import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalUnaryEndpoint

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert
namespace PacketLatticeData

/-- The active-path conditions supply the endpoint eligibility and
positive mass in the actual propagated physical residual estimate. Its
fixed reference subset omits the one terminal block. -/
theorem eventually_selected_active_physical_unary_tail
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
    ∀ (K : ℕ) (_hK : 0 < K), (K:ℝ) ≤ L^2 →
    ∀ (shift : Fin K) (gap : ℕ → ℝ) (packets : Finset P.PacketIndex)
      (assigned : P.PacketIndex → τ) (stop : Fin N → ℕ) (phase : ℕ → ℂ)
      (a Z Nmass : ℝ),
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → 0 < Nmass → Real.log Nmass ≤ 2*L →
    ∀ (z : ℝ×ℝ) (count : ℕ) (top : τ), top ∈ tops →
      (¬grid.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift count)) →
    ∀ (M : ℝ), 4 ≤ M → ∀ (H : ℕ), ShiftedBlocks.endpoint shift count ≤ H →
      grid.mass tops slope precision cutoff weight 0 (grid.index 0 (slope top)) z ≤
        L^Cmass*Nmass →
      (∀ k < ShiftedBlocks.endpoint shift count, 0 ≤ (phase k).re) →
      (∀ k < ShiftedBlocks.endpoint shift count, ‖phase k‖ ≤ Z) →
    let n := grid.shiftedPathMass tops slope precision cutoff weight shift top z
    let level := ShiftedBlocks.endpoint shift
    let value := P.physicalMaskedValue alt hAlt t b v test T L A z
    let transition := grid.sourceTransition tops slope precision cutoff weight K gap phase z
    let base := grid.sourcePacketBase tops slope precision cutoff weight assigned
      (fun q => stop q.1) value a z
    let Q := grid.fixedPathResidualPackets tops slope precision cutoff packets assigned
      (fun q => stop q.1) level (count-1) (slope top)
    ∀ e f, e < f → f ≤ firstMassStop n count M → n e-n f < 2 →
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
  filter_upwards [eventually_selected_physical_propagated_tail_bound Cmass hCmass]
    with L htail
  intro N κ Label Item _ _ P alt hAlt t b v test T A τ grid tops slope precision cutoff weight
    hp hw K hK hKL shift gap packets assigned stop phase a Z Nmass ha ha1 hZ hZL hN hlogN
    z count top htop hterminal M hM H hH hroot hphase hphaseNorm
  dsimp only
  intro e f hef hf hdrop j hj
  have he := grid.source_stopped_unary_endpoint tops slope precision cutoff weight shift top z
    count hterminal M hM hef hf hdrop
  have hfc : f ≤ count := he.1.trans (Nat.sub_le _ _)
  have hlevel := (ShiftedBlocks.endpoint_strictMono hK shift).monotone hfc
  exact htail N κ Label Item P alt hAlt t b v test T A τ grid tops slope precision cutoff weight
    hp hw K hK hKL gap packets assigned stop phase a Z Nmass ha ha1 hZ hZL hN hlogN
    z (ShiftedBlocks.endpoint shift) (ShiftedBlocks.endpoint_strictMono hK shift) (count-1) top htop
    e f H hef he.1 (hlevel.trans hH) he.2.1 he.2.2 hroot
    (fun k hk => hphase k (hk.trans_le hlevel))
    (fun k hk => hphaseNorm k (hk.trans_le hlevel)) j hj

end PacketLatticeData
end LipschitzHilbert

end

end OAI

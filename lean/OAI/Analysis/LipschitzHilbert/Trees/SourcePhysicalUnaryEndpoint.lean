import OAI.Analysis.LipschitzHilbert.Trees.SourcePhysicalPropagatedTail
import OAI.Analysis.LipschitzHilbert.Trees.SourceStoppedRecurrence

namespace OAI

/-! A low-drop unary segment on the active mass path ends strictly
before the terminal block and still has the positive mass required by
the physical propagated-residual estimate. -/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace LipschitzHilbert

theorem firstMassStop_unary_endpoint (n : ℕ → ℝ) (count : ℕ) (M : ℝ)
    (hM : 4 ≤ M) (hlast : n count = 0) {e f : ℕ}
    (hef : e < f) (hf : f ≤ firstMassStop n count M) (hdrop : n e-n f < 2) :
    f < count ∧ 1 ≤ n f := by
  have hlastM : n count ≤ M := by rw [hlast]; linarith
  have hs := firstMassStop_spec n count M hlastM
  have he : e < firstMassStop n count M := hef.trans_le hf
  have hactive := hs.2.2 e he
  have hn : 2 < n f := by linarith
  have hfc : f ≤ count := hf.trans hs.1
  have hne : f ≠ count := by intro h; rw [h,hlast] at hn; linarith
  exact ⟨lt_of_le_of_ne hfc hne,by linarith⟩

namespace AngularGrid

theorem source_stopped_unary_endpoint {τ X : Type*} {Kb : ℕ}
    (grid : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (shift : Fin Kb) (top : τ) (x : X) (count : ℕ)
    (hterminal : ¬grid.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift count))
    (M : ℝ) (hM : 4 ≤ M) {e f : ℕ} (hef : e < f)
    (hf : f ≤ firstMassStop (grid.shiftedPathMass tops slope precision cutoff weight shift top x)
      count M)
    (hdrop : grid.shiftedPathMass tops slope precision cutoff weight shift top x e-
      grid.shiftedPathMass tops slope precision cutoff weight shift top x f < 2) :
    f ≤ count-1 ∧
      grid.eligible cutoff (precision top) (ShiftedBlocks.endpoint shift f) ∧
      1 ≤ grid.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint shift f)
        (grid.index (ShiftedBlocks.endpoint shift f) (slope top)) x := by
  have h := firstMassStop_unary_endpoint
    (grid.shiftedPathMass tops slope precision cutoff weight shift top x) count M hM
    (grid.shiftedPathMass_terminal_zero tops slope precision cutoff weight shift top count hterminal x)
    hef hf hdrop
  have he := grid.shiftedPathMass_ne_zero_eligible tops slope precision cutoff weight shift top x f
    (ne_of_gt (lt_of_lt_of_le zero_lt_one h.2))
  refine ⟨by omega,he,?_⟩
  simpa only [shiftedPathMass,ite_eq_left he] using h.2

end AngularGrid

namespace SourceLabeledLattice

/-- The active-path conditions supply the endpoint eligibility and
positive mass in the actual propagated physical residual estimate. Its
fixed reference subset omits the one terminal block. -/
theorem eventually_selected_active_physical_unary_tail
    (Cmass : ℝ) (hCmass : 0 ≤ Cmass) :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item)
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

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI

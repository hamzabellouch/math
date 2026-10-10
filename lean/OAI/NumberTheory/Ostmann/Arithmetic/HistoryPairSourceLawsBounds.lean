import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsBoundsUpdate
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagMassBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns Filter
open HistorySelectedFlagMassBounds
attribute [local instance] Classical.propDecidable
local instance sourceLawsBoundsInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_integer_law_bounds_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10 : ℝ)*L) →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ m l : ℕ, l ≤ k →
      ∀ (ρ : Type) [Fintype ρ] [DecidableEq ρ] (rootOrigin : ρ → ℕ)
        (p : Pattern (pairedHistoryType (Template.initial m k) l)),
      let origin := pairedInternalOrigin (Template.initial m k) l
      let giants := fun _ : Bool => C.giant
      let roots := fun i : ρ => C.sources (rootOrigin i)
      (∀ i, SupportBounds k L (mixedSupport giants roots C.sources origin p i)
        (mixedMass giants roots C.sources origin p i)) ∧
      (∀ q, SupportBounds k L (commonCandidates C.sources origin)
        (blockNaturalWeight C.sources origin p q)) ∧
      (∀ (η : Type) [Fintype η] [DecidableEq η]
          (e : SourceIndex ρ (Block p) ≃ η) (q : Block p) (i : η),
        SupportBounds k L (mixedSupport giants roots C.sources origin p (e.symm i))
          (dummyMass giants roots C.sources origin p e q i)) := by
  filter_upwards [selected_flag_mass_bounds_eventually d Bs BD Bz hk] with L hL
  intro E C hG hGu hcl hcu hb hd m l hl ρ _ _ rootOrigin p
  dsimp only
  obtain ⟨hs, hg, hp⟩ := hL E C hG hGu hcl hcu hb hd
  obtain ⟨ho, hblock⟩ := hp m l hl
  have hblocks : ∀ q, Bounds k L
      (biasedBlockWeight C.sources (pairedInternalOrigin (Template.initial m k) l) p q) :=
    fun q => hblock p q
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact mixedMass_bounds _ _ _ _ p (fun _ => hg) (fun i => hs (rootOrigin i)) hblocks i
  · intro q
    exact blockNaturalWeight_bounds _ _ p q (hblocks q)
  · intro η _ _ e q i
    exact dummyMass_bounds _ _ _ _ p e q (fun _ => hg) (fun i => hs (rootOrigin i))
      hblocks (ho (blockAnchor p q).val) i

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI

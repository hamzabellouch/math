import OAI.NumberTheory.Ostmann.Arithmetic.HistorySelectedFlagMassBoundsCounts

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySelectedFlagMassBounds
open Construction CanonicalOccurrenceTransport CompensationEqualityPatterns Filter
attribute [local instance] Classical.propDecidable
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

def pairedBlockWeight {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k L E) (m l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial m k) l)) (q : Block p)
    (v : CommonSample C.sources (pairedInternalOrigin (Template.initial m k) l)) : ℝ :=
  CompensationEqualityPatterns.blockWeight p
      (sourceWeight C.sources (pairedInternalOrigin (Template.initial m k) l)) q v *
    (v.val : ℝ)^multiplicity p q / (v.val : ℝ)

theorem selected_flag_mass_bounds_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10 : ℝ)*L) →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      (∀ origin : ℕ, Bounds k L (C.sources origin).law.mass) ∧
      Bounds k L C.giant.law.mass ∧
      ∀ m l : ℕ, l ≤ k →
        (∀ i : Internal (Template.initial m k) l ⊕ Internal (Template.initial m k) l,
          Bounds k L (sourceWeight C.sources (pairedInternalOrigin (Template.initial m k) l) i)) ∧
        ∀ (p : Pattern (pairedHistoryType (Template.initial m k) l)) (q : Block p),
          Bounds k L (pairedBlockWeight C m l p q) := by
  filter_upwards [HistorySelectedSourceAtomBounds.selected_source_atom_bounds_eventually
    d Bs BD Bz hk, eventually_ge_atTop (0 : ℝ)] with L hs hL
  intro E C hG hGu hcl hcu hb hd
  have hc := hs E C hG hGu hcl hcu hb hd
  refine ⟨fun origin => prior_bounds (C.sources origin).law k hL (hc.2.2.1 origin),
    prior_bounds C.giant.law k hL hc.2.2.2.2.2, ?_⟩
  intro m l hl
  refine ⟨fun i => sourceWeight_bounds C.sources _ i k hL (hc.2.2.1 _), ?_⟩
  intro p q
  exact literal_block_bounds C (pairedInternalOrigin (Template.initial m k) l) p q
    hL (paired_internal_card_le m k l hl) (fun i => hc.1 _) (fun i => hc.2.1 _)

end Ostmann.Arithmetic.HistorySelectedFlagMassBounds

end

end OAI

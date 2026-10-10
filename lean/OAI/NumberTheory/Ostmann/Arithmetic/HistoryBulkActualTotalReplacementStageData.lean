import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindexGeometry
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualTotalReplacementBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTermSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualTotalReplacement
open Construction Conclusion Filter HistoryBulkSourceDisintegration
open HistoryBulkFibreGiantApproximation HistoryGiantReferenceMean HistoryRepresentativeSourceSeparation
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k l : ℕ} {E : Finset ℕ}

structure PlainStageData (C : InitialSourceChoice d Bs BD Bz k L E)
    (spectator : PrimeSource) (l : ℕ) : Prop where
  reference : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator
  residues : SpectatorResidueBounds C spectator l
  frequencies : ∀ _ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
    ∀ j ≤ l, ∀ origin, (C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j)
  admissible : ∀ ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
    ∀ r : Frame (l:=l) C (spectatorList spectator ds),
      PairAdmissible r.left r.right (spectatorList spectator ds)

theorem selected_plain_stage_data_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.exp ((1/2000:ℝ)*L) ≤ Real.log (p:ℕ) ∧
        Real.log (p:ℕ) ≤ Real.exp ((1/1000:ℝ)*L)) →
      ∀ l ≤ k, PlainStageData C spectator l :=
  ((HistoryBulkActualPrincipalSourceReindex.selected_square_geometry_eventually d Bs BD Bz hk).and
    (HistoryBulkFixedReferenceTerm.selected_reference_equality_eventually d Bs BD Bz hk)).mono
    (fun _L h E C hG hcl hcu hb hd spectator hspec l hl =>
      let hp := fun ds => h.1 E C hG hcl hcu hb hd spectator hspec ds l hl
      ⟨h.2 E C hG hcl hcu hb hd spectator hspec,
        fun ds => (hp ds).1, fun ds => (hp ds).2.1, fun ds => (hp ds).2.2⟩)

end Ostmann.Arithmetic.HistoryBulkActualTotalReplacement

end

end OAI

import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantApproximationDefs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction Conclusion Filter HistoryBulkFibreGiantApproximation
open HistoryBulkSupportConverse HistoryBulkPrincipalBSquareReference
open HistoryRepresentativeSourceSeparation

theorem selected_square_inputs_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀q:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (q:ℕ) ∧
        Real.log (q:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀(outside : List ℕ),(∀q∈outside,q∈spectator.candidates) →
      ∀l,l≤k →
      (∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) ∧
      (∀r : Frame (l:=l) C outside,PairAdmissible r.left r.right outside) := by
  filter_upwards [selected_source_inputs_eventually d Bs BD Bz hk,
    selected_frame_inputs_eventually d Bs BD Bz hk] with L hsource hframe
  intro E C hG hcl hcu hb hd spectator hspec outside hmem l hl
  have hsf := (hsource E C hG hcl hcu hb hd spectator hspec).2.2
  refine ⟨?_,fun r => (hframe E C hG hcl hcu hb hd spectator hspec outside hmem l hl r).1⟩
  intro q hq j hj
  exact hsf ⟨q,hmem q hq⟩ j (hj.trans hl)

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI

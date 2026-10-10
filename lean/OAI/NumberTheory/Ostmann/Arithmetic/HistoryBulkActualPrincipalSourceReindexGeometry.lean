import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferenceSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex
open Construction Conclusion Filter HistoryBulkFibreGiantApproximation
open HistoryBulkPrincipalBSquareReference HistoryBulkSupportConverse
open HistoryGiantReferenceMean HistoryRepresentativeSourceSeparation

theorem selected_square_geometry_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀spectator : PrimeSource,
      (∀q:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (q:ℕ) ∧
        Real.log (q:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ds : Fin (2*(bulkSize k L/2))→spectator.Sample,∀l≤k,
      (∀q∈spectatorList spectator ds,∀j≤l,frequencyBound Bs BD Bz k L j<q) ∧
      (∀j≤l,∀origin,(C.sources origin).AboveFrequency (frequencyBound Bs BD Bz k L j)) ∧
      (∀r : Frame (l:=l) C (spectatorList spectator ds),
        PairAdmissible r.left r.right (spectatorList spectator ds)) := by
  filter_upwards [selected_source_inputs_eventually d Bs BD Bz hk,
    selected_frame_inputs_eventually d Bs BD Bz hk] with L hsource hframe
  intro E C hG hcl hcu hb hd spectator hspec ds l hl
  obtain ⟨_,hf,hs⟩ := hsource E C hG hcl hcu hb hd spectator hspec
  have hout : ∀q∈spectatorList spectator ds,q∈spectator.candidates := by
    intro q hq
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact (ds j).property
  refine ⟨?_,fun j hj=>hf j (hj.trans hl),?_⟩
  · intro q hq j hj
    exact hs ⟨q,hout q hq⟩ j (hj.trans hl)
  · intro r
    exact (hframe E C hG hcl hcu hb hd spectator hspec
      (spectatorList spectator ds) hout l hl r).1

end Ostmann.Arithmetic.HistoryBulkActualPrincipalSourceReindex

end

end OAI

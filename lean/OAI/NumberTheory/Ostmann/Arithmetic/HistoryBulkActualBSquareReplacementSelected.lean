import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementBoundInterface
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualBSquareReplacementGeometryInterface
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFixedReferenceTermSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns
open HistoryBulkActualRootReferenceFamily HistoryBulkActualPrincipalBlockFamily
open HistoryBulkSourceDisintegration HistoryBulkFibreGiantApproximation
open HistoryBulkPrincipalBSquareReplacement HistoryRepresentativeSourceSeparation
open HistoryBulkActualPrincipalSourceReindexFamily Filter
attribute [local instance] Classical.propDecidable
local instance actualBSquareSelectedInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_frequency_error_eventually (d : Decomposition)
    (Bs BD Bz H : ℝ) {k : ℕ} (hBs : 0≤Bs) (hH : 0≤H) (hk : 2≤k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase →
      C.blockBase+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀q:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (q:ℕ) ∧
        Real.log (q:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∃hactual : HistoryBulkFixedReferenceTerm.SelectedReferenceEquality C spectator,
      ∀(outside : List ℕ)(houtside : ∀q∈outside,∃r:spectator.Sample,(r:ℕ)=q)
        (hout : outside.length=2*(bulkSize k L/2)),
      ∀l (hl : l≤k),
      ∃(hp : ∀q∈outside,q.Prime)
        (hAd : ∀r : Frame (l:=l) C outside,PairAdmissible r.left r.right outside)
        (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      ∀(σ : Equiv.Perm (Fin (2^l) × Fin (2*(bulkSize k L/2))))
        (J : Background C l → Index (Bs:=Bs) (BD:=BD) (Bz:=Bz) (k:=k) (L:=L) (l:=l) →
          SelectedBulkSample C l → ℤ → ℤ → ℂ)
        (α : Type) [Fintype α] (w : α→ℝ) (P Q : α→ℤ)
        (hw : ∀r,0≤w r) (hpos : ∀r,w r≠0 → 0<P r ∧ 0<Q r)
        (hcell : ∀r,w r≠0 → 0<P r ∧ 0<Q r ∧
          |Real.log (P r:ℝ)-(C.giantCenter:ℝ)|≤1 ∧
          |Real.log (Q r:ℝ)-(C.giantCenter:ℝ)|≤1)
        (corrected mixed : Bool), (if corrected then l<k else l≤k) →
      frequencyError C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV
          corrected mixed ≤ Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L:ℝ)) ∧
      frequencyError C outside σ J w P Q hactual hl houtside hw hpos hcell hp hAd hout hV
          corrected mixed ≤ Real.exp (-H*(bulkSize k L:ℝ)) := by
  have hk0 : 0<k := by omega
  filter_upwards [HistoryBulkFixedReferenceTerm.selected_reference_equality_eventually d Bs BD Bz hk0,
    selected_square_inputs_eventually d Bs BD Bz hk0,
    selected_root_density_B_replacement_interface d Bs BD Bz 0 H hBs hH hk]
    with L href hgeometry herror
  intro E C hG hGu hcl hcu hb hd spectator hspec
  let hactual := href E C hG hcl hcu hb hd spectator hspec
  refine ⟨hactual,?_⟩
  intro outside houtside hout l hl
  have hp : ∀q∈outside,q.Prime := by
    intro q hq
    obtain ⟨r,rfl⟩ := houtside q hq
    exact spectator.prime r.val r.property
  have hmem : ∀q∈outside,q∈spectator.candidates := by
    intro q hq
    obtain ⟨r,rfl⟩ := houtside q hq
    exact r.property
  obtain ⟨hV,hAd⟩ := hgeometry E C hG hcl hcu hb hd spectator hspec outside hmem l hl
  refine ⟨hp,hAd,hV,?_⟩
  intro σ J α _ w P Q hw hpos hcell corrected mixed hdepth
  have hsize : outside.length≤bulkSize k L := by rw [hout]; omega
  have hlog : ∀q∈outside,Real.log (q:ℝ)≤Real.exp ((1/1000:ℝ)*L) := by
    intro q hq
    obtain ⟨r,rfl⟩ := houtside q hq
    exact (hspec r).2
  have hbnd := herror E C hG hGu hcl hcu hb hd spectator hspec l corrected mixed hdepth
    outside (fun q hq => (hp q hq).pos) hsize hlog
    (Background C l × SelectedBulkSample C l)
    (FinitePrior.pair (backgroundPrior C l) (selectedBulkPrior C l))
    (fun v f g a => referenceFamily C outside σ (J a.1) w P Q hactual hl houtside hw hpos hcell
      hp hAd hout hV a.1 a.2 (v,(f,g)))
    (fun v f g a => densitySources C outside σ (J a.1) w P Q hactual hl houtside hw hpos hcell
      hp a.1 a.2 (v,(f,g)))
    (fun v f g a => staticMask C outside σ (J a.1) w P Q hactual hl houtside hw hpos hcell
      hp a.1 a.2 (v,(f,g)))
  simpa only [frequencyError,expression,zero_mul,Real.exp_zero,one_mul] using hbnd

end Ostmann.Arithmetic.HistoryBulkActualBSquareReplacement

end

end OAI

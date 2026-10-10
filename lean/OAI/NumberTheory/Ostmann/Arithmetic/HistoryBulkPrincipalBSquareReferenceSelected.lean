import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReferencePattern
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSelectedInputs
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeIntegerAdmissible

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference
open Construction CanonicalOccurrenceTransport Conclusion Filter CompensationEqualityPatterns
open HistoryPairRepresentatives HistoryPairRows HistoryBulkFibreGiantApproximation
open HistoryRepresentativeSourceSeparation HistoryRepresentativeIntegerAdmissible
open HistoryBulkSupportConverse HistoryBulkPrincipalBSquareReplacement HistoryPairSourceLaws
open HistoryCompensationRepresentativePatterns HistorySymbolicEncoding
local instance squareReferenceSelectedInternalDecidable (seed : List SourceSlot) (l : ℕ) :
    DecidableEq (Internal seed l) := Classical.decEq _

theorem selected_frame_inputs_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {depth : ℕ} (hdepth : 0<depth) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀ spectator : PrimeSource,
      (∀q:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (q:ℕ) ∧
        Real.log (q:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ outside : List ℕ, (∀q∈outside,q∈spectator.candidates) →
    ∀l,l≤depth → ∀r : Frame (l:=l) C outside,
      PairAdmissible r.left r.right outside ∧
      (∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q) := by
  filter_upwards [selected_source_inputs_eventually d Bs BD Bz hdepth] with L hL
  intro E C hG hcl hcu hb hd spectator hspec outside hout l hl r
  obtain ⟨hsep,hfreq,houtfreq⟩ := hL E C hG hcl hcu hb hd spectator hspec
  have hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q := by
    intro q hq j hj
    exact houtfreq ⟨q,hout q hq⟩ j (hj.trans hl)
  refine ⟨?_,hV⟩
  exact decoded_integer_pair_admissible C hsep (frequencyBound Bs BD Bz depth L)
    outside l r.leftSource r.rightSource r.s r.t r.P r.Q r.leftChoices r.rightChoices
    r.left_mass r.right_mass r.left_choices_mass r.right_choices_mass
    (fun j hj=>hfreq j (hj.trans hl))
    (fun q hq=>⟨r.outside_primes q hq,hV q hq⟩) r.left_supported r.right_supported

theorem selected_principalSquareReference_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {depth : ℕ} (hdepth : 0<depth) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz depth L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
    ∀ spectator : PrimeSource,
      (∀q:spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (q:ℕ) ∧
        Real.log (q:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
    ∀ outside : List ℕ, (∀q∈outside,q∈spectator.candidates) →
    ∀l,l≤depth → ∀r : Frame (l:=l) C outside,
    ∀(x : Frame.Source (C:=C) (l:=l)) (hx : (assignmentPrior C.sources _).mass x≠0),
    ∀(p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize depth L/2)) depth) l))
      (b : BlockDraw p (CommonSample C.sources
        (pairedInternalOrigin (Template.initial (2*(bulkSize depth L/2)) depth) l)))
      (hslots : ∀i,(slot r.left r.right (pairedInternalEquiv
        (Template.initial (2*(bulkSize depth L/2)) depth) r.left r.right
        (leftDraw r).labels (rightDraw r).labels i)).value=(expand p b i).val)
      (sw : ℕ) (houtlen : outside.length=2*sw)
      (σ : Equiv.Perm (Frame.Slots (depth:=depth) (L:=L) (l:=l))) (K : ℕ),
      ∃ (had : PairAdmissible r.left r.right outside)
        (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz depth L j<q)
        (R : PrincipalSquareReference C outside l p b.val),
        R=principalSquareReference r x hx p b hslots had sw houtlen hV σ K := by
  filter_upwards [selected_frame_inputs_eventually d Bs BD Bz hdepth] with L hL
  intro E C hG hcl hcu hb hd spectator hspec outside hout l hl r x hx p b hslots sw houtlen σ K
  obtain ⟨had,hV⟩ := hL E C hG hcl hcu hb hd spectator hspec outside hout l hl r
  exact ⟨had,hV,principalSquareReference r x hx p b hslots had sw houtlen hV σ K,rfl⟩

end Ostmann.Arithmetic.HistoryBulkPrincipalBSquareReference

end

end OAI

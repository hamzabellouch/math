import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalSymbolicFamily
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregationSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation
open Construction Conclusion CanonicalOccurrenceTransport CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryPairRepresentatives HistoryBulkReferenceFrequencyFamily HistorySelectedJointIntegralBounds
open HistoryBulkSelectedUniversalOperator HistoryBulkSelectedUniversalSymbolicFamily
open HistoryRepresentativeSourceSeparation Filter
open scoped BigOperators
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

structure SymbolicPatternFamily {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ}
    {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k L E)
    (outside : List ℕ) (l : ℕ)
    (p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)) where
  permutation : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2)))
  left : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l
  right : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l
  refs : RootReferenceFamily C.sources (Template.initial (2*(bulkSize k L/2)) k)
    (frequencyBound Bs BD Bz k L) outside l left right
  data : ∀i : RootPresent refs,ActualReferenceData C permutation i.val (rootSelected refs i)
  representative : ∀i : RootPresent refs,
    Block p ≃ Representative (rootLeftHistory refs i) (rootRightHistory refs i)
  mask : RootPresent refs → ℝ
  mask_mem : ∀i,0 ≤ mask i ∧ mask i ≤ 1

variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
  {C : InitialSourceChoice d Bs BD Bz k L E} {outside : List ℕ} {l : ℕ}

def SymbolicPatternFamily.value {p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)}
    (family : SymbolicPatternFamily C outside l p)
    (b : Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l))
    (mixed : Bool) (s : ℕ) (hp : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q) : ℂ :=
  ∑j,presentComplexValue family.refs (fun i=>
    symbolicFamilyWeight family.refs b family.representative mixed family.mask i *
      actualNestedIntegral C mixed s (family.data i) *
      referenceRootAverage mixed d k (2*(bulkSize k L/2)) family.permutation hp hV
        (rootSelected family.refs i)) j

theorem selected_symbolic_pattern_sum_eventually
    (d : Decomposition) (Bs BD Bz : ℝ) (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz)
    {k : ℕ} (hk : 2 ≤ k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase+favorableBlockWidth L ≤ Real.exp ((9/10:ℝ)*L) →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀(s : ℕ)(outside : List ℕ)(hout : ∀p∈outside,p∈spectator.candidates),
      outside.length=2*s → ∀l : ℕ,l≤k →
      ∃hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q,
      ∀(families : ∀p : Pattern (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l),
        (Block p → CommonSample C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)) →
        SymbolicPatternFamily C outside l p) (mixed : Bool),
      ‖patternComplexSum C.sources (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l)
        (fun p b=>(families p b).value b mixed s (fun q hq=>spectator.prime q (hout q hq)) hV)‖ ≤
        ((64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l)*
          (((3:ℝ)^(2^l))^outside.length)*
          Real.exp (2*(2:ℝ)^l*initialGap Bs k L+(bulkSize k L:ℝ))) *
          Real.exp (2*(2:ℝ)^l*(bulkSize k L:ℝ)) := by
  have hk' : 0 < k := by omega
  filter_upwards [selected_patternComplexSum_eventually d Bs BD Bz hk,
    selected_symbolic_family_eventually d Bs BD Bz hBs hBD hBz hk' (by norm_num : (0:ℝ)<1),
    SourceFrequencyBounds.frequency_lt_of_log_lower_eventually Bs BD Bz hk'
      (by norm_num : (0:ℝ)<1/2000)] with L hPattern hFamily hFreq
  intro E C hG hGu hc hcu hb hd spectator hspec s outside hout hlen l hl
  have hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q := by
    intro q hq j hj
    exact hFreq j (hj.trans hl) q (spectator.prime q (hout q hq)).pos
      (hspec ⟨q,hout q hq⟩).1
  refine ⟨hV,?_⟩
  intro families mixed
  apply hPattern E C hG hGu hc hcu hb hd l hl
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (mainAmplitude_pos Bs k L l).le) (by positivity)) (Real.exp_pos _).le
  · intro p b _ _
    obtain ⟨hv,hf⟩ := hFamily E C hG hc hcu hb hd spectator hspec s outside hout hlen l hl
      (families p b).permutation (families p b).left (families p b).right
      (families p b).refs (families p b).data
    simpa only [SymbolicPatternFamily.value,one_mul,mul_comm] using
      hf (pairedInternalOrigin (Template.initial (2*(bulkSize k L/2)) k) l)
        (pairedHistoryType (Template.initial (2*(bulkSize k L/2)) k) l) p b
        (families p b).representative mixed (families p b).mask (families p b).mask_mem

end Ostmann.Arithmetic.HistoryBulkUniversalPatternAggregation

end

end OAI

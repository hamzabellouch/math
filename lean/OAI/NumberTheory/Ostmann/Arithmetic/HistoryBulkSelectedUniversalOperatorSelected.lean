import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorAdmissible

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator
open Construction Conclusion HistoryBulkReferenceFrequencyFamily HistorySelectedJointIntegralBounds
open HistoryRepresentativeSourceSeparation Filter
open scoped BigOperators

theorem selected_universal_operator_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) {k : ℕ} (hk : 0 < k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ L : ℝ in atTop, ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀spectator : PrimeSource,
      (∀p : spectator.Sample,Real.exp ((1/2000:ℝ)*L)≤Real.log (p:ℕ) ∧
        Real.log (p:ℕ)≤Real.exp ((1/1000:ℝ)*L)) →
      ∀(s : ℕ)(outside : List ℕ)(hout : ∀p∈outside,p∈spectator.candidates),
      outside.length=2*s → ∀l,l≤k →
      ∀(σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
      (x y : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l)
      (refs : RootReferenceFamily C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) outside l x y)
      (data : ∀i : RootPresent refs,ActualReferenceData C σ i.val (rootSelected refs i)),
      ∃hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q,
      ∀mixed : Bool,
      ‖∑j,presentComplexValue refs (fun i=>actualNestedIntegral C mixed s (data i)*
        referenceRootAverage mixed d k (2*(bulkSize k L/2)) σ
          (fun p hp=>spectator.prime p (hout p hp)) hV (rootSelected refs i)) j‖ ≤
        (64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l)*
          (((3:ℝ)^(2^l))^outside.length)*
          Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) := by
  filter_upwards [actual_universal_operator_eventually d Bs BD Bz hBs hBD hBz hk hρ,
    actualReference_pair_admissible_eventually d Bs BD Bz hk,
    SourceFrequencyBounds.frequency_lt_of_log_lower_eventually Bs BD Bz hk
      (by norm_num : (0:ℝ)<1/2000),eventually_ge_atTop (2000:ℝ)] with L hMain hAd hFreq hL
  intro E C hG hc hcu hb hd spectator hspec s outside hout hlen l hl σ x y refs data
  have hp : ∀q∈outside,q.Prime := fun q hq=>spectator.prime q (hout q hq)
  have hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q := by
    intro q hq j hj
    exact hFreq j (hj.trans hl) q (hp q hq).pos (hspec ⟨q,hout q hq⟩).1
  have hthree : ∀q∈outside,3 ≤ q := by
    intro q hq
    by_contra hn
    have heq : q=2 := by have := (hp q hq).two_le; omega
    have he : Real.exp ((1/2000:ℝ)*L) ≤ Real.log (q:ℝ) :=
      (hspec ⟨q,hout q hq⟩).1
    rw [heq] at he
    have hexp := Real.add_one_le_exp ((1/2000:ℝ)*L)
    have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at he hlog
    linarith
  refine ⟨hV,?_⟩
  intro mixed
  apply hMain E C hG hc s outside hp hlen hthree l hl σ x y refs data hV
  intro i
  exact hAd E C hG hc hcu hb hd spectator hspec outside hout l hl σ x y
    i.val (rootSelected refs i) (data i)

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

end

end OAI

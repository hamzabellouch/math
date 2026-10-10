import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalSymbolicFamilyBasic

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalSymbolicFamily
open Construction Conclusion HistoryBulkReferenceFrequencyFamily HistorySelectedJointIntegralBounds
open HistoryBulkSelectedUniversalOperator CompensationEqualityPatterns HistoryPairSourceLaws
open HistoryPairRepresentatives
open HistoryRepresentativeSourceSeparation Filter
open scoped BigOperators

theorem selected_symbolic_family_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (origin τ : ι → ℕ)
        (p : Pattern τ) (b : Block p → CommonSample C.sources origin)
        (representative : ∀ i : RootPresent refs,
          Block p ≃ Representative (rootLeftHistory refs i) (rootRightHistory refs i))
        (mixed : Bool) (mask : RootPresent refs → ℝ),
      (∀ i, 0 ≤ mask i ∧ mask i ≤ 1) →
      ‖∑j,presentComplexValue refs (fun i=>symbolicFamilyWeight refs b representative mixed mask i*actualNestedIntegral C mixed s (data i)*
        referenceRootAverage mixed d k (2*(bulkSize k L/2)) σ
          (fun p hp=>spectator.prime p (hout p hp)) hV (rootSelected refs i)) j‖ ≤
        (∏ q : Block p, 2 / ((b q).val : ℝ)) *
          ((64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l)*
            (((3:ℝ)^(2^l))^outside.length)*
            Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ))) := by
  filter_upwards [selected_weighted_universal_operator_eventually d Bs BD Bz hBs hBD hBz hk hρ]
    with L hL
  intro E C hG hc hcu hb hd spectator hspec s outside hout hlen l hl σ x y refs data
  obtain ⟨hV,hMain⟩ := hL E C hG hc hcu hb hd spectator hspec s outside hout hlen l hl σ x y refs data
  refine ⟨hV,?_⟩
  intro ι _ _ origin τ p b representative mixed mask hm
  simpa only [mul_assoc] using
    hMain (symbolicFamilyWeight refs b representative mixed mask)
      (∏ q : Block p, 2 / ((b q).val : ℝ)) (reciprocalBlockProduct_nonneg b)
      (symbolicFamilyWeight_norm_le refs b representative mixed mask hm) mixed

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalSymbolicFamily

end

end OAI

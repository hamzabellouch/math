import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorIntegral

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator
open Construction Conclusion HistoryBulkReferenceFrequencyFamily HistorySelectedJointIntegralBounds
open HistoryRepresentativeSourceSeparation Filter
open scoped BigOperators

theorem actual_universal_operator_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) {k : ℕ} (hk : 0 < k)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ L : ℝ in atTop, ∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase  →  C.blockBase-2<(C.giantCenter:ℝ)  → 
      ∀(s : ℕ)(outside : List ℕ)(hp : ∀q∈outside,q.Prime),outside.length=2*s → 
      (∀q∈outside,3 ≤ q)  →  ∀l≤k,
      ∀(σ : Equiv.Perm (Fin (2^l)×Fin (2*(bulkSize k L/2))))
      (x y : InternalSourceDraws C.sources (Template.initial (2*(bulkSize k L/2)) k) l)
      (refs : RootReferenceFamily C.sources (Template.initial (2*(bulkSize k L/2)) k)
        (frequencyBound Bs BD Bz k L) outside l x y)
      (data : ∀i : RootPresent refs,ActualReferenceData C σ i.val (rootSelected refs i))
      (hV : ∀q∈outside,∀j≤l,frequencyBound Bs BD Bz k L j<q),
      (∀i : RootPresent refs,PairAdmissible (rootLeftHistory refs i) (rootRightHistory refs i) outside)  → 
      ∀mixed : Bool,
      ‖∑j,presentComplexValue refs (fun i=>actualNestedIntegral C mixed s (data i)*
        referenceRootAverage mixed d k (2*(bulkSize k L/2)) σ hp hV (rootSelected refs i)) j‖ ≤
        (64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l)*
          (((3:ℝ)^(2^l))^outside.length)*
          Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) := by
  filter_upwards [weighted_present_family_eventually hBs hBD hBz hk hρ,
    actualNestedIntegral_norm_eventually d Bs BD Bz k,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 2] with L hSum hIntegral hm
  have hm' : 2 ≤ bulkSize k L := by exact_mod_cast hm
  have hblocksize : 0 < 2*(bulkSize k L/2) := by omega
  intro E C hblock hcenter s outside hp hout hthree l hl σ x y refs data hV had mixed
  apply hSum l hl k _ hblocksize C.sources _ outside x y refs mixed d σ hp hV had hthree
    (fun i=>actualNestedIntegral C mixed s (data i))
    (64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l)
  · exact mul_nonneg (by positivity) (mainAmplitude_pos Bs k L l).le
  · intro i
    exact hIntegral E C hblock hcenter s outside (fun q hq=>(hp q hq).pos) hout
      l σ x y i.val (rootSelected refs i) (data i) mixed

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

end

end OAI

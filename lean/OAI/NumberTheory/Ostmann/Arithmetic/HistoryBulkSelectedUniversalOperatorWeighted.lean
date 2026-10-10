import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperatorSelected

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator
open Construction Conclusion HistoryBulkReferenceFrequencyFamily HistorySelectedJointIntegralBounds
open HistoryRepresentativeSourceSeparation Filter
open scoped BigOperators

theorem selected_weighted_universal_operator_eventually (d : Decomposition) (Bs BD Bz : ℝ)
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
      ∀(W : RootPresent refs→ℂ)(B : ℝ),0 ≤ B → (∀i,‖W i‖ ≤ B) →
      ∀mixed : Bool,
      ‖∑j,presentComplexValue refs (fun i=>W i*actualNestedIntegral C mixed s (data i)*
        referenceRootAverage mixed d k (2*(bulkSize k L/2)) σ
          (fun p hp=>spectator.prime p (hout p hp)) hV (rootSelected refs i)) j‖ ≤
        (B*(64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l))*
          (((3:ℝ)^(2^l))^outside.length)*
          Real.exp (2*(2:ℝ)^l*initialGap Bs k L+ρ*(bulkSize k L:ℝ)) := by
  filter_upwards [weighted_present_family_eventually hBs hBD hBz hk hρ,
    actualNestedIntegral_norm_eventually d Bs BD Bz k,
    actualReference_pair_admissible_eventually d Bs BD Bz hk,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 2,
    SourceFrequencyBounds.frequency_lt_of_log_lower_eventually Bs BD Bz hk
      (by norm_num : (0:ℝ)<1/2000),eventually_ge_atTop (2000:ℝ)] with L hMain hIntegral hAd hm hFreq hL
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
  intro W B hB hW mixed
  have hblocksize : 0 < 2*(bulkSize k L/2) := by
    have hm' : 2 ≤ bulkSize k L := by exact_mod_cast hm
    omega
  have hA : 0 ≤ 64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l :=
    mul_nonneg (by positivity) (mainAmplitude_pos Bs k L l).le
  apply hMain l hl k _ hblocksize C.sources _ outside x y refs mixed d σ hp hV
    (fun i=>hAd E C hG hc hcu hb hd spectator hspec outside hout l hl σ x y
      i.val (rootSelected refs i) (data i)) hthree
    (fun i=>W i*actualNestedIntegral C mixed s (data i))
    (B*(64*2^(2^l*(2*(bulkSize k L/2)))*mainAmplitude Bs k L l))
    (mul_nonneg hB hA)
  intro i
  rw [norm_mul]
  exact mul_le_mul (hW i)
    (hIntegral E C hG hc s outside (fun q hq=>(hp q hq).pos) hlen
      l σ x y i.val (rootSelected refs i) (data i) mixed)
    (norm_nonneg _) hB

end Ostmann.Arithmetic.HistoryBulkSelectedUniversalOperator

end

end OAI

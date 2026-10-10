import OAI.NumberTheory.Jacobsthal.Estimates.StrongSourceFamilies

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.ReferenceExponentialTail
open FinitePathGeometry PrimeHistories PrimeBinMembership ActualPrimeHigh ReferenceAdmission StrongReferenceTransport StrongSourceFamilies
open LiteralUniformPrimeTail LiteralPrimeOccupation LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail

theorem uniform_reference_exponential_tail (d c eps : ℝ) (hd : 0 < d) (hc : 0 < c) (heps : 0 < eps) :
    ∃ K₀ B₀ w₀ : ℝ,3 ≤ K₀ ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧
      ∀ K B w top : ℝ,K₀ ≤ K → B₀ ≤ B → w₀ ≤ w → w < top → Real.log B ≤ d*Real.log w →
      ∀ z : Node,z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B →
      z.closed=true → w^B=top → ∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps∈F,K < (terminal w z ps).gap) →
      B^2*(∑ ps∈F,prefixWeight ps*Real.exp (-c*(terminal w z ps).gap)) ≤ eps := by
  obtain ⟨M,BT,WT,_hBT,hWT,hTail⟩ := actual_uniform_original_prime_tail d c eps hd hc heps
  refine ⟨3*((M:ℝ)+1),max BT 3,WT,by nlinarith [Nat.cast_nonneg (α:=ℝ) M],le_max_right _ _,hWT,?_⟩
  intro K B w top hK hB hw₀ htop hcomp z hi h199 h23 hz hcut hclosed hpower F hF hGap
  have hB3 : 3 ≤ B := (le_max_right _ _).trans hB
  have hw : 1 < w := hWT.trans_le hw₀
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  have hsub : F ⊆ uncappedPrefixes w 1 z :=
    fun ps hps => (source_reference_transport hw htop z hs hz hg hclosed hcap ps (hF hps)).1
  have hsum : (∑ ps∈F,prefixWeight ps*Real.exp (-c*(terminal w z ps).gap))=
      ∑ ps∈F,prefixWeight ps*tailListReward c (3*((M:ℝ)+1)) w z ps := by
    apply Finset.sum_congr rfl
    intro ps hps
    rw [tailListReward,ite_eq_left (hK.trans_lt (hGap ps hps))]
  rw [hsum]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun ps _ _ => mul_nonneg (prefixWeight_nonneg ps) (tailListReward_nonneg c (3*((M:ℝ)+1)) w z ps))
  exact (mul_le_mul_of_nonneg_left hle (sq_nonneg B)).trans
    (hTail M le_rfl B w ((le_max_left _ _).trans hB) hw₀ 1 (by norm_num) (by linarith)
      hcomp z hi h199 h23 hz hcut)
end NumberTheoryLean.ReferenceExponentialTail


end Erdos970

end OAI

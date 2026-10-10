import OAI.NumberTheory.Jacobsthal.Paths.GeometricWords

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.GeometricIsolatedBin
open PrimeHistories GeometricRegularWords GeometricBoxImages GeometricWordsAudit ActualWordSelection ActualRegularBoxes
open ErdosSubsetWord SafeSubsetBoxGeometry FirstIsolatedPosition IsolatedBinGeometry IsolatedRealPrimeRange
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints LogarithmicBinPartition
open ErdosPrimeInputs.PrimePrefixMass

attribute [local instance] Classical.propDecidable

theorem geometric_box_isolated_singleton {w top xi C B R L alpha beta : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hpower : w^B=top)
    (hsearch : w^((1/4:ℝ)) ≤ alpha*B) (z : Node)
    (m : Fin (binCount w top xi) → ℕ) (hm : m ∈ geometricBoxes hw htop hxi C B R L alpha beta z) :
    ∃ i : Fin (binCount w top xi),m i=1 ∧ isolatedBin w top xi B alpha beta i ∧ top^alpha ≤ lower w top xi i ∧
      upper w top xi i ≤ top^beta ∧ ActualSourceTags.searchBin w (lower w top xi i) := by
  obtain ⟨ps,hps,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨pre,p,tail,he,hisol,_hfirst⟩ := geometric_first_isolated hw htop hxi z ps hps
  have hrange := isolated_real_range hw htop hxi hpower hisol
  have hlo := hrange.1
  have hhi := hrange.2
  have hs := isolated_bin_search hisol hsearch
  let i := label (zero_lt_one.trans hw) htop hxi p
  have hp : p ∈ ps := by rw [he]; simp
  have hreg := (Finset.mem_filter.mp hps).1
  obtain ⟨hd,_hl,_hc,_hg,hsingle⟩ := Finset.mem_filter.mp hreg
  have hn : ps.Nodup := (mem_decreasingPrefixes.mp hd).1.imp (fun h => ne_of_gt h)
  have hcount : 0 < (ps.map (label (zero_lt_one.trans hw) htop hxi)).count i :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have hle := hsingle i hs
  refine ⟨i,?_,hisol,hlo,hhi,hs⟩
  rw [wordMultiplicity_count _ ps hn]
  omega
end NumberTheoryLean.GeometricIsolatedBin



namespace NumberTheoryLean.GeometricBinOrdering
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints PrimeBinRepresentatives
open IsolatedBinGeometry BoundedEdgeBins BoundedEdgePrimeRange


theorem left_exponent_mono {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (i j : Fin (binCount w top xi)) (hij : i ≤ j) :
    leftExponent w (lower w top xi i) ≤ leftExponent w (lower w top xi j) := by
  have hlow := endpoint_mono (zero_lt_one.trans hw) htop hxi (show i.1 ≤ j.1 from hij)
  exact div_le_div_of_nonneg_right (Real.log_le_log (endpoint_pos (zero_lt_one.trans hw) i.1) hlow) (Real.log_pos hw).le

theorem isolated_before_bounded_edge {w top xi B alpha beta M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (m : Fin (binCount w top xi) → ℕ) (i j : Fin (binCount w top xi))
    (hi : isolatedBin w top xi B alpha beta i) (hj : boundedEdgeBin w top xi Y m M X j)
    (hlarge : X < alpha*B) : j < i := by
  by_contra! hle
  have hh := left_exponent_mono hw htop hxi i j hle
  have hb := bounded_edge_lower_exponent hw htop hxi m j hj
  linarith [hi.1]
end NumberTheoryLean.GeometricBinOrdering



namespace NumberTheoryLean.GeometricInverseGeometry
open FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
open ErdosCofactorChoices ErdosSubsetWord GeometricBoxImages GeometricIsolatedBin
open GeometricBinOrdering BoundedEdgeBins BoundedEdgePrimeRange ParentCofactorChoices CofactorAllChoiceBounds
open SafeSubsetBoxGeometry BinCutSelections
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints


theorem geometric_inverse_geometry {w top xi B C K L alpha a M X : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 1 ≤ C) (hlog : 1 ≤ Real.log w)
    (hcomp : Real.log B ≤ 2*Real.log w) (hDelta : 2*C*xi ≤ 1) (hB : 3 ≤ B)
    (hpower : w^B=top) (hsearch : w^((1/4:ℝ)) ≤ alpha*B) (hlarge : X < alpha*B)
    (Y : ℕ) (hY : 0 < Y) (z : Node) (hroot : z.gap=Real.log (Y:ℝ)/Real.log w-a+2)
    (hi : z.side=.even) (h199 : 199/100 ≤ z.ratio) (hz : Consistent z) (hcut : z.cutoff=B) (hclosed : z.closed=true)
    (m : Fin (binCount w top xi) → ℕ) (hm : m ∈ geometricBoxes hw htop hxi C B K L alpha (1/100) z) :
    ∃ i : Fin (binCount w top xi),m i=1 ∧ top^alpha ≤ lower w top xi i ∧ lower w top xi i ≤ top^((1:ℝ)/100) ∧
      ∀ j : Fin (binCount w top xi),boundedEdgeBin w top xi Y m M X j →
      i ≠ j ∧ m j=1 ∧
      parentCofactorMultiplicity m i j i=0 ∧ parentCofactorMultiplicity m i j j=0 ∧
      ((∑ k,parentCofactorMultiplicity m i j k : ℕ):ℝ) ≤ C*Real.log B ∧
      w ≤ lower w top xi j ∧ lower w top xi j ≤ w^X ∧
      (∀ q ∈ cofactorChoices (globalBins w top xi) (parentCofactorMultiplicity m i j),
        ∀ p ∈ globalBins w top xi i,Real.log ((Y:ℝ)/((p:ℝ)*(q:ℝ)))/Real.log w ≤ M+1) ∧
      (∀ q ∈ cofactorChoices (globalBins w top xi) (parentCofactorMultiplicity m i j),
        ∀ p ∈ globalBins w top xi i,∀ u ∈ globalBins w top xi j,
          a ≤ Real.log ((Y:ℝ)/((p:ℝ)*(q:ℝ)*(u:ℝ)))/Real.log w) := by
  obtain ⟨i,hmi,hisol,hilo,hihi,_hsearch⟩ := geometric_box_isolated_singleton hw htop hxi hpower hsearch z m hm
  have hsmall : 2*(xi/Real.log w) ≤ 6*(2*C*xi) := by
    have hh := div_le_self hxi.le hlog
    nlinarith
  have ha := geometric_box_anchor hw htop hxi (by linarith : 0 ≤ C) hcomp hsmall z m hm
  have hlen := anchor_total_length hw htop hxi z m ha
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB z hi h199 hz hcut
  have hcap : w^z.cutoff=top := by rwa [hcut]
  refine ⟨i,hmi,hilo,(bin_source_bounds (zero_lt_one.trans hw) htop hxi i).2.1.le.trans hihi,?_⟩
  intro j hj
  have hji := isolated_before_bounded_edge hw htop hxi m i j hisol hj hlarge
  have hzero := cofactor_slots_zero m i j
  have htotal : ((∑ k,parentCofactorMultiplicity m i j k : ℕ):ℝ) ≤ C*Real.log B :=
    (Nat.cast_le.mpr (cofactor_total_le m i j)).trans hlen
  have hrange := bounded_edge_prime_range hw htop hxi m j hj
  have hall := cofactor_all_choice_lengths hw htop hxi (by linarith : 0 ≤ C) hcomp Y hY z hroot
    hs hz hg hclosed hcap m ha i j hji hmi hj
  refine ⟨ne_of_gt hji,bounded_edge_singleton m j hj,hzero.1,hzero.2,htotal,hrange.1,hrange.2,?_,hall.2⟩
  intro q hq p hp
  exact (hall.1 q hq p hp).trans (by linarith)
end NumberTheoryLean.GeometricInverseGeometry


end Erdos970

end OAI

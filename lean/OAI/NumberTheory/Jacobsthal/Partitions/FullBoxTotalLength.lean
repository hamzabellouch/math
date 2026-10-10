import OAI.NumberTheory.Jacobsthal.Paths.FullBoxPrefixLower
import OAI.NumberTheory.Jacobsthal.Sieve.ErasedCofactorGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceWeighted
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
  StrongSourceFamilies SafeSubsetBoxGeometry ActualReferencePrefixes PrimeProductLogCoordinates
  ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection SingletonBinProduct
  LogarithmicBinScale LogarithmicBinLabels LogarithmicBinPartition LogarithmicBinEndpoints
attribute [local instance] Classical.propDecidable

theorem full_box_total_length_lower {w top xi B C K a : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap = Real.log (Y : ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed = true) (hcap : w^z.cutoff = top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (f : Fin (binCount w top xi) → Finset ℕ) (hf : f ∈ selections (globalBins w top xi) m) :
    a ≤ Real.log ((Y : ℝ)/(selectionProduct f : ℝ))/Real.log w := by
  have hfull := (anchored_choice_geometry hw htop hxi hC hcomp z m ha f hf).1
  have hprefix : descendingWord f ∈ (descendingWord f).inits :=
    (List.mem_inits _ _).mpr ⟨[],by simp⟩
  have hgap := reference_prefix_gap_floor hw htop z hs hz hg hclosed hcap _ _ hfull hprefix
  have hsource := word_source_membership hw htop hxi m f hf
  have hlog := terminal_gap_log_quotient Y hY z hroot (descendingWord f)
    (fun p hp => ((mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hsource p hp)).1.pos)
  have hprod := descendingWord_product (globalBins w top xi)
    (fun j k hjk => bins_pairwise_disjoint (zero_lt_one.trans hw) htop hxi j k hjk)
    f (fun j => ((mem_selections _ m f).mp hf j).1)
  rw [hprod] at hlog
  linarith

theorem erased_cofactor_all_lengths {w top xi B C K a : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap = Real.log (Y : ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed = true) (hcap : w^z.cutoff = top)
    (m : Fin (binCount w top xi) → ℕ) (ha : SafeAnchor hw htop hxi C B K z m)
    (i : Fin (binCount w top xi)) (hi : m i = 1)
    (f : Fin (binCount w top xi) → Finset ℕ)
    (hf : f ∈ selections (globalBins w top xi) (eraseMultiplicity m i)) :
    ∀ p ∈ globalBins w top xi i,a ≤ Real.log ((Y : ℝ)/((p : ℝ)*selectionProduct f))/Real.log w := by
  intro p hp
  have hfill := fill_selection_mem (globalBins w top xi) m i hi f hf p hp
  have hh := full_box_total_length_lower hw htop hxi hC hcomp Y hY z hroot hs hz hg hclosed hcap m ha
    (fillSelection f i p) hfill
  rw [filled_product f i p (erased_coordinate_empty _ m i f hf),Nat.cast_mul] at hh
  exact hh

end ErdosVarianceWeighted

end

end Erdos970

end OAI

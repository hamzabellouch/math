import OAI.NumberTheory.Jacobsthal.Analysis.UncappedCompactMass
import OAI.NumberTheory.Jacobsthal.Partitions.StrongReferenceTransport

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.StrongSourceFamilies
open FinitePathGeometry PrimeHistories PrimeTiltGeometry PrimeBinMembership ActualPrimeHigh StrongReferenceTransport
open ReferenceAdmission LogarithmicBinPartition UncappedCompactMass
open ErdosPrimeInputs.HarmonicPrimeMeasure ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail
attribute [local instance] Classical.propDecidable

theorem source_reference_transport {w top : ℝ} (hw : 1 < w) (htop : w < top) (z : Node)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (ps : List ℕ)
    (hp : ps ∈ referencePrefixes w (sourcePrimeSet w top) z.side z.gap) :
    ps ∈ uncappedPrefixes w 1 z ∧ 2 ≤ (terminal w z ps).gap := by
  obtain ⟨hD,ha⟩ := Finset.mem_filter.mp hp
  have hDM := mem_decreasingPrefixes.mp hD
  have hP : ∀ p ∈ ps,p.Prime ∧ (1:ℝ)<primeExponent w p ∧
      capGuard z.closed z.cutoff (primeExponent w p) := by
    intro p hps
    obtain ⟨hpp,hlo,hhi⟩ := (mem_sourcePrimeSet (zero_lt_one.trans hw) htop p).mp (hDM.2 p hps)
    have hpp0 : (0:ℝ)<p := by exact_mod_cast hpp.pos
    refine ⟨hpp,?_,?_⟩
    · change 1 < Real.log p/Real.log w
      exact (one_lt_div (Real.log_pos hw)).mpr (Real.log_lt_log (zero_lt_one.trans hw) hlo)
    · have hx : primeExponent w p ≤ z.cutoff := (exponent_le_iff hw hpp0).mpr (by rwa [hcap])
      simpa only [capGuard,hclosed,ite_true] using hx
  have h := strong_history_transport hw (by norm_num : (0:ℝ)≤1) z ps hs hz hg hDM.1 hP ha
  exact ⟨(mem_uncappedPrefixes hw z ps).mpr h.1,h.2.1⟩

theorem finite_compact_family_le {w top K : ℝ} (hw : 1 < w) (htop : w < top) (z : Node)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed=true) (hcap : w^z.cutoff=top) (F : Finset (List ℕ))
    (hF : F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap)
    (hK : ∀ ps ∈ F,(terminal w z ps).gap ≤ K) :
    (∑ ps ∈ F,prefixWeight ps) ≤ compactPrefixMass K w 1 z := by
  have hsub : F ⊆ uncappedPrefixes w 1 z := fun ps hp =>
    (source_reference_transport hw htop z hs hz hg hclosed hcap ps (hF hp)).1
  have he : (∑ ps ∈ F,prefixWeight ps)=
      ∑ ps ∈ F,prefixWeight ps*(if 2 ≤ (terminal w z ps).gap ∧ (terminal w z ps).gap ≤ K then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro ps hp
    have hlo := (source_reference_transport hw htop z hs hz hg hclosed hcap ps (hF hp)).2
    rw [ite_eq_left ⟨hlo,hK ps hp⟩,mul_one]
  rw [he]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ps _ _ => by
    split_ifs
    · simpa only [mul_one] using prefixWeight_nonneg ps
    · simp)

theorem uniform_source_family_mass (K d : ℝ) (hK : 3 ≤ K) (hd : 0 < d) :
    ∃ C B₀ w₀ : ℝ,0 < C ∧ 3 ≤ B₀ ∧ 1 < w₀ ∧ ∀ B w top : ℝ,B₀ ≤ B → w₀ ≤ w →
      w < top → Real.log B ≤ d*Real.log w → ∀ z : Node,
      z.side=.even → 199/100 ≤ z.ratio → z.ratio ≤ 23/10 → Consistent z → z.cutoff=B →
      z.closed=true → w^B=top → ∀ F : Finset (List ℕ),
      F ⊆ referencePrefixes w (sourcePrimeSet w top) z.side z.gap →
      (∀ ps ∈ F,(terminal w z ps).gap ≤ K) → B^2*(∑ ps ∈ F,prefixWeight ps) ≤ C := by
  obtain ⟨C,B₀,w₀,hC,_hB₀,hw₀,hbound⟩ := uniform_uncapped_compact_mass K 1 d hK (by norm_num) hd
  refine ⟨C,max 3 B₀,w₀,hC,le_max_left _ _,hw₀,?_⟩
  intro B w top hB hw htop hcomp z hi h199 h23 hz hcut hclosed hcap F hF hFK
  have hB3 : 3 ≤ B := (le_max_left _ _).trans hB
  have hs : Valid z.side z.ratio := by rw [hi]; change 198/100 ≤ z.ratio; linarith
  have hg := source_strong_state hB3 z hi h199 hz hcut
  have hwm : 1 < w := hw₀.trans_le hw
  have hmass := finite_compact_family_le hwm htop z hs hz hg hclosed (by rwa [hcut]) F hF hFK
  exact (mul_le_mul_of_nonneg_left hmass (sq_nonneg B)).trans
    (hbound B w ((le_max_right _ _).trans hB) hw hcomp z hi h199 h23 hz hcut)
end NumberTheoryLean.StrongSourceFamilies

end

end Erdos970

end OAI

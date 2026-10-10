import OAI.NumberTheory.Jacobsthal.Partitions.FullBoxTotalLength

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosVarianceWeighted
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport SafeSubsetBoxGeometry
  ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection LogarithmicBinScale

theorem product_le_Y_of_length (w a : ℝ) (hw : 1 < w) (ha : 0 ≤ a) (Y d : ℕ)
    (hY : 0 < Y) (hd : 0 < d) (hlen : a ≤ Real.log ((Y : ℝ)/(d : ℝ))/Real.log w) : d ≤ Y := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hYR : (0 : ℝ) < Y := by exact_mod_cast hY
  have hh : w^a ≤ (Y : ℝ)/(d : ℝ) := (Real.le_logb_iff_rpow_le hw (div_pos hYR hdR)).mp hlen
  have hratio : 1 ≤ (Y : ℝ)/(d : ℝ) := (Real.one_le_rpow hw.le ha).trans hh
  have hreal := (le_div_iff₀ hdR).mp hratio
  have hdle : (d : ℝ) ≤ Y := by simpa only [one_mul] using hreal
  exact_mod_cast hdle

theorem full_box_variance_fibres {w top xi B C K a : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C) (ha0 : 0 ≤ a)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap = Real.log (Y : ℝ)/Real.log w-a+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed = true) (hcap : w^z.cutoff = top)
    (m : Fin (binCount w top xi) → ℕ) (hanchor : SafeAnchor hw htop hxi C B K z m)
    (i : Fin (binCount w top xi)) (hi : m i = 1) :
    ∀ f ∈ selections (globalBins w top xi) (eraseMultiplicity m i),Squarefree (selectionProduct f) ∧
      (∀ t ∈ (selectionProduct f).primeFactors,w < (t : ℝ)) ∧
      (∀ p ∈ globalBins w top xi i,(selectionProduct f).Coprime p ∧
        3*a/4 ≤ Real.log ((Y : ℝ)/((p : ℝ)*selectionProduct f))/Real.log w) := by
  intro f hf
  have harith := erased_cofactor_arithmetic hw htop hxi m i f hf
  have hlen := erased_cofactor_all_lengths hw htop hxi hC hcomp Y hY z hroot hs hz hg hclosed hcap m hanchor i hi f hf
  refine ⟨harith.1,harith.2.1,?_⟩
  intro p hp
  exact ⟨harith.2.2 p hp,(by linarith : 3*a/4 ≤ a).trans (hlen p hp)⟩

end ErdosVarianceWeighted

end

end Erdos970

end OAI

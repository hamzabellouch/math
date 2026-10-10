import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBoundsBasic
import OAI.NumberTheory.Ostmann.Construction.SelectedCounterpartWindows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds
open Construction Conclusion Characters.RationalHistory HistoryOccurrenceVariables
open HistorySymbolicEncoding HistoryProductWindows HistoryPairSmoothXi HistoryPairPattern
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem root_matches {seed : List SourceSlot} {h : History l}
    (hh : TreeSourceLabels seed h) : Template.Matches (Template.current seed l) h.root.small := by
  cases h with
  | leaf a => exact hh
  | node a p u hp hm left right => exact hh.1

theorem paired_H_window (b s k₀ : ℕ) (X tb td G : ℝ) (center : ℕ → ℝ)
    (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hk : TreeSourceLabels (Template.initial (2*b) k₀) k)
    (x : PairKey h k → ℝ)
    (hx : SourceDomain b k₀ G center k (fun i => x (rightMap h k i)))
    (hne : pairedRealXi b s X tb td G h k hs ks x ≠ 0) :
    |Real.log (((pairedDiagonalHKeys h k (l+1)).map x).prod) -
      (G+(2:ℝ)^l*(2*tb+inheritedCenter b k₀ l center))| ≤ inheritedWidth k₀ l := by
  have hn : actualRealHistoryScalar b s X tb td G outside k ks
      (fun i => x (rightMap h k i)) ≠ 0 := by
    intro hz
    exact hne (by simp only [pairedRealXi,actualRealXi,hz,star_zero,mul_zero])
  simpa only [pairedDiagonalHKeys,List.map_map,Function.comp_def] using
    actual_history_H_window b s k₀ l X tb td G center k ks (root_matches hk) _ hx hn

theorem selected_paired_H_window {d : Decomposition} {Bs BD Bz : ℝ} {k₀ : ℕ}
    {L : ℝ} {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz k₀ L E)
    (s : ℕ) (hl : l < k₀) (X : ℝ) (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (x : PairKey h k → ℝ)
    (hx : SourceDomain (bulkSize k₀ L/2) k₀ C.giantCenter
      (C.cells.center (bulkSize k₀ L/2)) k (fun i => x (rightMap h k i)))
    (hne : pairedRealXi (bulkSize k₀ L/2) s X C.bulkBin C.spectatorBin C.giantCenter h k hs ks x ≠ 0) :
    |Real.log (((pairedDiagonalHKeys h k (l+1)).map x).prod) -
      ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l)| ≤ nominalInheritedWidth k₀ l := by
  apply inherited_window_normalize (bulkSize k₀ L/2) k₀ l _ C.giantCenter C.bulkBin
    (nominalJ Bs BD Bz k₀ L C.blockBase C.giantCenter C.spectatorBin)
    (stepGap BD Bz k₀ L l) (nominalWeight k₀
      (nominalJ Bs BD Bz k₀ L C.blockBase C.giantCenter C.spectatorBin) (stepGap BD Bz k₀ L))
    (C.cells.center (bulkSize k₀ L/2)) _ (C.top_frequency_center_error _)
    (C.type_frequency_center_error _) (nominalWeight_recurrence_scaled hl _ _)
  exact paired_H_window _ s k₀ X C.bulkBin C.spectatorBin C.giantCenter _ h k hs ks hk x hx hne

end Ostmann.Arithmetic.HistoryBulkCorrectedXiBounds

end

end OAI

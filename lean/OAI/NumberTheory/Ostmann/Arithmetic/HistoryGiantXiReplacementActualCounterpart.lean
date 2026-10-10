import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkCorrectedXiBoundsRemoved
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantCounterpartBoundsBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantXiReplacementActual
open Construction Conclusion HistoryOccurrenceVariables HistoryPairPattern
open HistorySymbolicEncoding HistoryPairSmoothXi HistoryActiveCoordinates
open HistoryPairGiantCoordinates HistoryProductWindows HistoryGiantCounterpartBounds
open HistoryBulkCorrectedXiBounds

theorem counterpartBounds_of_reference_Xi
    {d : Decomposition} {Bs BD Bz : ℝ} {k₀ l : ℕ} {L : ℝ} {E : Finset ℕ}
    (C : InitialSourceChoice d Bs BD Bz k₀ L E) (s : ℕ) (X : ℝ)
    {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (hl : l < k₀)
    (hk : TreeSourceLabels (Template.initial (2*(bulkSize k₀ L/2)) k₀) k)
    (hgiants : RootGiantsAgree h k)
    (hx : SourceDomain (bulkSize k₀ L/2) k₀ C.giantCenter
      (C.cells.center (bulkSize k₀ L/2)) k (fun i => pairBackground h k (rightMap h k i)))
    (hne : pairedRealXi (bulkSize k₀ L/2) s X C.bulkBin C.spectatorBin C.giantCenter
      h k hs ks (pairBackground h k) ≠ 0) :
    CounterpartBounds ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k₀ L l)
      (C.compensationLogScale l) (nominalInheritedWidth k₀ l+2) (nominalRemovedWidth k₀ l)
      (pairedDiagonalHKeys h k (l+1)) (pairedDiagonalUKeys h k (l+1))
      (giantCoordinates h k) (pairBackground h k)
      (fun _ => C.giantCenter-1) (fun _ => C.giantCenter+1) := by
  have hw := selected_paired_H_window C s hl X h k hs ks hk (pairBackground h k) hx hne
  have hu := selected_paired_U_window C hl h k hk (pairBackground h k) hx
  have he : (fun i => pairBackground h k (rightMap h k i)) =
      fun i => (integerSample k i:ℝ) := rightMap_cast_comp h k hgiants
  simp only [pairedDiagonalHKeys,pairedDiagonalUKeys,List.map_map,Function.comp_def] at hw hu
  rw [he] at hw hu
  have hg := hx.giant true
  change |Real.log ((fun i => pairBackground h k (rightMap h k i)) (.inl true))-C.giantCenter| ≤ 1 at hg
  rw [he] at hg
  change |Real.log (k.root.giantMinus:ℝ)-C.giantCenter| ≤ 1 at hg
  have hp := History.supported_root_positive ks
  constructor
  · rw [H_endpoint_log_product h k hp]
    have hh := (abs_le.mp hw).1
    have hq := (abs_le.mp hg).2
    linarith
  · rw [U_endpoint_log_product h k hp]
    have hh := (abs_le.mp hu).2
    linarith

end Ostmann.Arithmetic.HistoryGiantXiReplacementActual

end

end OAI

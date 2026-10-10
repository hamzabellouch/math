import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSourceScalar

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource
open Construction Conclusion HistoryPairPattern HistoryPairSmoothXi HistoryBulkReferenceScalarCoordinates
open HistoryPairBulkCoordinates HistoryPairGiantCoordinates HistoryActiveCoordinates
open HistoryBulkGiantCorrectedBounds HistoryBulkIntegralReplacement
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

theorem mixedScalar_eq_jointScalar {d : Decomposition} {Bs BD Bz L : ℝ} {depth : ℕ}
    {E : Finset ℕ} (C : InitialSourceChoice d Bs BD Bz depth L E)
    (sw : ℕ) (h k : History l)
    (hs : h.Supported (frequencyBound Bs BD Bz depth L) outside)
    (ks : k.Supported (frequencyBound Bs BD Bz depth L) outside)
    (hh : Template.Matches (Template.current (Template.initial (2*(bulkSize depth L/2)) depth) l) h.root.small)
    (x : Fin (2^l)×Fin (2*(bulkSize depth L/2))→ℝ) (u : Option Unit→ℝ) :
    mixedScalar (bulkSize depth L/2) sw C.scale C.bulkBin C.spectatorBin C.giantCenter
      (2*(bulkSize depth L/2)) depth h k hs ks hh x u =
    jointScalar C sw h k hs ks (optionEquiv h k)
      (orderedEquiv (2*(bulkSize depth L/2)) depth h k hs hh) u x := by
  unfold mixedScalar
  rw [primeScalar_eq_jointScalar]
  have hu : (fun t : Bool=>if t then u (some ()) else u none) =
      (fun t=>u (optionBoolEquiv.symm t)) := by
    funext t
    cases t <;> rfl
  rw [hu]
  rfl

end Ostmann.Arithmetic.HistoryBulkReferencePeriodicMeanSource

end

end OAI

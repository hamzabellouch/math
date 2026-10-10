import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryDiagonalSmallGiantTransportSourceBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryDiagonalSmallAverage
open Construction DiagonalSmallResidueNorm HistorySignedResidueFactorization HistoryCRTIntegration
open HistoryCRTProjection ResidueHaar

section
variable (d : Decomposition) (sources : SourceFamily) (T U : List SourceSlot)
    (x : SourceAssignment sources T) (u : SourceAssignment sources U)
    {l : ℕ} (h : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside)
    (hslots : h.root.small.Perm
      (assignedSlots sources U u ++ assignedSlots sources T x))
    (hsource : ∀ i : Fin T.length, (sources (T.get i).origin).AboveFrequency (V l))
    (hx : (assignmentPrior sources T).mass x ≠ 0)
    (M : ℕ) (hA : rootModulus h ∣ M)

theorem sourceLiftedRootSmallTest_norm_le_modulus (hM : 0 < M)
    (z : ZMod M × ZMod M) :
    ‖(sourceLiftedRootSmallTest d sources T U x u h hs hslots hsource hx M hA z:ℂ)‖ ≤
      (M:ℝ) := by
  apply (sourceLiftedRootSmallTest_norm_le d sources T U x u h hs hslots hsource hx M hA z).trans
  exact_mod_cast Nat.le_of_dvd hM hA

theorem sourceLiftedRootSmallTest_mixed_average [NeZero M] :
    average (fun z : MixedPair M =>
      (sourceLiftedRootSmallTest d sources T U x u h hs hslots hsource hx M hA
        (z.1,(z.2:ZMod M)):ℂ)) =
      ((∏i : Fin (assignedSlots sources U u).length,
        (((((assignedSlots sources U u).get i).value-1:ℕ):ℝ) /
          ((assignedSlots sources U u).get i).value):ℝ):ℂ) := by
  let := assignedSmallPrimeFacts sources T U x u
  exact liftedRootSmallTest_mixed_average d h (assignedSlots sources U u)
    (assignedSlots sources T x) hslots outside.prod h.root.giantPlus h.root.giantMinus
    h.root.frequency (sourceReferenceSmallUnitData sources T U x u h hs hslots hsource hx) M hA

theorem norm_sourceLiftedRootSmallTest_mixed_average_le_one [NeZero M] :
    ‖average (fun z : MixedPair M =>
      (sourceLiftedRootSmallTest d sources T U x u h hs hslots hsource hx M hA
        (z.1,(z.2:ZMod M)):ℂ))‖ ≤ 1 := by
  let := assignedSmallPrimeFacts sources T U x u
  exact norm_liftedRootSmallTest_mixed_average_le_one d h (assignedSlots sources U u)
    (assignedSlots sources T x) hslots outside.prod h.root.giantPlus h.root.giantMinus
    h.root.frequency (sourceReferenceSmallUnitData sources T U x u h hs hslots hsource hx) M hA

end
end Ostmann.Arithmetic.HistoryDiagonalSmallAverage

end

end OAI

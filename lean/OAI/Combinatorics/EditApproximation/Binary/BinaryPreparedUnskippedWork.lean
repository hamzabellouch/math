import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedUnskipped
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedRepresentativeWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryUnskippedGuardWork
import OAI.Combinatorics.EditApproximation.Geometry.LocalArithmeticBudget

namespace OAI

/-! The complete unskipped-band constructor pays for both actual wide
grids, every prefix predicate, all child envelopes, and the final guards. -/

namespace EditApproximation
namespace BinaryFraction

def preparedUnskippedBitBudget (e b M P v w B : ℕ) : ℕ :=
  2 * wideMaterializationBitBudget M P B +
    representativeCompleteBitBudget M w (4 * B + 20) +
    unskippedGuardBitBudget e b M v w B + 2 * w + 4

theorem representativeCompleteBitBudget_mono_vertices (M v w B : ℕ) (h : v ≤ w) :
    representativeCompleteBitBudget M v B ≤ representativeCompleteBitBudget M w B := by
  unfold representativeCompleteBitBudget representativeTailBitBudget bandFromActionsBitBudget
    wideMinimumBitBudget bandPredicateBitBudget anchorGuardBitBudget bandToleranceBitBudget
    representativeGuardInputBudget naturalDistanceBitBudget
  dsimp only
  gcongr

theorem unskippedGuardBitBudget_mono_vertices (e b M v v' w w' B : ℕ)
    (hv : v ≤ v') (hw : w ≤ w') :
    unskippedGuardBitBudget e b M v w B ≤ unskippedGuardBitBudget e b M v' w' B := by
  unfold unskippedGuardBitBudget roundedBandBitBudget bandEnvelopeBitBudget
  dsimp only
  gcongr

theorem preparedUnskippedBitBudget_mono_vertices (e b M P v v' w w' B : ℕ)
    (hv : v ≤ v') (hw : w ≤ w') :
    preparedUnskippedBitBudget e b M P v w B ≤ preparedUnskippedBitBudget e b M P v' w' B := by
  have hr := representativeCompleteBitBudget_mono_vertices M w w' (4 * B + 20) hw
  have hg := unskippedGuardBitBudget_mono_vertices e b M v v' w w' B hv hw
  unfold preparedUnskippedBitBudget
  omega

theorem preparedUnskippedCandidateWithWork_cost {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (b P e B : ℕ)
    (hbpos : 0 < b) (hPpos : 0 < P) (tau F : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (center : TargetInterval target.length)
    (hnx : Nat.size source.length + 2 ≤ B) (hny : Nat.size target.length + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b + 2 ≤ B) (hP : Nat.size P ≤ B)
    (he : e + 1 ≤ B) (htau : tau.width ≤ B) (hF : F.width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B) :
    let band := preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
      tau (inversePowerTwo e) child
    let wide := wideActionGridWithWork M parent center b P
    (preparedUnskippedCandidateWithWork source target parent b P e hbpos hPpos tau F
      child initial center).2 ≤ preparedUnskippedBitBudget e b M P band.1.length wide.1.length B := by
  dsimp only
  let band := preparedRepresentativeWithWork parent center (parent.hi - parent.lo) b P
    tau (inversePowerTwo e) child
  let wide := wideActionGridWithWork M parent center b P
  have htheta : (inversePowerTwo e).width ≤ B := by
    rw [inversePowerTwo_width]
    exact he
  have hband := preparedRepresentativeWithWork_complete_cost parent center b P B hPpos tau
    (inversePowerTwo e) child (by omega) (by omega) hM (by omega) hP htau htheta hchild
  have hwide := wideActionGridWithWork_complete_cost M parent center b P B hPpos
    (by omega) (by omega) hM (by omega) hP
  change band.2 ≤ wideMaterializationBitBudget M P B +
    representativeCompleteBitBudget M wide.1.length (4 * B + 20) + wide.1.length + 1 at hband
  change wide.2 ≤ wideMaterializationBitBudget M P B at hwide
  change (preparedUnskippedCandidateWithWork source target parent b P e hbpos hPpos tau F
    child initial center).2 ≤ preparedUnskippedBitBudget e b M P band.1.length wide.1.length B
  unfold preparedUnskippedCandidateWithWork
  dsimp only
  by_cases hempty : band.1 = []
  · rw [dite_eq_left hempty]
    change band.2 + 1 ≤ _
    unfold preparedUnskippedBitBudget
    omega
  · rw [dite_eq_right hempty]
    have hguard := unskippedGuardWithWork_cost parent center b e F band.1
      (wide.1.map Vector.get) hempty initial B hF hb hnx hny
      (fun action _ i => hinitial i (action i))
    simp only [List.length_map] at hguard
    split_ifs
    all_goals
      change band.2 + wide.2 +
        (unskippedGuardWithWork parent center b e F band.1 (wide.1.map Vector.get) hempty initial).2 +
          wide.1.length + _ ≤ _
      unfold preparedUnskippedBitBudget
      omega

theorem preparedUnskippedCandidateWithWork_uniform_cost {α : Type*} (source target : List α)
    {M : ℕ} (parent : TargetInterval source.length) (b P e B : ℕ)
    (hbpos : 0 < b) (hPpos : 0 < P) (tau F : BinaryFraction)
    (child initial : Fin M → TargetInterval target.length → BinaryFraction)
    (center : TargetInterval target.length)
    (hnx : Nat.size source.length + 2 ≤ B) (hny : Nat.size target.length + 2 ≤ B)
    (hM : Nat.size M ≤ B) (hb : Nat.size b + 2 ≤ B) (hP : Nat.size P ≤ B)
    (he : e + 1 ≤ B) (htau : tau.width ≤ B) (hF : F.width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B) :
    (preparedUnskippedCandidateWithWork source target parent b P e hbpos hPpos tau F
      child initial center).2 ≤ preparedUnskippedBitBudget e b M P
        ((40 * P + 2) ^ (2 * M)) ((40 * P + 2) ^ (2 * M)) B := by
  apply (preparedUnskippedCandidateWithWork_cost source target parent b P e B hbpos hPpos
    tau F child initial center hnx hny hM hb hP he htau hF hchild hinitial).trans
  apply preparedUnskippedBitBudget_mono_vertices
  · rw [preparedRepresentativeWithWork_value source target parent center b P hPpos]
    exact (representativeBandActions_length_le source target parent center b P tau.value
      (inversePowerTwo e).value (fun i q => (child i q).value)).trans
        (wideActionList_length_le M parent center b P hPpos)
  · have h := congrArg List.length (wideActionGridWithWork_value M parent center b P hPpos)
    simp only [List.length_map] at h
    rw [h]
    exact wideActionList_length_le M parent center b P hPpos

end BinaryFraction
end EditApproximation

end OAI

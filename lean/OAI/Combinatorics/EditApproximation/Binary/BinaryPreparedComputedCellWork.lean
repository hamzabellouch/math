import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedComputedCell
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedCellGroupWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSetupWork

namespace OAI

/-! The cell cost includes materializing the exact dyadic scale array;
the finite draw counts are then those of the original cell sampler. -/

namespace EditApproximation
namespace BinaryFraction

theorem preparedComputedCellGroupWithWork_cost {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F e Q eM eb eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hbdef : b = 2 ^ eb) (hFdef : F = 2 ^ eF) (hPpos : 0 < P)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ)
    (hB : 6 ≤ B) (hnx : Nat.size source.length + 2 ≤ B)
    (hny : Nat.size target.length + 2 ≤ B) (hM : Nat.size M + 2 ≤ B)
    (hQ : Nat.size Q + 2 ≤ B) (hb : Nat.size b + 2 ≤ B)
    (hP : Nat.size P ≤ B) (hF : Nat.size F + 2 ≤ B) (he : e + 1 ≤ B)
    (htau : tau.width ≤ B) (ha : a.width ≤ B)
    (hparent : ∀ q, (parentInitial q).width ≤ B)
    (hchild : ∀ i q, (child i q).width ≤ B)
    (hinitial : ∀ i q, (initial i q).width ≤ B)
    (hcurrent : ∀ i q, (current i q).width ≤ B)
    (hscale : eM + eb + eF + 7 ≤ B)
    (hleft : Nat.size cell.1 ≤ B) (hright : Nat.size cell.2 ≤ B)
    (hPdyadic : ∃ j : ℕ, P = 2 ^ j) :
    (preparedComputedCellGroupWithWork source target parent b P F e Q eM eb eF
      hMdef hbdef hFdef hPpos tau a parentInitial child initial current draw cell).2 ≤
      groupScalesBitBudget eM eb eF +
        preparedCellGroupBitBudget M (groupDyadicScales M b (nat F).value).length e b P B + 1 := by
  have hs := groupScalesWithWork_bounds eM eb eF
  have hc := preparedCellGroupWithWork_cost source target parent b P F e Q B
    (by rw [hbdef]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hMdef hbdef hFdef)
    draw hPpos cell hB hnx hny hM hQ hb hP hF he htau ha hparent hchild hinitial hcurrent
    (fun x hx => (hs.1 x hx).trans hscale) hleft hright ⟨eb, hbdef⟩ hPdyadic
  change (groupScalesWithWork eM eb eF).2 + _ + 1 ≤ _
  omega

end BinaryFraction
end EditApproximation

end OAI

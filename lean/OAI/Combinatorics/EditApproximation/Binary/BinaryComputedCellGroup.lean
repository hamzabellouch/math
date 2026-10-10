import OAI.Combinatorics.EditApproximation.Binary.BinaryCellGroupKernel

namespace OAI

/-! The cell kernel constructs its rational scales from the dyadic
parameter exponents. -/

namespace EditApproximation
namespace BinaryFraction

theorem computedGroupScales_value (M b F eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hb : b = 2 ^ eb) (hF : F = 2 ^ eF) :
    (groupScalesWithWork eM eb eF).1.map value = groupDyadicScales M b (nat F).value := by
  rw [nat_value, hM, hb, hF, Nat.cast_pow, Nat.cast_ofNat]
  exact groupScalesWithWork_value eM eb eF

def computedCellGroupWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hb : b = 2 ^ eb) (hF : F = 2 ^ eF)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ) :
    Option (BinaryBellmanAction (TargetInterval target.length)
      (Fin M × TargetInterval target.length) M) × ℕ :=
  let scales := groupScalesWithWork eM eb eF
  let result := cellGroupWithWork source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current scales.1
    (computedGroupScales_value M b F eM eb eF hM hb hF) draw cell
  (result.1, scales.2 + result.2 + 1)

theorem computedCellGroupWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P F exponent Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hb : b = 2 ^ eb) (hF : F = 2 ^ eF)
    (tau a : BinaryFraction) (parentInitial : TargetInterval target.length → BinaryFraction)
    (child initial current : Fin M → TargetInterval target.length → BinaryFraction)
    (draw : cellScaleDraw M b Q (nat F).value) (cell : ℕ × ℕ) (hP : 0 < P) :
    ((computedCellGroupWithWork source target parent b P F exponent Q eM eb eF hM hb hF tau a
      parentInitial child initial current draw cell).1.map BinaryBellmanAction.decode) =
      chooseCellGroupAction source target parent b P F exponent Q tau.value a.value
        (fun q => (parentInitial q).value) (fun i q => (child i q).value)
        (fun i q => (initial i q).value) (fun i q => (current i q).value) cell
        (Eq.mp (congrArg (cellScaleDraw M b Q) (nat_value F)) draw) := by
  have h := cellGroupWithWork_value source target parent b P F exponent Q
    (by rw [hb]; exact Nat.two_pow_pos eb) tau a parentInitial child initial current
    (groupScalesWithWork eM eb eF).1 (computedGroupScales_value M b F eM eb eF hM hb hF)
    draw cell hP
  simpa only [computedCellGroupWithWork] using h

end BinaryFraction
end EditApproximation

end OAI

import OAI.Combinatorics.EditApproximation.Geometry.Connections
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-!
# Integer endpoint grids

Rounding is an executable integer division. It preserves valid interval
states and shared endpoints, and the edit-distance perturbation is bounded
by the actual two remainders. No real-valued grid is substituted for it.
-/

namespace EditApproximation



theorem gridRound_le (spacing position : ℕ) : gridRound spacing position ≤ position :=
  Nat.mul_div_le _ _

theorem gridRound_mono (spacing : ℕ) : Monotone (gridRound spacing) := by
  intro p q hpq
  exact Nat.mul_le_mul_left spacing (Nat.div_le_div_right hpq)

theorem gridRound_distance (spacing position : ℕ) :
    Nat.dist position (gridRound spacing position) = position % spacing := by
  have h := Nat.mod_add_div position spacing
  unfold Nat.dist gridRound
  omega

theorem gridRound_error_lt (spacing position : ℕ) (hspacing : 0 < spacing) :
    Nat.dist position (gridRound spacing position) < spacing := by
  rw [gridRound_distance]
  exact Nat.mod_lt _ hspacing

theorem gridRound_of_dvd {spacing position : ℕ} (hdiv : spacing ∣ position) :
    gridRound spacing position = position := by
  have hzero := Nat.mod_eq_zero_of_dvd hdiv
  have h := Nat.mod_add_div position spacing
  simpa only [hzero, zero_add, gridRound] using h

@[simp] theorem gridRound_one (position : ℕ) : gridRound 1 position = position := by
  simp [gridRound]



theorem roundInterval_shared {n spacing : ℕ} (first second : TargetInterval n)
    (hshared : first.hi = second.lo) :
    (roundInterval spacing first).hi = (roundInterval spacing second).lo := by
  exact congrArg (gridRound spacing) hshared

theorem roundInterval_error {n : ℕ} (spacing : ℕ) (hspacing : 0 < spacing)
    (state : TargetInterval n) :
    Nat.dist state.lo (roundInterval spacing state).lo +
      Nat.dist state.hi (roundInterval spacing state).hi < 2 * spacing := by
  have hlo := gridRound_error_lt spacing state.lo hspacing
  have hhi := gridRound_error_lt spacing state.hi hspacing
  change Nat.dist state.lo (gridRound spacing state.lo) +
    Nat.dist state.hi (gridRound spacing state.hi) < 2 * spacing
  omega

theorem edit_roundInterval_bound {α : Type*} (source target : List α)
    (spacing : ℕ) (state : TargetInterval target.length) :
    EditDistortion.edit source
        (substring target (roundInterval spacing state).lo (roundInterval spacing state).hi) ≤
      EditDistortion.edit source (substring target state.lo state.hi) +
        state.lo % spacing + state.hi % spacing := by
  have hperturb := edit_substring_endpoints_le target state.lo state.hi
    (roundInterval spacing state).lo (roundInterval spacing state).hi
  have htri := EditDistortion.cost_triangle (s := true) source
    (substring target state.lo state.hi)
    (substring target (roundInterval spacing state).lo (roundInterval spacing state).hi)
  change EditDistortion.edit source
      (substring target (roundInterval spacing state).lo (roundInterval spacing state).hi) ≤
    EditDistortion.edit source (substring target state.lo state.hi) +
      EditDistortion.edit (substring target state.lo state.hi)
        (substring target (roundInterval spacing state).lo (roundInterval spacing state).hi) at htri
  apply htri.trans
  have hlo : Nat.dist state.lo (roundInterval spacing state).lo = state.lo % spacing :=
    gridRound_distance spacing state.lo
  have hhi : Nat.dist state.hi (roundInterval spacing state).hi = state.hi % spacing :=
    gridRound_distance spacing state.hi
  rw [hlo, hhi] at hperturb
  omega

end EditApproximation

end OAI

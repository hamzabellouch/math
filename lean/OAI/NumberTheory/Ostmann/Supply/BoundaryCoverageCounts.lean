import OAI.NumberTheory.Ostmann.Supply.BoundaryCoverageFinite

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Supply
open Filter Ostmann.Preliminaries
open scoped BigOperators

theorem eventually_initial_count_upper (S : Set ℕ) {C : ℝ} (hC : 0 < C)
    (hupper : ∀ᶠ X : ℕ in atTop,
      (countUpTo S X : ℝ) ≤ C * Real.sqrt X * Real.log (X : ℝ)^2) :
    ∀ᶠ X : ℕ in atTop,
      (countUpTo S (initialWindowCutoff X) : ℝ) ≤
        C * (X : ℝ)^(9/20:ℝ) * Real.log (X : ℝ)^2 := by
  filter_upwards [initialWindowCutoff_tendsto.eventually hupper,
    initialWindowCutoff_tendsto.eventually_ge_atTop 2,
    eventually_ge_atTop 2] with X hupper hcut hX
  have hxr : (1:ℝ) ≤ X := by exact_mod_cast (show 1≤X by omega)
  have hcutr : (1:ℝ) ≤ initialWindowCutoff X := by exact_mod_cast (show 1 ≤ initialWindowCutoff X by omega)
  have hfloor : (initialWindowCutoff X:ℝ) ≤ (X:ℝ)^(9/10:ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (by positivity) _)
  have hlogs : Real.log (initialWindowCutoff X:ℝ) ≤ Real.log (X:ℝ) :=
    Real.log_le_log (by linarith) (hfloor.trans (Real.rpow_le_self_of_one_le hxr (by norm_num)))
  have hsqrt : Real.sqrt (initialWindowCutoff X:ℝ) ≤ (X:ℝ)^(9/20:ℝ) := by
    have hid : Real.sqrt ((X:ℝ)^(9/10:ℝ)) = (X:ℝ)^(9/20:ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (show (0:ℝ)≤X by positivity)]
      norm_num
    simpa only [hid] using Real.sqrt_le_sqrt hfloor
  apply hupper.trans
  gcongr

theorem eventually_boundaryPairCount_le (d : Decomposition) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      (boundaryPairCount d X : ℝ) ≤
        2*C^2*(X:ℝ)^(19/20:ℝ)*Real.log (X:ℝ)^4 := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := summand_sqrt_bounds d
  refine ⟨C,hC,?_⟩
  have hA := hbounds.mono (fun X h => h.2.2.1)
  have hB := hbounds.mono (fun X h => h.2.2.2)
  filter_upwards [hA,hB,eventually_initial_count_upper d.A hC hA,
    eventually_initial_count_upper d.B hC hB,eventually_ge_atTop 1]
    with X hA hB hAs hBs hX
  have hp : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hab := mul_le_mul hAs hB (Nat.cast_nonneg _) (by positivity)
  have hba := mul_le_mul hA hBs (Nat.cast_nonneg _) (by positivity)
  have hid : (X:ℝ)^(9/20:ℝ)*Real.sqrt X=(X:ℝ)^(19/20:ℝ) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hp]
    norm_num
  have hleft :
      (C*(X:ℝ)^(9/20:ℝ)*Real.log (X:ℝ)^2)*
        (C*Real.sqrt X*Real.log (X:ℝ)^2) =
        C^2*(X:ℝ)^(19/20:ℝ)*Real.log (X:ℝ)^4 := by
    rw [←hid]
    ring
  have hright :
      (C*Real.sqrt X*Real.log (X:ℝ)^2)*
        (C*(X:ℝ)^(9/20:ℝ)*Real.log (X:ℝ)^2) =
        C^2*(X:ℝ)^(19/20:ℝ)*Real.log (X:ℝ)^4 := by
    rw [mul_comm]
    exact hleft
  rw [hleft] at hab
  rw [hright] at hba
  simp only [boundaryPairCount,Nat.cast_add,Nat.cast_mul]
  nlinarith

end Ostmann.Supply

end

end OAI

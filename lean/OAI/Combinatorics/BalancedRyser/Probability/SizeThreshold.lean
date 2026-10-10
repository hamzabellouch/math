import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace OAI

open Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

theorem eventually_size_condition (rho : ℝ) (hrho : 0 < rho) :
    ∀ᶠ q : ℕ in atTop,
      4 ≤ q ∧ 2 * (1 + (Nat.ceil (Real.log (q : ℝ)) : ℝ)) < rho * q := by
  have hlogReal : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (rho / 4) * ‖x‖ :=
    Real.isLittleO_log_id_atTop.bound (by positivity)
  have hlog :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop) hlogReal
  have hlarge : ∀ᶠ q : ℕ in atTop, (8 / rho : ℝ) < q :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop)
      (eventually_gt_atTop (8 / rho))
  filter_upwards [hlog, hlarge, eventually_ge_atTop 4] with q hlog hlarge hq
  refine ⟨hq, ?_⟩
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqnonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hlognonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqone
  have hlogbound : Real.log (q : ℝ) ≤ (rho / 4) * q := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hlognonneg, abs_of_nonneg hqnonneg] using hlog
  have hceil : (Nat.ceil (Real.log (q : ℝ)) : ℝ) < Real.log (q : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlognonneg
  have hrhoq : 8 < rho * (q : ℝ) := by
    have := (div_lt_iff₀ hrho).mp hlarge
    nlinarith
  nlinarith

theorem exists_size_threshold (rho : ℝ) (hrho : 0 < rho) :
    ∃ q0 : ℕ, ∀ q : ℕ, q0 ≤ q →
      4 ≤ q ∧ 2 * (1 + (Nat.ceil (Real.log (q : ℝ)) : ℝ)) < rho * q := by
  exact eventually_atTop.1 (eventually_size_condition rho hrho)

theorem constituent_cap_lt_order {q B : ℕ} {rho : ℝ}
    (hrho : rho < 1)
    (hsize : 2 * (1 + (B : ℝ)) < rho * q) : B < q := by
  have hqnonneg : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hBnonneg : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hmul : rho * (q : ℝ) ≤ q := by nlinarith
  have : (B : ℝ) < q := by nlinarith
  exact_mod_cast this

theorem ordinary_pencil_gap {q B t : ℝ} {rho : ℝ}
    (hB : 0 ≤ B) (hsize : 2 * (1 + B) < rho * q)
    (ht : t ≤ rho * q / 4) : 1 + t < rho * q := by
  nlinarith

theorem partner_pencil_gap {q B t : ℝ} {rho : ℝ}
    (hsize : 2 * (1 + B) < rho * q)
    (ht : t ≤ rho * q / 4) : 1 + B + 2 * t < rho * q := by
  nlinarith

end Balanced

end OAI

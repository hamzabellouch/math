import Mathlib
import OAI.NumberTheory.Jacobsthal.Estimates.UniformCollisionError

namespace OAI

namespace Erdos970

section

namespace ErdosLineCollision

theorem normalized_collision_bound (I K C n R N L : ℝ)
    (hK0 : 0 ≤ K) (hC : 0 ≤ C) (hn : 0 < n) (hN : 0 < N) (hL : 0 < L)
    (hcollision : I^2 ≤ K*(C*N^2+I)) (hthin : K ≤ n*R/L^6) (hI : I ≤ n*N) :
    (I/(n*N))^2 ≤ C*R/(n*L^6)+R/(N*L^6) := by
  have hup : I^2 ≤ (n*R/L^6)*(C*N^2+n*N) := by
    calc
      _ ≤ K*(C*N^2+I) := hcollision
      _ ≤ K*(C*N^2+n*N) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hI) hK0
      _ ≤ _ := mul_le_mul_of_nonneg_right hthin (by positivity)
  rw [div_pow]
  calc
    _ ≤ ((n*R/L^6)*(C*N^2+n*N))/(n*N)^2 :=
      div_le_div_of_nonneg_right hup (sq_nonneg _)
    _ = _ := by field_simp

end ErdosLineCollision

end

section

open Filter
open scoped Topology
namespace ErdosSourceCollision
open ErdosLineCollision

theorem uniform_normalized_collision (C eta eps : ℝ) (hC : 0 ≤ C) (heta : 0 < eta) (heps : 0 < eps) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ inc K R N n : ℝ,
      1 < R → R ≤ z^((1 : ℝ)/100) → z^((93 : ℝ)/100) ≤ N →
      eta*R/(4*Real.log R) ≤ n → 0 ≤ K →
      inc^2 ≤ K*(C*N^2+inc) → K ≤ n*R/(Real.log z)^6 → inc ≤ n*N →
      inc ≤ eps*n*N := by
  filter_upwards [uniform_collision_error C eta eps hC heta heps] with z hz
  refine ⟨hz.1,?_⟩
  intro inc K R N n hR hRz hN hcount hK hcoll hthin hI
  have hz0 : 0 < z := by linarith [hz.1]
  have hR0 : 0 < R := by linarith
  have hlogR : 0 < Real.log R := Real.log_pos hR
  have hn : 0 < n := (div_pos (mul_pos heta hR0) (mul_pos (by norm_num) hlogR)).trans_le hcount
  have hNp : 0 < N := (Real.rpow_pos_of_pos hz0 _).trans_le hN
  have hL : 0 < Real.log z := by linarith [hz.2.1]
  have hsq := (normalized_collision_bound inc K C n R N (Real.log z) hK hC hn hNp hL hcoll hthin hI).trans
    (hz.2.2 R N n hR hRz hN hcount)
  have hratio : inc/(n*N) ≤ eps := by nlinarith [sq_nonneg (inc/(n*N)-eps)]
  have hh := (div_le_iff₀ (mul_pos hn hNp)).mp hratio
  nlinarith

end ErdosSourceCollision

end

end Erdos970

end OAI

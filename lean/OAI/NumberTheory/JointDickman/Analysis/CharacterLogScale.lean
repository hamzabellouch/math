import OAI.NumberTheory.JointDickman.Analysis.CharacterRectangleLog

namespace OAI

/-! # Logarithmic modulus and height choices for the character contour -/
namespace JointDickman

theorem modulus_add_two_le {L C : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hq : (q:ℝ) ≤ L^C) :
    (q:ℝ)+2 ≤ 3*L^C := by
  have hp := Real.one_le_rpow hL hC
  linarith

theorem character_scale_product_bound {L C B : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hq : (q:ℝ) ≤ L^C) :
    ((q:ℝ)+2)*(2*L^B+2) ≤ 12*L^(C+B) := by
  have hq' := modulus_add_two_le hL hC hq
  have hp := Real.one_le_rpow hL hB
  have ht : 2*L^B+2 ≤ 4*L^B := by linarith
  calc
    _ ≤ (3*L^C)*(4*L^B) := mul_le_mul hq' ht (by positivity) (by positivity)
    _ = 12*L^(C+B) := by rw [Real.rpow_add (by linarith : 0 < L)]; ring

theorem character_scale_width_lower {L C B A ε : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hq : (q:ℝ) ≤ L^C) :
    A*(12:ℝ)^(-ε)*L^(-(C+B)*ε) ≤ characterContourWidth A ε q (2*L^B) := by
  have hprod := character_scale_product_bound hL hC hB hq
  have hp : (12*L^(C+B))^(-ε) ≤ (((q:ℝ)+2)*(2*L^B+2))^(-ε) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hprod (by linarith)
  have he : (12*L^(C+B))^(-ε) = (12:ℝ)^(-ε)*L^(-(C+B)*ε) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ←Real.rpow_mul (by linarith : 0 ≤ L)]
    congr 2
    ring
  rw [he] at hp
  simpa only [characterContourWidth, mul_assoc] using mul_le_mul_of_nonneg_left hp hA

theorem character_scale_width_sqrt_growth {L C B A ε : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hq : (q:ℝ) ≤ L^C) (he : (C+B)*ε = 1/2) :
    (A*(12:ℝ)^(-ε)/2)*L^(1/2:ℝ) ≤
      L*(characterContourWidth A ε q (2*L^B)/2) := by
  have h := mul_le_mul_of_nonneg_left (character_scale_width_lower hL hC hB hA hε hq)
    (show 0 ≤ L/2 by linarith)
  have hexp : -(C+B)*ε = -(1/2:ℝ) := by linarith
  rw [hexp] at h
  have hp : L*L^(-(1/2:ℝ)) = L^(1/2:ℝ) := by
    nth_rw 1 [←Real.rpow_one L]
    rw [←Real.rpow_add (by linarith : 0 < L)]
    norm_num
  calc
    _ = (L/2)*(A*(12:ℝ)^(-ε)*L^(-(1/2:ℝ))) := by rw [←hp]; ring
    _ ≤ (L/2)*characterContourWidth A ε q (2*L^B) := h
    _ = _ := by ring

theorem character_scale_tail_bound {L C B D : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hq : (q:ℝ) ≤ L^C)
    (he : C/4-B/2 ≤ -D) :
    ((q:ℝ)+2)^(1/4:ℝ)*(L^B)^(-1/2:ℝ) ≤ (3:ℝ)^(1/4:ℝ)*L^(-D) := by
  have hq' := Real.rpow_le_rpow (show (0:ℝ) ≤ q+2 by positivity)
    (modulus_add_two_le hL hC hq) (by norm_num : (0:ℝ) ≤ 1/4)
  calc
    _ ≤ (3*L^C)^(1/4:ℝ)*(L^B)^(-1/2:ℝ) :=
      mul_le_mul_of_nonneg_right hq' (Real.rpow_nonneg (by positivity) _)
    _ = (3:ℝ)^(1/4:ℝ)*L^(C/4-B/2) := by
      rw [Real.mul_rpow (by norm_num) (by positivity),
        ←Real.rpow_mul (by linarith : 0 ≤ L), ←Real.rpow_mul (by linarith : 0 ≤ L),
        mul_assoc, ←Real.rpow_add (by linarith : 0 < L)]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he) (by positivity)

theorem character_scale_horizontal_bound {L C B D : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hq : (q:ℝ) ≤ L^C)
    (he : C/4-7*B/4 ≤ -D) :
    (((q:ℝ)+2)*(L^B+2))^(1/4:ℝ)/(1+(L^B)^2) ≤ (9:ℝ)^(1/4:ℝ)*L^(-D) := by
  have hL0 : 0 < L := by linarith
  have hq' := modulus_add_two_le hL hC hq
  have hpow : 1 ≤ L^B := Real.one_le_rpow hL hB
  have ht : L^B+2 ≤ 3*L^B := by linarith
  have hprod : ((q:ℝ)+2)*(L^B+2) ≤ 9*L^(C+B) := by
    calc
      _ ≤ (3*L^C)*(3*L^B) := mul_le_mul hq' ht (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add hL0]; ring
  have hsquare : (L^B)^2 = L^(2*B) := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hL0.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  calc
    _ ≤ (9*L^(C+B))^(1/4:ℝ)/(L^B)^2 := div_le_div₀ (by positivity)
      (Real.rpow_le_rpow (by positivity) hprod (by norm_num)) (by positivity) (by linarith [sq_nonneg (L^B)])
    _ = (9:ℝ)^(1/4:ℝ)*L^(C/4-7*B/4) := by
      rw [hsquare, Real.mul_rpow (by norm_num) (by positivity), ←Real.rpow_mul hL0.le,
        mul_div_assoc, ←Real.rpow_sub hL0]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL he) (by positivity)

theorem character_scale_exponents {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    let B := 2*D+C+10
    0 < B ∧ C/4-B/2 ≤ -D ∧ C/4-7*B/4 ≤ -D := by
  dsimp only
  constructor
  · linarith
  constructor <;> linarith

end JointDickman

end OAI

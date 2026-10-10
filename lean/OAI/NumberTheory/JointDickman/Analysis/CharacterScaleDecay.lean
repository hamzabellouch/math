import OAI.NumberTheory.JointDickman.Analysis.CharacterLogScale
import OAI.NumberTheory.JointDickman.Analysis.LaplaceMovingCutoff

namespace OAI

/-! # Rapid decay of the character contour at logarithmic scales -/
namespace JointDickman
open Filter Asymptotics
open scoped Topology

theorem rpow_mul_stretched_exp_isLittleO {a α : ℝ} (ha : 0 < a) (hα : 0 < α)
    (p b : ℝ) :
    (fun L : ℝ => L^p*Real.exp (-a*L^α)) =o[atTop] (fun L => L^b) := by
  have h := (isBigO_refl (fun L : ℝ => L^p) atTop).mul_isLittleO
    (stretched_exp_isLittleO_rpow ha hα (b-p))
  apply h.congr' (Eventually.of_forall (fun _ => rfl))
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [←Real.rpow_add hL]
  congr 1
  ring

theorem character_scale_majorant_bound {L C B : ℝ} {q : ℕ}
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hB : 0 ≤ B) (hq : (q:ℝ) ≤ L^C) :
    (((q:ℝ)+2)*(L^B+2))^(1/4:ℝ) ≤ (9:ℝ)^(1/4:ℝ)*L^((C+B)/4) := by
  have hp := Real.one_le_rpow hL hB
  have ht : L^B+2 ≤ 3*L^B := by linarith
  have hprod : ((q:ℝ)+2)*(L^B+2) ≤ 9*L^(C+B) := by
    calc
      _ ≤ (3*L^C)*(3*L^B) := mul_le_mul (modulus_add_two_le hL hC hq) ht
        (by positivity) (by positivity)
      _ = _ := by rw [Real.rpow_add (by linarith : 0 < L)]; ring
  calc
    _ ≤ (9*L^(C+B))^(1/4:ℝ) := Real.rpow_le_rpow (by positivity) hprod (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ←Real.rpow_mul (by linarith : 0 ≤ L)]
      congr 2
      ring

theorem character_scale_left_decay {C B A ε : ℝ}
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hA : 0 < A) (hε : 0 < ε)
    (he : (C+B)*ε = 1/2) (D : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℕ, (q:ℝ) ≤ L^C →
      (((q:ℝ)+2)*(L^B+2))^(1/4:ℝ)*
        Real.exp (-(L*(characterContourWidth A ε q (2*L^B)/2))) ≤
      (9:ℝ)^(1/4:ℝ)*L^(-D) := by
  let a := A*(12:ℝ)^(-ε)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hdec := rpow_mul_stretched_exp_isLittleO ha (by norm_num : (0:ℝ) < 1/2)
    ((C+B)/4) (-D)
  filter_upwards [eventually_ge_atTop (1:ℝ), hdec.def zero_lt_one] with L hL hdecL
  intro q hq
  have hLL : 0 < L := by linarith
  have hdecL' : L^((C+B)/4)*Real.exp (-a*L^(1/2:ℝ)) ≤ L^(-D) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ L^((C+B)/4)*
      Real.exp (-a*L^(1/2:ℝ)) by positivity),
      abs_of_nonneg (Real.rpow_nonneg hLL.le _), one_mul] using hdecL
  have hg := character_scale_width_sqrt_growth hL hC hB hA.le hε.le hq he
  have hExp : Real.exp (-(L*(characterContourWidth A ε q (2*L^B)/2))) ≤
      Real.exp (-a*L^(1/2:ℝ)) := Real.exp_le_exp.mpr (by dsimp [a]; linarith)
  calc
    _ ≤ ((9:ℝ)^(1/4:ℝ)*L^((C+B)/4))*Real.exp (-a*L^(1/2:ℝ)) :=
      mul_le_mul (character_scale_majorant_bound hL hC hB hq) hExp
        (Real.exp_pos _).le (by positivity)
    _ = (9:ℝ)^(1/4:ℝ)*(L^((C+B)/4)*Real.exp (-a*L^(1/2:ℝ))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecL' (by positivity)

theorem character_scale_choose {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ B ε : ℝ, 0 < B ∧ 0 < ε ∧ ε ≤ 1 ∧ (C+B)*ε = 1/2 ∧
      C/4-B/2 ≤ -D ∧ C/4-7*B/4 ≤ -D := by
  let B := 2*D+C+10
  have hB : 0 < B := by dsimp [B]; linarith
  have hCB : 0 < C+B := by linarith
  refine ⟨B,1/(2*(C+B)),hB,by positivity,?_,?_,?_,?_⟩
  · apply (div_le_one (by positivity : 0 < 2*(C+B))).mpr
    dsimp [B]
    linarith
  · field_simp
  · dsimp [B]; linarith
  · dsimp [B]; linarith

end JointDickman

end OAI

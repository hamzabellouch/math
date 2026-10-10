import OAI.NumberTheory.JointDickman.Analysis.CharacterPerronEstimate
import OAI.NumberTheory.JointDickman.Analysis.CharacterScaleDecay

namespace OAI

/-! # Uniform logarithmic savings for the character Perron integral -/
namespace JointDickman
open Complex Filter
open scoped Topology

theorem characterPerron_log_bound {z C D : ℝ}
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (q:ℝ) ≤ L^C → χ ≠ 1 →
        ‖VerticalIntegral' (characterNormalizedPerron χ z L) (1/L)‖ ≤ K*L^(-D) := by
  obtain ⟨B,ε,hB,hε,hε1,hprod,hBt,hBh⟩ := character_scale_choose hC hD
  obtain ⟨A,F,G,hA,hA4,hF,hG,hest⟩ := characterPerron_estimate hz hz1 hε hε1
  let K := F*Real.exp 1*(3:ℝ)^(1/4:ℝ) +
    (1/(2*Real.pi))*(5*G*Real.pi*(9:ℝ)^(1/4:ℝ) +
      10*G*Real.exp 1*(9:ℝ)^(1/4:ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,hK,?_⟩
  have hdec := character_scale_left_decay hC hB.le hA hε hprod D
  have hheight : ∀ᶠ L : ℝ in atTop, 3 < L^B :=
    (tendsto_rpow_atTop hB).eventually (eventually_gt_atTop 3)
  filter_upwards [eventually_ge_atTop (2:ℝ), hheight, hdec] with L hL hT hleft
  intro q _ χ hq hn
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  let T := L^B
  let δ := characterContourWidth A ε q (2*T)
  let W := (((q:ℝ)+2)*(T+2))^(1/4:ℝ)
  have hc : 0 < 1/L := by positivity
  have hc2 : 1/L ≤ 1/2 := (div_le_iff₀ hL0).mpr (by linarith)
  have hδ4 : δ ≤ 1/4 := by
    have hw : 1 ≤ ((q:ℝ)+2)*(2*T+2) := by
      change 3 < T at hT
      nlinarith [Nat.cast_nonneg (α := ℝ) q]
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hw (show -ε ≤ 0 by linarith)
    exact (mul_le_of_le_one_right hA.le hp).trans hA4
  have hlen : δ/2+1/L ≤ 1 := by linarith
  have hLc : L*(1/L) = 1 := by field_simp
  have hp := hest q χ hn L (1/L) T hL0.le hc hc2 hT
  change ‖VerticalIntegral' (characterNormalizedPerron χ z L) (1/L)‖ ≤
    F*((q:ℝ)+2)^(1/4:ℝ)*Real.exp (L*(1/L))*T^(-1/2:ℝ) +
    (1/(2*Real.pi))*((5*(G*W)*Real.exp (-(L*(δ/2))))*Real.pi +
      2*((5*(G*W)*Real.exp (L*(1/L))/(1+T^2))*(δ/2+1/L))) at hp
  rw [hLc] at hp
  have ht := character_scale_tail_bound hL1 hC hq hBt
  have hh := character_scale_horizontal_bound hL1 hC hB.le hq hBh
  have hl := hleft q hq
  have htail : F*((q:ℝ)+2)^(1/4:ℝ)*Real.exp 1*T^(-1/2:ℝ) ≤
      (F*Real.exp 1*(3:ℝ)^(1/4:ℝ))*L^(-D) := by
    calc
      _ = (F*Real.exp 1)*(((q:ℝ)+2)^(1/4:ℝ)*T^(-1/2:ℝ)) := by ring
      _ ≤ (F*Real.exp 1)*((3:ℝ)^(1/4:ℝ)*L^(-D)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have hleft' : (5*(G*W)*Real.exp (-(L*(δ/2))))*Real.pi ≤
      (5*G*Real.pi*(9:ℝ)^(1/4:ℝ))*L^(-D) := by
    calc
      _ = (5*G*Real.pi)*(W*Real.exp (-(L*(δ/2)))) := by ring
      _ ≤ (5*G*Real.pi)*((9:ℝ)^(1/4:ℝ)*L^(-D)) :=
        mul_le_mul_of_nonneg_left hl (by positivity)
      _ = _ := by ring
  have hhor : 2*((5*(G*W)*Real.exp 1/(1+T^2))*(δ/2+1/L)) ≤
      (10*G*Real.exp 1*(9:ℝ)^(1/4:ℝ))*L^(-D) := by
    calc
      _ ≤ 2*(5*(G*W)*Real.exp 1/(1+T^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_of_le_one_right (by dsimp [W]; positivity) hlen
      _ = (10*G*Real.exp 1)*(W/(1+T^2)) := by ring
      _ ≤ (10*G*Real.exp 1)*((9:ℝ)^(1/4:ℝ)*L^(-D)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  apply hp.trans
  calc
    _ ≤ (F*Real.exp 1*(3:ℝ)^(1/4:ℝ))*L^(-D) + (1/(2*Real.pi))*
        ((5*G*Real.pi*(9:ℝ)^(1/4:ℝ))*L^(-D) +
          (10*G*Real.exp 1*(9:ℝ)^(1/4:ℝ))*L^(-D)) :=
      add_le_add htail (mul_le_mul_of_nonneg_left (add_le_add hleft' hhor) (by positivity))
    _ = K*L^(-D) := by dsimp [K]; ring

end JointDickman

end OAI

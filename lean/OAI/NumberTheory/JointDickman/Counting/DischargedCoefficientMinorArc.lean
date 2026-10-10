import OAI.NumberTheory.JointDickman.Arithmetic.SquarefreeMinorArc
import OAI.NumberTheory.JointDickman.Arithmetic.LogarithmicScaleBounds
import OAI.NumberTheory.JointDickman.Counting.CoefficientScalePower

namespace OAI

/-! # The coefficient minor-arc estimate on the actual logarithmic range -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem coefficient_minorArc_bounded_log {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ B : ℕ in atTop,
    ∀ (Y : ℕ) (X θ V : ℝ), 0 < Y →
      (B:ℝ)/2 ≤ Real.log Y → Real.log Y ≤ 3*(B:ℝ) →
      (B:ℝ)^12 ≤ X → X ≤ (Y:ℝ)*(B:ℝ)^2 → (Y:ℝ) ≤ V*X →
      ¬ InRationalArc θ ((B:ℝ)^12) ((B:ℝ)^13/X) →
      ‖coefficientAdditivePartialSum B Y θ‖ ≤
        C*(1+2*Real.pi*V)*Y*(B:ℝ)^(-1/2+ε) := by
  obtain ⟨C,hC,hminor⟩ := squarefree_minor_arc_sum_bound
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [eventually_nat_log_linear 80,coefficientScale_power (half_pos hε),
    eventually_nat_one_add_log_power (half_pos hε),eventually_ge_atTop 2]
    with B hlinear hscale hlog hB
  intro Y X θ V hY hYlo hYhi hX hXY hYV hnot
  have hB0 : (0:ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hX0 : 0 < X := (pow_pos hB0 12).trans_le hX
  have hY0 : (0:ℝ) < Y := by exact_mod_cast hY
  have hV : 0 ≤ V := by nlinarith
  have hfactor : 0 ≤ 1+2*Real.pi*V := by positivity
  have hraw := hminor (roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) (1/2))
    (roughSquarefreeWeight_isMultiplicative _ _)
    (roughSquarefreeWeight_half_bounded _)
    (by intro n hn; simp [roughSquarefreeWeight,squarefreeWeight,hn])
    Y B X θ V hY hB hlinear hYlo hYhi hX hXY hYV hnot
  have hi : Ioc 0 Y = Icc 1 Y := by
    ext n
    simp only [mem_Ioc,mem_Icc]
    omega
  rw [hi] at hraw
  rw [coefficientAdditivePartialSum_factor,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (coefficientScale_nonneg B)]
  calc
    _ ≤ coefficientScale B*(C*(1+2*Real.pi*V)*Y*(1+Real.log B)/(B:ℝ)) :=
      mul_le_mul_of_nonneg_left hraw (coefficientScale_nonneg B)
    _ ≤ (B:ℝ)^(1/2+ε/2)*(C*(1+2*Real.pi*V)*Y*(2*(B:ℝ)^(ε/2))/(B:ℝ)) := by
      apply mul_le_mul hscale
      · gcongr
      · positivity
      · positivity
    _ = _ := by
      have hp : (B:ℝ)^(1/2+ε/2)*(B:ℝ)^(ε/2)/(B:ℝ) = (B:ℝ)^(-1/2+ε) := by
        calc
          _ = (B:ℝ)^((1/2+ε/2)+(ε/2))/(B:ℝ) := by rw [←Real.rpow_add hB0]
          _ = (B:ℝ)^((1/2+ε/2)+(ε/2))/(B:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
          _ = _ := by
            rw [←Real.rpow_sub hB0]
            congr 1
            ring
      calc
        _ = 2*C*(1+2*Real.pi*V)*Y*((B:ℝ)^(1/2+ε/2)*(B:ℝ)^(ε/2)/(B:ℝ)) := by ring
        _ = _ := by rw [hp]

end JointDickman

end OAI

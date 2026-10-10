import Mathlib
import OAI.Analysis.CoulombIonization.Variational.SmoothNewton

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff Topology

namespace CoulombAtom

lemma configurationOne_finrank : Module.finrank ℝ (Configuration 1) = 3 := by
  change Module.finrank ℝ (Fin 1 → Space) = 3
  rw [Module.finrank_pi_fintype]
  simp only [Space,finrank_euclideanSpace_fin,Fin.sum_univ_one]

lemma packetDensity_scale (y x : Space) {r : ℝ} (hr : 0 < r) :
    packetDensity y r x = r⁻¹^3 * packetDensity 0 1 (r⁻¹ • (x-y)) := by
  rw [packetDensity_formula,packetDensity_formula,inv_pow,inv_pow,inv_pow,
    Real.sq_sqrt (radialScaledRaw_mass_pos hr).le,
    Real.sq_sqrt (radialScaledRaw_mass_pos (by norm_num : (0:ℝ)<1)).le,
    radialScaledRaw_mass r hr,radialScaledRaw_mass 1 (by norm_num),configurationOne_finrank]
  simp only [sub_zero,inv_one,one_smul,one_pow,one_mul,mul_inv_rev]
  ring

lemma packetDensity_unit_pos {x : Space} (hx : ‖x‖ < 1) : 0 < packetDensity 0 1 x := by
  rw [packetDensity_formula]
  have hn : 0 < ‖radialPacketBase x‖ := by
    rw [radialPacketBase,Complex.norm_real,Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    apply Real.smoothTransition.pos_of_pos
    nlinarith [norm_nonneg x]
  simp only [inv_one,sub_zero,one_smul]
  exact mul_pos (mul_pos (Nat.cast_pos.mpr Fintype.card_pos)
    (pow_pos (inv_pos.mpr (Real.sqrt_pos.mpr (radialScaledRaw_mass_pos (by norm_num)))) _))
    (pow_pos hn _)

lemma exists_packet_unit_control : ∃ (L : NNReal) (p : ℝ), 0 < p ∧
    LipschitzWith L (packetDensity 0 1) ∧
    ∀ x : Space, ‖x‖ ≤ 3/4 → p ≤ packetDensity 0 1 x := by
  obtain ⟨L,hL⟩ := (packetDensity_smooth 0 1).lipschitzWith_of_hasCompactSupport
    (packetDensity_compact 0 (by norm_num)) (by simp)
  obtain ⟨z,hz,hmin⟩ := (isCompact_closedBall (0 : Space) (3/4 : ℝ)).exists_isMinOn
    (show (closedBall (0 : Space) (3/4 : ℝ)).Nonempty from ⟨0,by norm_num⟩)
    (packetDensity_continuous 0 1).continuousOn
  refine ⟨L,packetDensity 0 1 z,packetDensity_unit_pos ?_,hL,?_⟩
  · have hh : ‖z‖ ≤ (3/4 : ℝ) := by simpa only [mem_closedBall,dist_zero_right] using hz
    linarith
  · intro x hx
    exact hmin (by simpa only [mem_closedBall,dist_zero_right] using hx)

lemma packetDensity_scaled_difference {L : NNReal} (hL : LipschitzWith L (packetDensity 0 1))
    {r : ℝ} (hr : 0 < r) (x y z : Space) :
    |packetDensity x r z-packetDensity y r z| ≤ (L:ℝ)/r^4*‖x-y‖ := by
  rw [packetDensity_scale x z hr,packetDensity_scale y z hr,←mul_sub,abs_mul,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) _)]
  have hh := hL.dist_le_mul (r⁻¹ • (z-x)) (r⁻¹ • (z-y))
  rw [Real.dist_eq,dist_eq_norm,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),
    show z-x-(z-y)=y-x by abel,norm_sub_rev] at hh
  calc
    _ ≤ r⁻¹^3*((L:ℝ)*(r⁻¹*‖x-y‖)) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

lemma packetDensity_scaled_lower {p r : ℝ} (hr : 0 < r)
    (hp : ∀ z : Space, ‖z‖ ≤ 3/4 → p ≤ packetDensity 0 1 z)
    {z : Space} (hz : ‖z‖ ≤ 3*r/4) : p/r^3 ≤ packetDensity 0 r z := by
  rw [packetDensity_scale 0 z hr,sub_zero]
  have hn : ‖r⁻¹ • z‖ ≤ (3/4:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),inv_mul_le_iff₀ hr]
    linarith
  have hh := mul_le_mul_of_nonneg_left (hp (r⁻¹ • z) hn) (pow_nonneg (inv_nonneg.mpr hr.le) 3)
  simpa only [div_eq_mul_inv,inv_pow,mul_comm] using hh

end CoulombAtom

end

end OAI

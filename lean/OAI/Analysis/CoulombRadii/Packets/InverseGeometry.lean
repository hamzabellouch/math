import Mathlib
import OAI.Analysis.CoulombRadii.LimitTheory.UniformGroundStateCountControl
import OAI.Analysis.CoulombRadii.Packets.AtomicMesh

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma physical_inverse_width_geometry {c r₀ r s A : ℝ} {y : Position}
    (hc : 0 < c) (hr₀ : 0 < r₀) (hr : 0 < r) (hs : 0 < s) (hA : 0 < A)
    (hr₀y : r₀ ≤ ‖y‖) (hry : r ≤ ‖y‖) (hya : Coulomb.atomicCellScale y ≤ A*r) (hrs : r ≤ s) :
    (c*100000/(max 1 A)^packetExponent)*(Coulomb.atomicCellScale y)^(1+packetExponent) ≤
      packetWidth c r₀ s y ∧
    packetWidth c r₀ s y/Coulomb.atomicCellScale y ≤ (100000*c)*s^packetExponent ∧
    r^(101/100:ℝ) ≤ 100000^(101/100:ℝ)*(Coulomb.atomicCellScale y)^(101/100:ℝ) := by
  let a := Coulomb.atomicCellScale y
  have hd : 0 < ‖y‖ := hr.trans_le hry
  have ha : 0 < a := by dsimp [a,Coulomb.atomicCellScale]; positivity
  have he : ‖y‖=100000*a := by dsimp [a,Coulomb.atomicCellScale]; ring
  have hmax : 0 < max 1 A := lt_max_of_lt_left (by norm_num)
  have hma : a/(max 1 A) ≤ min ‖y‖ s := by
    apply le_min
    · rw [div_le_iff₀ hmax,he]
      nlinarith [le_max_left (1:ℝ) A]
    · rw [div_le_iff₀ hmax]
      have H := hya.trans (mul_le_mul_of_nonneg_left hrs hA.le)
      exact H.trans (by nlinarith [le_max_right (1:ℝ) A])
  have hwEq : packetWidth c r₀ s y=c*‖y‖*(min ‖y‖ s)^packetExponent := by
    simp only [packetWidth,max_eq_left hr₀y]
  constructor
  · have H := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (div_nonneg ha.le hmax.le) hma (by norm_num [packetExponent] : 0 ≤ packetExponent))
      (show 0 ≤ c*‖y‖ by positivity)
    rw [←hwEq,Real.div_rpow ha.le hmax.le] at H
    apply le_trans _ H
    rw [he,Real.rpow_add ha,Real.rpow_one]
    ring_nf
    exact le_rfl
  constructor
  · have H := packetWidth_le c r₀ s hc.le hr₀ hs y
    rw [max_eq_left hr₀y,he] at H
    apply (div_le_iff₀ ha).mpr
    exact H.trans_eq (by ring)
  · have H := Real.rpow_le_rpow hr.le hry (by norm_num : (0:ℝ) ≤ 101/100)
    rw [he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 100000) ha.le] at H
    exact H

lemma physical_inverse_count_rescale {K A r a : ℝ} (hK : 0 ≤ K) (hA : 0 < A)
    (hr : 0 < r) (ha : 0 < a) (h : a ≤ A*r) : K/r^3 ≤ (K*A^3)*a^(-3:ℝ) := by
  rw [show a^(-3:ℝ)=(a^3)⁻¹ by rw [Real.rpow_neg ha.le]; norm_num]
  rw [←div_eq_mul_inv,div_le_div_iff₀ (pow_pos hr 3) (pow_pos ha 3)]
  have H : a^3 ≤ (A*r)^3 :=
    (pow_le_pow_iff_left₀ ha.le (mul_nonneg hA.le hr.le) (by norm_num : (3 : ℕ) ≠ 0)).mpr h
  rw [mul_pow] at H
  nlinarith [mul_le_mul_of_nonneg_left H hK]
end NeutralAtom
end

end

end OAI

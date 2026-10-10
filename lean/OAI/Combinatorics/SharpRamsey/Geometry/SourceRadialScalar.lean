import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.SourcePencilScales
import OAI.Combinatorics.SharpRamsey.Geometry.SourceRadialActivation

namespace OAI

section
namespace SharpLogRamsey.SourceRadialTests
open Filter Real
open scoped Topology
noncomputable section

theorem radial_exception_scale {σ P g C N D A : ℝ}
    (hA : 0≤A) (hN : exp (3*σ/2+g)/2≤N) (hgu : g≤σ/2+C)
    (hD : D*exp (σ+P/100-2*g)≤A*exp (2*σ))
    (habs : 2*A*exp C≤exp (P/200)) :
    D≤N*exp (-P/200) := by
  have hd : D≤A*exp (σ-P/100+2*g) := by
    apply (mul_le_mul_iff_left₀ (exp_pos (σ+P/100-2*g))).mp
    calc
      _ ≤ A*exp (2*σ) := hD
      _ = A*exp (σ-P/100+2*g)*exp (σ+P/100-2*g) := by
        rw [mul_assoc,←exp_add]
        congr 2
        ring
  calc
    D ≤ A*exp (σ-P/100+2*g) := hd
    _ ≤ A*exp (C+(3*σ/2+g-P/100)) :=
      mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) hA
    _ = (A*exp C)*exp (3*σ/2+g-P/100) := by rw [exp_add]; ring
    _ ≤ (exp (P/200)/2)*exp (3*σ/2+g-P/100) :=
      mul_le_mul_of_nonneg_right (by linarith only [habs]) (exp_pos _).le
    _ = (exp (3*σ/2+g)/2)*exp (-P/200) := by
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
      congr 1
      rw [←exp_add,←exp_add]
      congr 1
      ring
    _ ≤ N*exp (-P/200) := mul_le_mul_of_nonneg_right hN (exp_pos _).le

theorem eventually_radial_loss (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (P g N D : ℝ),σ^δ≤P →
      exp (3*σ/2+g)/2≤N → g≤σ/2+C →
      D*exp (σ+P/100-2*g)≤70000*exp (2*σ) →
      D≤N*exp (-P/200) := by
  have ht : Tendsto (fun σ : ℝ => exp (σ^δ/200)) atTop atTop :=
    tendsto_exp_atTop.comp ((tendsto_rpow_atTop hδ).atTop_div_const (by norm_num : (0:ℝ)<200))
  filter_upwards [ht.eventually_ge_atTop (140000*exp C)] with σ hσ P g N D hP hN hgu hD
  apply radial_exception_scale (by norm_num) hN hgu hD
  have hh : 140000*exp C≤exp (P/200) := hσ.trans
    (exp_le_exp.mpr (div_le_div_of_nonneg_right hP (by norm_num)))
  simpa only [show (2:ℝ)*70000=140000 by norm_num] using hh

theorem radial_pair_scale {σ P g N : ℝ} (hσ : 0≤σ)
    (hN : 0<N) (hNu : N≤exp (3*σ/2+g)) (hP : 4≤exp (P/100)) :
    exp (σ+P/100-2*g)*(exp σ+1)^2≤(exp (3*σ)/N)^2*exp (P/50) := by
  have hq : 1≤exp σ := one_le_exp_iff.mpr hσ
  have hb : exp (3*σ/2-g)≤exp (3*σ)/N := by
    apply (le_div_iff₀ hN).mpr
    calc
      _ ≤ exp (3*σ/2-g)*exp (3*σ/2+g) := mul_le_mul_of_nonneg_left hNu (exp_pos _).le
      _ = _ := by rw [←exp_add]; congr 1; ring
  calc
    _ ≤ exp (σ+P/100-2*g)*(2*exp σ)^2 := by gcongr; linarith
    _ = 4*exp (3*σ+P/100-2*g) := by rw [mul_pow,←exp_nat_mul]; norm_num; rw [mul_left_comm,←exp_add]; congr 2; ring
    _ ≤ exp (P/100)*exp (3*σ+P/100-2*g) := mul_le_mul_of_nonneg_right hP (exp_pos _).le
    _ = (exp (3*σ/2-g))^2*exp (P/50) := by rw [←exp_nat_mul,←exp_add,←exp_add]; congr 1; norm_num; ring
    _ ≤ _ := by gcongr

theorem strong_small_support {σ P N p : ℝ} (hσ : 0≤σ) (hN : 0<N)
    (hNu : N≤exp (2*σ-4*P)) (hp : 0<p) (hpoly : 400*p≤exp P) :
    2*(exp σ+1)/(1/(100*p))≤(exp (3*σ)/N)*exp (-3*P) := by
  have hq : 1≤exp σ := one_le_exp_iff.mpr hσ
  have hb : exp (σ+4*P)≤exp (3*σ)/N := by
    apply (le_div_iff₀ hN).mpr
    calc
      _ ≤ exp (σ+4*P)*exp (2*σ-4*P) := mul_le_mul_of_nonneg_left hNu (exp_pos _).le
      _ = _ := by rw [←exp_add]; congr 1; ring
  calc
    _ = 200*p*(exp σ+1) := by field_simp; ring
    _ ≤ 400*p*exp σ := by nlinarith
    _ ≤ exp P*exp σ := mul_le_mul_of_nonneg_right hpoly (exp_pos _).le
    _ = exp (σ+4*P)*exp (-3*P) := by rw [←exp_add,←exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hb (exp_pos _).le

end
end SharpLogRamsey.SourceRadialTests

end

end OAI

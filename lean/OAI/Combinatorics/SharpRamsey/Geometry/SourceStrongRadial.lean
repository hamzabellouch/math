import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.SourceRadialScalar

namespace OAI

section
namespace SharpLogRamsey.SourceRadialTests
open Filter Real
open scoped Topology
noncomputable section

theorem eventually_strong_tests (δ C : ℝ) (hδ : 0<δ) :
    ∀ᶠ σ : ℝ in atTop,∀ (P g : ℝ) (N Kp p : ℕ),
    σ^δ≤P → P≤σ/40 → σ/2-4*P≤g → g≤σ/2+C →
    0<p → (p:ℝ)≤σ^2 →
    exp (3*σ/2+g)/2≤(N:ℝ) → (N:ℝ)≤exp (3*σ/2+g) →
    (Kp:ℝ)≤2*exp (σ+17*g/15) →
    let M := ⌈(1/(100*(p:ℝ)))*(N:ℝ)/exp σ⌉₊
    4≤M ∧ M≤N ∧
    198*sqrt ((N:ℝ)/(M:ℝ))<(M:ℝ) ∧
    33*sqrt ((N:ℝ)/(M:ℝ))<exp σ ∧
    (N:ℝ)^2*exp (-5*sqrt ((N:ℝ)/(M:ℝ)))<1/2 ∧ 8*Kp≤M^2 := by
  have ht := ScaleSelection.eventually_polynomial_le_exp_rpow 100 2 1 (1/50)
    (by norm_num) (by norm_num)
  simp only [rpow_one,rpow_ofNat] at ht
  filter_upwards [ht,eventually_rich_tests δ C hδ,eventually_ge_atTop (1:ℝ)]
    with σ hpoly htest hσ P g N Kp p hP hPu hgl hgu hp hpu hN hNu hK
  have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hg : 2*σ/5≤g := by linarith
  have hpg : 100*(p:ℝ)≤exp (g/20) := by
    calc
      _ ≤ 100*σ^2 := mul_le_mul_of_nonneg_left hpu (by norm_num)
      _ ≤ exp ((1/50)*σ) := hpoly
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have ha : exp (-g/20)≤1/(100*(p:ℝ)) := by
    rw [show -g/20=-(g/20) by ring,exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hpg
  have ha2 : 1/(100*(p:ℝ))≤2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(p:ℝ))).mpr
    have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
    linarith
  apply htest g (1/(100*(p:ℝ))) N Kp _ hgu ha ha2 hN hNu hK
  have hpow : 0≤σ^δ := rpow_nonneg (by linarith : 0≤σ) _
  linarith

theorem eventually_strong_list :
    ∀ᶠ σ : ℝ in atTop,∀ (P g : ℝ) (N J p : ℕ),
    P≤σ/40 → σ/2-4*P≤g → 0<p → (p:ℝ)≤σ^2 →
    exp (3*σ/2+g)/2≤(N:ℝ) → (J:ℝ)≤exp (σ/2-2*g/15) →
    2*J≤⌈(1/(100*(p:ℝ)))*(N:ℝ)/exp σ⌉₊ := by
  have ht := ScaleSelection.eventually_polynomial_le_exp_rpow 100 2 1 (1/50)
    (by norm_num) (by norm_num)
  simp only [rpow_one,rpow_ofNat] at ht
  filter_upwards [ht,eventually_ge_atTop (250000:ℝ)]
    with σ hpoly hσ P g N J p hPu hgl hp hpu hN hJ
  have hp' : (0:ℝ)<p := Nat.cast_pos.mpr hp
  have hg : 2*σ/5≤g := by linarith
  have hpg : 100*(p:ℝ)≤exp (g/20) := by
    calc
      _ ≤ 100*σ^2 := mul_le_mul_of_nonneg_left hpu (by norm_num)
      _ ≤ exp ((1/50)*σ) := hpoly
      _ ≤ _ := exp_le_exp.mpr (by linarith)
  have ha : exp (-g/20)≤1/(100*(p:ℝ)) := by
    rw [show -g/20=-(g/20) by ring,exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hpg
  have ha2 : 1/(100*(p:ℝ))≤2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<100*(p:ℝ))).mpr
    have hp1 : (1:ℝ)≤p := by exact_mod_cast hp
    linarith
  simpa only [div_eq_mul_inv,mul_assoc] using
    list_threshold (by linarith : 2≤σ) (by linarith : 100000≤g) ha ha2 hN hJ

theorem strong_exception_scale {σ P N D p : ℝ} (hp : 0<p)
    (hN : exp (2*σ-4*P)/2≤N)
    (hD : D*(1/(100*p))^2≤20000*exp (2*σ))
    (hpoly : 400000000*p^2≤exp P) :
    D≤N*exp (5*P) := by
  have hd : D≤200000000*p^2*exp (2*σ) := by
    apply (mul_le_mul_iff_left₀ (show 0<(1/(100*p))^2 by positivity)).mp
    calc
      _ ≤ 20000*exp (2*σ) := hD
      _ = (200000000*p^2*exp (2*σ))*(1/(100*p))^2 := by
        field_simp
        ring
  calc
    D ≤ 200000000*p^2*exp (2*σ) := hd
    _ ≤ (exp P/2)*exp (2*σ) := mul_le_mul_of_nonneg_right (by linarith only [hpoly]) (exp_pos _).le
    _ = (exp (2*σ-4*P)/2)*exp (5*P) := by
      rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
      congr 1
      rw [←exp_add,←exp_add]
      congr 1
      ring
    _ ≤ N*exp (5*P) := mul_le_mul_of_nonneg_right hN (exp_pos _).le

end
end SharpLogRamsey.SourceRadialTests

end

end OAI

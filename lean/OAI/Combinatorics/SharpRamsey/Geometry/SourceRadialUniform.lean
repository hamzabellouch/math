import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.SourceRadialTests

namespace OAI

section
namespace SharpLogRamsey.SourceRadialTests
open Filter Real
open scoped Topology
noncomputable section

theorem eventually_rich_tests (δ C : ℝ) (hδ : 0 < δ) :
    ∀ᶠ σ : ℝ in atTop, ∀ (g a : ℝ) (N Kp : ℕ),
    σ^δ/10000 ≤ g → g ≤ σ/2+C → exp (-g/20) ≤ a → a ≤ 2 →
    exp (3*σ/2+g)/2 ≤ (N:ℝ) → (N:ℝ) ≤ exp (3*σ/2+g) →
    (Kp:ℝ) ≤ 2*exp (σ+17*g/15) →
    let M := ⌈a*(N:ℝ)/exp σ⌉₊
    4 ≤ M ∧ M ≤ N ∧
    198*sqrt ((N:ℝ)/(M:ℝ)) < (M:ℝ) ∧
    33*sqrt ((N:ℝ)/(M:ℝ)) < exp σ ∧
    (N:ℝ)^2*exp (-5*sqrt ((N:ℝ)/(M:ℝ))) < 1/2 ∧
    8*Kp ≤ M^2 := by
  have hgt : Tendsto (fun σ : ℝ => σ^δ/10000) atTop atTop := by
    simpa only [div_eq_mul_inv,mul_comm] using
      (tendsto_rpow_atTop hδ).const_mul_atTop (by norm_num : (0:ℝ) < 10000⁻¹)
  have hp := ScaleSelection.eventually_polynomial_le_exp_rpow 3 4 1 1 (by norm_num) (by norm_num)
  filter_upwards [hgt.eventually_ge_atTop 100000,hp,
    eventually_ge_atTop (2:ℝ),eventually_ge_atTop (2000*exp (C/20)),
    eventually_ge_atTop (2*C+2)] with σ hg hp hσ hc hd g a N Kp hgl hgu hal hau hNl hNu hK
  dsimp only
  let M := ⌈a*(N:ℝ)/exp σ⌉₊
  have hg0 : 0 ≤ g := by linarith
  have hg' : 100000 ≤ g := hg.trans hgl
  have hb := threshold_bounds hσ hg0 hal hau hNl
  dsimp only at hb
  change exp (σ/2+19*g/20)/2 ≤ (M:ℝ) ∧ _ at hb
  have hM4 : 4 ≤ M := by
    have he := add_one_le_exp (σ/2+19*g/20)
    have hh : (4:ℝ) ≤ M := by linarith [hb.1]
    exact_mod_cast hh
  have hMN : M ≤ N := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ (exp_pos _)).mpr
    have hq : a ≤ exp σ := hau.trans (by linarith [add_one_le_exp σ])
    have hh := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg N : (0:ℝ) ≤ N)
    simpa only [mul_comm] using hh
  have hh := rich_tests hg' hb.1 hb.2.2.2 (Nat.cast_nonneg N) hK
  have hchar := characteristic_test hc hgu hb.2.2.2
  have hp' : 3*σ^4 ≤ exp σ := by simpa only [Real.rpow_ofNat,Real.rpow_one,one_mul] using hp
  have hfail := failure_test hσ hgu (Nat.cast_nonneg N) hNu hb.2.2.1 hp'
    (show 4*σ+2*C-5*σ^2 ≤ -2 by nlinarith [sq_nonneg (σ-1)])
  refine ⟨hM4,hMN,hh.1,hchar,hfail,?_⟩
  exact_mod_cast hh.2

theorem list_threshold {σ g a : ℝ} {N J : ℕ}
    (hσ : 2 ≤ σ) (hg : 100000 ≤ g)
    (ha : exp (-g/20) ≤ a) (ha2 : a ≤ 2)
    (hN : exp (3*σ/2+g)/2 ≤ (N:ℝ))
    (hJ : (J:ℝ) ≤ exp (σ/2-2*g/15)) :
    2*J ≤ ⌈a*(N:ℝ)/exp σ⌉₊ := by
  have hm := (threshold_bounds hσ (by linarith) ha ha2 hN).1
  have he : exp (σ/2+19*g/20)=exp (σ/2-2*g/15)*exp (13*g/12) := by
    rw [←exp_add]; congr 1; ring
  have hc : 4 ≤ exp (13*g/12) := by linarith [add_one_le_exp (13*g/12)]
  have hh := mul_le_mul_of_nonneg_left hc (exp_pos (σ/2-2*g/15)).le
  rw [he] at hm
  have hh' : 2*(J:ℝ) ≤ (⌈a*(N:ℝ)/exp σ⌉₊:ℝ) := by nlinarith only [hJ,hh,hm]
  exact_mod_cast hh'

end
end SharpLogRamsey.SourceRadialTests

end

end OAI

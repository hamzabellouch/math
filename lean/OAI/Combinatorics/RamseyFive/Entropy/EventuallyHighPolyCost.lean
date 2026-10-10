import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.HighPolyConstant

namespace OAI

noncomputable section
namespace SharpRamseyFive.ScoreGeometry
open Filter ParameterHierarchy
open scoped Topology

theorem eventually_high_poly_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (k c : ℝ) (hk : 0≤k) (hc : 0≤c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R p a : ℝ,Range η σ D R →
      0≤p → p≤k*σ → 0≤a → a≤c*σ*Real.exp (P η σ D R/50) →
      Real.exp (P η σ D R/50)+2*(p+1)*highBudgetPoly a p (P η σ D R)≤
        Real.exp (P η σ D R/5) := by
  let C := highPolyConstant k c
  have hC : 0<C := highPolyConstant_pos hk hc
  have hK : 0<1+2*(k+1)*C := by positivity
  have hab := eventually_power_absorption hη hη' (1+2*(k+1)*C) 206 (1/10)
    hK (by norm_num) (by norm_num)
  have hs := eventually_hierarchy hη hη' 0 1 0 (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hab,hs] with σ hσ hab hs
  intro D R p a hr hp hphi ha hahi
  have hpar := finite_bounds hη hη' hσ hr
  have hP : 0≤P η σ D R := (Real.rpow_nonneg (by linarith) _).trans hpar.2.2.2.2.2.1
  have hPhi : P η σ D R≤σ := by
    have hh := hs D R 0 0 hr (by simp) (Real.rpow_nonneg (by linarith) _)
    simpa only [one_mul] using hh.2.1
  have hpol := highBudgetPoly_bound hσ (Real.one_le_exp_iff.mpr (by positivity : 0≤P η σ D R/50))
    hp hphi hP hPhi ha hahi hk hc
  have hcoef : 1+2*(p+1)*C*σ^(205:ℕ)≤(1+2*(k+1)*C)*σ^(206:ℕ) := by
    have hh : p+1≤(k+1)*σ := by nlinarith
    have h1 : 1≤σ^(206:ℕ) := one_le_pow₀ hσ
    calc
      _ ≤ σ^(206:ℕ)+2*((k+1)*σ)*C*σ^(205:ℕ) := by gcongr
      _ = _ := by rw [show σ^(206:ℕ)=σ^205*σ from pow_succ σ 205]; ring
  have hh : (1+2*(k+1)*C)*σ^(206:ℕ)≤Real.exp (P η σ D R/10) := by
    have ht := hab D R hr
    rw [show σ^(206:ℝ)=σ^(206:ℕ) from Real.rpow_natCast σ 206] at ht
    simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm (10⁻¹:ℝ)] using ht
  calc
    _ ≤ Real.exp (P η σ D R/50)+2*(p+1)*(C*σ^(205:ℕ)*Real.exp (P η σ D R/50)) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hpol (by positivity))
    _ = (1+2*(p+1)*C*σ^(205:ℕ))*Real.exp (P η σ D R/50) := by ring
    _ ≤ Real.exp (P η σ D R/10)*Real.exp (P η σ D R/50) :=
      mul_le_mul_of_nonneg_right (hcoef.trans hh) (Real.exp_nonneg _)
    _ = Real.exp (P η σ D R/10+P η σ D R/50) := (Real.exp_add ..).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem eventually_high_pair_cost {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (k c : ℝ) (hk : 0≤k) (hc : 0≤c) :
    ∀ᶠ σ : ℝ in atTop,∀ D R p a : ℝ,Range η σ D R →
      0≤p → p≤k*σ → 0≤a → a≤c*σ*Real.exp (P η σ D R/50) →
      400+a*(100*p)^200≤Real.exp (P η σ D R/10) ∧
      p^2≤Real.exp (P η σ D R/10) := by
  have hC : 0<400+c*(100*k)^(200:ℕ) := by
    exact add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg hc (pow_nonneg (by positivity) _))
  have hab := eventually_power_absorption hη hη' (400+c*(100*k)^(200:ℕ)) 201 (1/20)
    hC (by norm_num) (by norm_num)
  have hpabs := eventually_power_absorption hη hη' (1+k^2) 2 (1/10)
    (by positivity) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),hab,hpabs] with σ hσ hab hpabs
  intro D R p a hr hp hphi ha hahi
  have hσ0 : 0≤σ := by linarith
  have hP : 0≤P η σ D R := (Real.rpow_nonneg hσ0 _).trans
    (finite_bounds hη hη' hσ hr).2.2.2.2.2.1
  have hE : 1≤Real.exp (P η σ D R/50) := Real.one_le_exp_iff.mpr (by positivity)
  constructor
  · have hpw : (100*p)^(200:ℕ)≤((100*k)*σ)^200 :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) _
    have h1 : 1≤σ^(201:ℕ)*Real.exp (P η σ D R/50) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hσ) hE
    have hh : (400+c*(100*k)^(200:ℕ))*σ^(201:ℕ)≤Real.exp (P η σ D R/20) := by
      have ht := hab D R hr
      rw [show σ^(201:ℝ)=σ^(201:ℕ) from Real.rpow_natCast σ 201] at ht
      simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm (20⁻¹:ℝ)] using ht
    calc
      _ ≤ 400*(σ^(201:ℕ)*Real.exp (P η σ D R/50))+
          (c*σ*Real.exp (P η σ D R/50))*((100*k)*σ)^200 :=
        add_le_add (by linarith) (mul_le_mul hahi hpw (pow_nonneg (by positivity) _) (by positivity))
      _ = ((400+c*(100*k)^(200:ℕ))*σ^(201:ℕ))*Real.exp (P η σ D R/50) := by ring
      _ ≤ Real.exp (P η σ D R/20)*Real.exp (P η σ D R/50) :=
        mul_le_mul_of_nonneg_right hh (Real.exp_nonneg _)
      _ = Real.exp (P η σ D R/20+P η σ D R/50) := (Real.exp_add ..).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hh := hpabs D R hr
    rw [show σ^(2:ℝ)=σ^(2:ℕ) from Real.rpow_natCast σ 2] at hh
    calc
      _ ≤ (k*σ)^2 := pow_le_pow_left₀ hp hphi _
      _ ≤ (1+k^2)*σ^2 := by nlinarith [sq_nonneg σ]
      _ ≤ _ := by simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm (10⁻¹:ℝ)] using hh

end SharpRamseyFive.ScoreGeometry

end

end OAI

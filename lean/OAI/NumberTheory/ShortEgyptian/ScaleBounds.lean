import OAI.NumberTheory.ShortEgyptian.ScaleGeometry

namespace OAI

namespace ShortEgyptian

@[instance_reducible] noncomputable def scaleFinDecidableEq (S : ℝ) : DecidableEq (Fin (scaleM S)) := Classical.decEq _
attribute [local instance] scaleFinDecidableEq

open Filter Topology

lemma eventually_scaleM_large (A : ℝ) :
    ∀ᶠ S : ℝ in atTop, A*Real.log S ≤ (scaleM S:ℝ) := by
  filter_upwards [eventually_log_pow_le (2*(max A 0+2)) 2 (by norm_num : (0:ℝ)<1),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with S h hL
  rw [Real.rpow_one] at h
  have hA : 0 ≤ max A 0 := le_max_right _ _
  have hAA : A ≤ max A 0 := le_max_left _ _
  have hL0 : 0 < Real.log S := by linarith
  have hbig : 4*Real.log S ≤ S := by nlinarith [sq_nonneg (Real.log S),mul_nonneg hA (sq_nonneg (1+Real.log S))]
  have hm := (scaleM_bounds S hL hbig).1
  apply le_trans _ hm
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*Real.log S)).mpr
  have hh : 2*(max A 0)*(Real.log S)^2 ≤ S := by nlinarith [mul_nonneg hA hL0.le]
  nlinarith [mul_le_mul_of_nonneg_right hAA (sq_nonneg (Real.log S))]

lemma eventually_depth_tail :
    ∀ᶠ S : ℝ in atTop,
      (depth S:ℝ)*Real.exp (-(1/250:ℝ)*scaleM S) < 1/2 := by
  let K : ℝ := 3*(dimX:ℝ)*10000
  have hK : 0 < K := by norm_num [K,dimX,dimM]
  filter_upwards [eventually_scaleM_large 500,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_log_pow_le 4 1 (by norm_num : (0:ℝ)<1),eventually_ge_atTop (4*K),
    eventually_gt_atTop (0:ℝ)] with S hm hL hbig hSK hS
  rw [Real.rpow_one,pow_one] at hbig
  have hb : 4*Real.log S ≤ S := by linarith
  have hmb := scaleM_bounds S hL hb
  have hd := depth_bound S hS hL hmb.1 hmb.2.2
  have hE : Real.exp (-(1/250:ℝ)*scaleM S) ≤ 1/S^2 := by
    calc
      _ ≤ Real.exp (-(2*Real.log S)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg,two_mul,Real.exp_add,Real.exp_log hS]; simp [pow_two]
  have hLS : Real.log S ≤ S := by have hh := Real.log_le_sub_one_of_pos hS; linarith
  calc
    _ ≤ (K*S)*(1/S^2) := mul_le_mul (hd.trans (mul_le_mul_of_nonneg_left hLS hK.le)) hE
      (Real.exp_nonneg _) (by positivity)
    _ = K/S := by field_simp
    _ ≤ 1/4 := (div_le_iff₀ hS).mpr (by linarith)
    _ < _ := by norm_num

structure ListScale (S : ℝ) : Prop where
  two_le : 2 ≤ S
  log_large : 100 ≤ Real.log S
  log_bound : 100001*Real.log S ≤ S
  m_large : 1000000*Real.log S ≤ (scaleM S:ℝ)
  reciprocal_power : (reciprocalPower (3*dimC):ℝ) ≤ Real.log S
  reciprocal_const : (reciprocalConstantNat (3*dimC):ℝ)*32^reciprocalPower (3*dimC) ≤ Real.exp (S/4)
  depth_tail : (depth S:ℝ)*Real.exp (-(1/250:ℝ)*scaleM S) < 1/2

lemma eventually_ListScale : ∀ᶠ S : ℝ in atTop, ListScale S := by
  let A : ℝ := (reciprocalConstantNat (3*dimC):ℝ)*32^reciprocalPower (3*dimC)
  have hA : 0 < A := mul_pos (by exact_mod_cast reciprocalConstant_pos (3*dimC)) (by positivity)
  filter_upwards [eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 100,
    eventually_log_pow_le 100001 1 (by norm_num : (0:ℝ)<1),eventually_scaleM_large 1000000,
    Real.tendsto_log_atTop.eventually_ge_atTop (reciprocalPower (3*dimC):ℝ),
    eventually_ge_atTop (4*Real.log A),eventually_depth_tail]
    with S hS hlog hbig hm hP hA' hd
  rw [Real.rpow_one,pow_one] at hbig
  refine ⟨hS,hlog,by linarith,hm,hP,?_,hd⟩
  exact (Real.log_le_iff_le_exp hA).mp (by linarith)

lemma ListScale.log_one {S : ℝ} (h : ListScale S) : 1 ≤ Real.log S := by linarith [h.log_large]
lemma ListScale.S_pos {S : ℝ} (h : ListScale S) : 0 < S := by linarith [h.two_le]
lemma ListScale.m_bounds {S : ℝ} (h : ListScale S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧ (scaleM S:ℝ) ≤ S :=
  scaleM_bounds S h.log_one (by linarith [h.log_bound,h.log_large])
lemma ListScale.m_pos {S : ℝ} (h : ListScale S) : 0 < scaleM S := by
  have hh : 0 < (scaleM S:ℝ) := by linarith [h.m_large,h.log_large]
  exact_mod_cast hh
lemma ListScale.m_hundred {S : ℝ} (h : ListScale S) : 100 ≤ (scaleM S:ℝ) := by linarith [h.m_large,h.log_large]
lemma ListScale.m_fourier {S : ℝ} (h : ListScale S) : 100000*Real.log S ≤ (99/100:ℝ)*scaleM S := by
  linarith [h.m_large,h.log_large]
lemma exp_neg_small (v : ℝ) (hv : 2560000 ≤ v) : Real.exp (-(1/10000:ℝ)*v) ≤ 1/256 := by
  have hlog : Real.log 256 ≤ 255 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<256)
    norm_num at hh
    exact hh
  apply (Real.le_log_iff_exp_le (by norm_num : (0:ℝ)<1/256)).mp
  rw [Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub]
  linarith
lemma ListScale.rho_small {S : ℝ} (h : ListScale S) : scaleRho S ≤ 1/256 :=
  exp_neg_small _ (by linarith [h.m_large,h.log_large])
lemma ListScale.terminal_small {S : ℝ} (h : ListScale S) (u : ℕ)
    (hu : 100000*Real.log S ≤ Real.log u) : Real.exp (-(1/10000:ℝ)*Real.log u) ≤ 1/256 :=
  exp_neg_small _ (by linarith [h.log_large])

end ShortEgyptian

end OAI

import OAI.Probability.PosteriorReplicas.Information.ReplicaLoss

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Matrix InnerProductSpace Filter Metric
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace PosteriorReplicas

lemma gaussianMomentConstant_log_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log (gaussianMomentConstant k).toReal ≤ -(k:ℝ)/2*Real.log k + 4*k := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have he : (gaussianMomentConstant k).toReal = (Real.sqrt k)⁻¹^k *
      (1+Real.exp ((k:ℝ)/2)*2^(k+1)) := by
    unfold gaussianMomentConstant
    rw [ENNReal.toReal_mul,ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_mul]
    simp only [ENNReal.toReal_one,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (Real.sqrt (k:ℝ))⁻¹^k),
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [he,Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_inv,
    Real.log_sqrt hkp.le]
  have hone : (1:ℝ) ≤ Real.exp ((k:ℝ)/2)*2^(k+1) :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp_iff.mpr (by positivity)) (one_le_pow₀ (by norm_num))
  have hlog := Real.log_le_log (by positivity : 0 < 1+Real.exp ((k:ℝ)/2)*2^(k+1))
    (show 1+Real.exp ((k:ℝ)/2)*2^(k+1) ≤ 2*(Real.exp ((k:ℝ)/2)*2^(k+1)) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_mul (Real.exp_pos _).ne' (by positivity),
    Real.log_exp,Real.log_pow] at hlog
  have hl2 : Real.log 2 ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
  push_cast at hlog
  nlinarith [mul_le_mul_of_nonneg_left hl2 (show 0 ≤ (k:ℝ)+2 by positivity)]

lemma wishartMoment_log_le {ℓ m k : ℕ} (hk : 1 ≤ k) (hkm : k+m ≤ ℓ) :
    Real.log (wishartMoment ℓ m k).toReal ≤ (m:ℝ)*(-(k:ℝ)/2*Real.log k + 4*k) := by
  have hp := ENNReal.toReal_pos (wishartMoment_pos (by omega : m ≤ ℓ)).ne' (wishartMoment_ne_top hk hkm)
  have ht := ENNReal.pow_ne_top (gaussianMomentConstant_ne_top k) (n := m)
  have hb := (ENNReal.toReal_le_toReal (wishartMoment_ne_top hk hkm) ht).mpr (wishartMoment_bound hk hkm)
  have hlog := Real.log_le_log hp hb
  rw [ENNReal.toReal_pow,Real.log_pow] at hlog
  exact hlog.trans (mul_le_mul_of_nonneg_left (gaussianMomentConstant_log_le hk) (Nat.cast_nonneg m))

lemma label_unitBall_log_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log (volume {y : Labels k | labelNorm y ≤ 1}).toReal ≤
      (k:ℝ)/2*(Real.log (2*Real.pi)+1-Real.log k) := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have h := gaussian_density_ball_lower (E := Vec k) (Real.sqrt_nonneg (k:ℝ))
  rw [← label_closedBall_volume, label_closedBall_scale (Real.sqrt_nonneg (k:ℝ))] at h
  simp only [finrank_euclideanSpace_fin,Real.sq_sqrt hkp.le] at h
  have hr := ENNReal.toReal_mono (by simp : (1:ℝ≥0∞) ≠ ∞) h
  simp only [ENNReal.toReal_mul,ENNReal.toReal_one,ENNReal.toReal_ofReal (by positivity :
    0 ≤ (2*Real.pi)^(-(k:ℝ)/2)*Real.exp (-(k:ℝ)/2)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (Real.sqrt (k:ℝ))^k)] at hr
  have hv : 0 < (volume {y : Labels k | labelNorm y ≤ 1}).toReal :=
    ENNReal.toReal_pos (label_unitBall_pos k).ne' (label_unitBall_ne_top k)
  have hp : 0 < (2*Real.pi)^(-(k:ℝ)/2)*Real.exp (-(k:ℝ)/2) := by positivity
  have hh := Real.log_le_log (mul_pos hp (mul_pos (pow_pos (Real.sqrt_pos.mpr hkp) _) hv)) hr
  rw [Real.log_one,Real.log_mul hp.ne' (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by positivity),Real.log_exp,Real.log_mul (by positivity) hv.ne',Real.log_pow,
    Real.log_sqrt hkp.le] at hh
  linarith

lemma binMeanBound_log_le {k : ℕ} (hk : 1 ≤ k) (J : ℕ) :
    Real.log (binMeanBound k J) ≤ (k:ℝ)/2*(Real.log (2*Real.pi)+1-Real.log k)+
      Real.log ((J:ℝ)+2)+(k:ℝ)*Real.log 2 := by
  have hv : 0 < (volume {y : Labels k | labelNorm y ≤ 1}).toReal :=
    ENNReal.toReal_pos (label_unitBall_pos k).ne' (label_unitBall_ne_top k)
  rw [binMeanBound,Real.log_mul hv.ne' (by positivity)]
  have hb : (2+(J:ℝ)*2^k) ≤ ((J:ℝ)+2)*2^k := by
    have hp : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    nlinarith
  have hh := Real.log_le_log (by positivity : (0:ℝ)<2+(J:ℝ)*2^k) hb
  rw [Real.log_mul (by positivity) (by positivity),Real.log_pow] at hh
  linarith [label_unitBall_log_le hk]

lemma scaled_dimension_log_le {n k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha : 0 < a)
    (hn : (n:ℝ)+1 ≤ a*k) : Real.log ((n:ℝ)+1) ≤ Real.log k + a := by
  have hkp : 0 < (k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have h := Real.log_le_log (by positivity : (0:ℝ)<(n:ℝ)+1) hn
  rw [Real.log_mul ha.ne' hkp.ne'] at h
  linarith [Real.log_le_self ha.le]

lemma comparisonCost_le {d ℓ k m : ℕ} (hk : 1 ≤ k) (hkm : k+m≤ℓ)
    (hdk : d ≤ 32*k) (hℓk : ℓ ≤ 16*k) (J : ℕ) :
    comparisonCost d ℓ k m J ≤ (m:ℝ)*((40+Real.pi)*(k:ℝ)+Real.log ((J:ℝ)+2)) := by
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hdn : (d:ℝ) ≤ 32*k := by exact_mod_cast hdk
  have hℓn : (ℓ:ℝ) ≤ 16*k := by exact_mod_cast hℓk
  have hl := scaled_dimension_log_le hk (by norm_num : (0:ℝ)<17) (by linarith : (ℓ:ℝ)+1≤17*k)
  have hd := scaled_dimension_log_le hk (by norm_num : (0:ℝ)<33) (by linarith : (d:ℝ)+1≤33*k)
  have hZ := wishartMoment_log_le hk hkm
  have hB := binMeanBound_log_le hk J
  have hL2 : Real.log 2 ≤ 1 := by simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hLp : Real.log (2*Real.pi) ≤ 2*Real.pi := Real.log_le_self (by positivity)
  have hk0 : 0 ≤ (k:ℝ) := by positivity
  have hm0 : 0 ≤ (m:ℝ) := by positivity
  have hl' := mul_le_mul_of_nonneg_left hl (show 0 ≤ (k:ℝ)*(m:ℝ)/2 by positivity)
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ (m:ℝ)*(k:ℝ)/2 by positivity)
  have hB' := mul_le_mul_of_nonneg_left hB hm0
  have hL2' := mul_le_mul_of_nonneg_left hL2 (show 0 ≤ (m:ℝ)*(k:ℝ) by positivity)
  have hLp' := mul_le_mul_of_nonneg_left hLp (show 0 ≤ (m:ℝ)*(k:ℝ)/2 by positivity)
  unfold comparisonCost
  nlinarith [mul_nonneg hm0 hk0]

end PosteriorReplicas
end

end OAI

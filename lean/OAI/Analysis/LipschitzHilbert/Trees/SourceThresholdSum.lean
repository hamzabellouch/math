import OAI.Analysis.LipschitzHilbert.Trees.SourceThresholdWeights
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace OAI

/-! Uniform summation over any finite family of dyadic density thresholds. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

def ordinaryThresholdRatio : ℝ := (2:ℝ)^(-(1/5:ℝ))

def ordinaryThresholdEnvelope (k : ℤ) : ℝ := ordinaryThresholdRatio^k.natAbs

theorem ordinaryThresholdRatio_pos : 0<ordinaryThresholdRatio :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem ordinaryThresholdRatio_lt_one : ordinaryThresholdRatio<1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem ordinaryThresholdEnvelope_summable : Summable ordinaryThresholdEnvelope := by
  have h := summable_geometric_of_abs_lt_one
    (show |ordinaryThresholdRatio|<1 by
      rw [abs_of_pos ordinaryThresholdRatio_pos]
      exact ordinaryThresholdRatio_lt_one)
  apply Summable.of_nat_of_neg
  · simpa only [ordinaryThresholdEnvelope,Int.natAbs_natCast] using h
  · simpa only [ordinaryThresholdEnvelope,Int.natAbs_neg,Int.natAbs_natCast] using h

theorem ordinaryThresholdEnvelope_tsum :
    (∑' k : ℤ, ordinaryThresholdEnvelope k)≤2/(1-ordinaryThresholdRatio) := by
  have h := summable_geometric_of_abs_lt_one
    (show |ordinaryThresholdRatio|<1 by
      rw [abs_of_pos ordinaryThresholdRatio_pos]
      exact ordinaryThresholdRatio_lt_one)
  have hnat : Summable (fun n : ℕ => ordinaryThresholdEnvelope n) := by
    simpa only [ordinaryThresholdEnvelope,Int.natAbs_natCast] using h
  have hneg : Summable (fun n : ℕ => ordinaryThresholdEnvelope (-n)) := by
    simpa only [ordinaryThresholdEnvelope,Int.natAbs_neg,Int.natAbs_natCast] using h
  rw [hnat.tsum_of_nat_of_neg hneg]
  simp only [ordinaryThresholdEnvelope,Int.natAbs_neg,Int.natAbs_natCast,Int.natAbs_zero,pow_zero]
  rw [tsum_geometric_of_abs_lt_one
    (show |ordinaryThresholdRatio|<1 by
      rw [abs_of_pos ordinaryThresholdRatio_pos]
      exact ordinaryThresholdRatio_lt_one)]
  rw [div_eq_mul_inv]
  linarith

theorem ordinaryThresholdWeight_dyadic {gamma : ℝ} (hgamma : 0<gamma) (hgammaOne : gamma≤1)
    (k : ℤ) :
    ordinaryThresholdWeight gamma ((2:ℝ)^k)≤4*gamma^(1/4:ℝ)*ordinaryThresholdEnvelope k := by
  cases k with
  | ofNat n =>
    have heta : (1:ℝ)≤2^n := one_le_pow₀ (by norm_num)
    have h := ordinaryThresholdWeight_large hgamma hgammaOne heta
    rw [←Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)] at h
    change ordinaryThresholdWeight gamma ((2:ℝ)^n)≤
      4*gamma^(1/4:ℝ)*ordinaryThresholdRatio^n
    exact h.trans (by
      have hg := Real.rpow_nonneg hgamma.le (1/4:ℝ)
      have hr := pow_nonneg ordinaryThresholdRatio_pos.le n
      change 2*gamma^(1/4:ℝ)*ordinaryThresholdRatio^n≤_
      nlinarith)
  | negSucc n =>
    have he : (2:ℝ)^(Int.negSucc n)=((2:ℝ)^(n+1))⁻¹ := by
      rw [zpow_negSucc]
    have hetaPos : (0:ℝ)<((2:ℝ)^(n+1))⁻¹ := by positivity
    have hetaOne : ((2:ℝ)^(n+1))⁻¹≤1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have h := ordinaryThresholdWeight_small hgamma hetaPos hetaOne
    have hpower : (((2:ℝ)^(n+1))⁻¹)^(1/5:ℝ)=ordinaryThresholdRatio^(n+1) := by
      rw [←Real.rpow_neg_eq_inv_rpow,←Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2)]
      rfl
    rw [hpower] at h
    simpa only [he,ordinaryThresholdEnvelope,Int.natAbs_negSucc] using h

theorem ordinaryThreshold_finite_sum {gamma : ℝ} (hgamma : 0<gamma) (hgammaOne : gamma≤1)
    (S : Finset ℤ) :
    (∑ k∈S, ordinaryThresholdWeight gamma ((2:ℝ)^k))≤
      (8/(1-ordinaryThresholdRatio))*gamma^(1/4:ℝ) := by
  have hg : 0≤4*gamma^(1/4:ℝ) := by positivity
  calc
    _ ≤ ∑ k∈S, (4*gamma^(1/4:ℝ))*ordinaryThresholdEnvelope k :=
      Finset.sum_le_sum (fun k _ => ordinaryThresholdWeight_dyadic hgamma hgammaOne k)
    _ = (4*gamma^(1/4:ℝ))*∑ k∈S, ordinaryThresholdEnvelope k := by rw [Finset.mul_sum]
    _ ≤ (4*gamma^(1/4:ℝ))*(∑' k : ℤ, ordinaryThresholdEnvelope k) :=
      mul_le_mul_of_nonneg_left (ordinaryThresholdEnvelope_summable.sum_le_tsum S
        (fun k _ => pow_nonneg ordinaryThresholdRatio_pos.le k.natAbs)) hg
    _ ≤ (4*gamma^(1/4:ℝ))*(2/(1-ordinaryThresholdRatio)) :=
      mul_le_mul_of_nonneg_left ordinaryThresholdEnvelope_tsum hg
    _ = _ := by ring

theorem ordinaryThresholdWeight_scale_upper {gamma eta C : ℝ}
    (heta : 0<eta) (hC : 1≤C) :
    ordinaryThresholdWeight gamma eta≤C*ordinaryThresholdWeight (gamma/C) eta := by
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hm : min gamma (2*eta)≤C*min (gamma/C) (2*eta) := by
    by_cases h : gamma/C≤2*eta
    · rw [min_eq_left h,mul_div_cancel₀ _ hCp.ne']
      exact min_le_left _ _
    · rw [min_eq_right (le_of_not_ge h)]
      exact (min_le_right _ _).trans (le_mul_of_one_le_left (by positivity) hC)
  have hp : 0≤Real.sqrt eta*(1+eta^(-(1/20:ℝ)))/eta := by positivity
  have h := mul_le_mul_of_nonneg_right hm hp
  simpa only [ordinaryThresholdWeight,mul_div_assoc,mul_assoc] using h

theorem ordinaryThreshold_finite_sum_bounded {gamma C : ℝ} (hgamma : 0<gamma)
    (hC : 1≤C) (hgammaC : gamma≤C) (S : Finset ℤ) :
    (∑ k∈S, ordinaryThresholdWeight gamma ((2:ℝ)^k))≤
      (8*C/(1-ordinaryThresholdRatio))*gamma^(1/4:ℝ) := by
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hgammaDiv : 0<gamma/C := div_pos hgamma hCp
  have hsmall : gamma/C≤1 := (div_le_one hCp).mpr hgammaC
  have hg : gamma/C≤gamma := div_le_self hgamma.le hC
  have hpow := Real.rpow_le_rpow hgammaDiv.le hg (by norm_num : (0:ℝ)≤1/4)
  have hden : 0<1-ordinaryThresholdRatio := sub_pos.mpr ordinaryThresholdRatio_lt_one
  calc
    _ ≤ ∑ k∈S, C*ordinaryThresholdWeight (gamma/C) ((2:ℝ)^k) :=
      Finset.sum_le_sum (fun k _ => ordinaryThresholdWeight_scale_upper (zpow_pos (by norm_num) k) hC)
    _ = C*(∑ k∈S, ordinaryThresholdWeight (gamma/C) ((2:ℝ)^k)) := by rw [Finset.mul_sum]
    _ ≤ C*((8/(1-ordinaryThresholdRatio))*(gamma/C)^(1/4:ℝ)) :=
      mul_le_mul_of_nonneg_left (ordinaryThreshold_finite_sum hgammaDiv hsmall S) hCp.le
    _ ≤ C*((8/(1-ordinaryThresholdRatio))*gamma^(1/4:ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (by positivity)) hCp.le
    _ = _ := by ring

end LipschitzHilbert

end

end OAI

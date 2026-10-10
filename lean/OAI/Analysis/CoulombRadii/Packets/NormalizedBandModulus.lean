import Mathlib
import OAI.Analysis.CoulombRadii.LimitTheory.UniformGroundStateCountControl
import OAI.Analysis.CoulombRadii.Packets.AtomicMesh
import OAI.Analysis.CoulombRadii.RandomFields.ObservationSmallScale
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma norm_pow_difference_bound {R : ℝ} (hR : 0 ≤ R) {y z : Position}
    (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) (k : ℕ) :
    |‖z‖^k-‖y‖^k| ≤ ‖z-y‖*k*R^(k-1) := by
  have H := abs_pow_sub_pow_le (a:=‖z‖) (b:=‖y‖) (n:=k)
  simp only [abs_of_nonneg (norm_nonneg _)] at H
  apply H.trans
  exact mul_le_mul_of_nonneg
    (mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le z y) (Nat.cast_nonneg _))
    (pow_le_pow_left₀ (by positivity) (max_le hz hy) _)
    (by positivity) (pow_nonneg hR _)

lemma normalized_density_difference {ρ : Position → ℝ} {r L P Q : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    {y z : Position} (_ : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (hz0 : r ≤ ‖z‖) (hz1 : ‖z‖ ≤ 4*L*r)
    (hρ0 : 0 ≤ ρ y) (hρ : ρ y ≤ P/r^6)
    (hlip : |ρ z-ρ y| ≤ (Q/r^7)*‖z-y‖) :
    |‖z‖^6*ρ z-‖y‖^6*ρ y| ≤
      ((4*L)^6*Q+6*(4*L)^5*P)*(‖z-y‖/r) := by
  have he : ‖z‖^6*ρ z-‖y‖^6*ρ y=‖z‖^6*(ρ z-ρ y)+(‖z‖^6-‖y‖^6)*ρ y := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg (norm_nonneg z) 6),abs_of_nonneg hρ0]
  have hdist := norm_pow_difference_bound (by positivity : 0 ≤ 4*L*r) hy1 hz1 6
  norm_num only [Nat.cast_ofNat,Nat.reduceSub] at hdist
  calc
    _ ≤ (4*L*r)^6*((Q/r^7)*‖z-y‖)+(‖z-y‖*6*(4*L*r)^5)*(P/r^6) :=
      add_le_add
        (mul_le_mul_of_nonneg (pow_le_pow_left₀ (hr.le.trans hz0) hz1 6) hlip
          (pow_nonneg (norm_nonneg z) 6)
          (mul_nonneg (div_nonneg hQ (pow_nonneg hr.le _)) (norm_nonneg _)))
        (mul_le_mul_of_nonneg hdist hρ (abs_nonneg _)
          (div_nonneg hP (pow_nonneg hr.le _)))
    _ = _ := by field_simp

lemma normalized_field_difference {F : Position → ℝ} {r L C M lam : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hC : 0 ≤ C) (hM : 0 ≤ M) (hlam : 1 ≤ lam)
    {y z : Position} (hy0 : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (_ : r ≤ ‖z‖) (hz1 : ‖z‖ ≤ 4*L*r)
    (hcap : ‖y‖^4*F y ≤ M)
    (hosc : |F z-F y| ≤ C*(‖z-y‖/r)*(lam/r^4+max (-F y) 0)) :
    |‖z‖^4*F z-‖y‖^4*F y| ≤
      ((4*L)^4*C+4*(4*L)^3*max M 1)*(‖z-y‖/r)*(lam+max (-(‖y‖^4*F y)) 0) := by
  let N := max (-(‖y‖^4*F y)) 0
  have hN : 0 ≤ N := le_max_right _ _
  have hyn : 0 < ‖y‖ := hr.trans_le hy0
  have hFy : F y ≤ M/r^4 := by
    calc
      _ ≤ M/‖y‖^4 := (le_div_iff₀ (pow_pos hyn 4)).mpr (by simpa only [mul_comm] using hcap)
      _ ≤ M/r^4 := div_le_div_of_nonneg_left hM (pow_pos hr 4) (pow_le_pow_left₀ hr.le hy0 4)
  have hneg : max (-F y) 0 ≤ N/r^4 := by
    apply (le_div_iff₀ (pow_pos hr 4)).mpr
    have he : N=‖y‖^4*max (-F y) 0 := by
      dsimp [N]
      rw [mul_max_of_nonneg _ _ (pow_nonneg (norm_nonneg y) 4),mul_zero,mul_neg]
    rw [he]
    calc
      max (-F y) 0 * r^4 = r^4 * max (-F y) 0 := mul_comm _ _
      _ ≤ ‖y‖^4 * max (-F y) 0 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr.le hy0 4) (le_max_right _ _)
  have habs : |F y| ≤ (M+N)/r^4 := by
    rw [abs_le]
    constructor
    · have H := (le_max_left (-F y) 0).trans hneg
      have hMN : N/r^4 ≤ (M+N)/r^4 := div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le 4)
      linarith
    · exact hFy.trans (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le 4))
  have hFdiff : |F z-F y| ≤ C*(‖z-y‖/r)*((lam+N)/r^4) := by
    apply hosc.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [add_div]
    gcongr
  have hdist := norm_pow_difference_bound (by positivity : 0 ≤ 4*L*r) hy1 hz1 4
  norm_num only [Nat.cast_ofNat,Nat.reduceSub] at hdist
  have hMN : M+N ≤ max M 1*(lam+N) := by
    have hm0 : 0 ≤ max M 1 := le_trans (by norm_num) (le_max_right _ _)
    have hm1 := le_max_right M (1:ℝ)
    have H := mul_le_mul_of_nonneg_left hlam hm0
    have HN := mul_le_mul_of_nonneg_right hm1 hN
    nlinarith [le_max_left M (1:ℝ)]
  have he : ‖z‖^4*F z-‖y‖^4*F y=‖z‖^4*(F z-F y)+(‖z‖^4-‖y‖^4)*F y := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_mul,abs_of_nonneg (pow_nonneg (norm_nonneg z) 4)]
  calc
    _ ≤ (4*L*r)^4*(C*(‖z-y‖/r)*((lam+N)/r^4))+
        (‖z-y‖*4*(4*L*r)^3)*((M+N)/r^4) :=
      add_le_add
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz1 4) hFdiff (abs_nonneg _) (by positivity))
        (mul_le_mul hdist habs (abs_nonneg _) (by positivity))
    _ ≤ (4*L*r)^4*(C*(‖z-y‖/r)*((lam+N)/r^4))+
        (‖z-y‖*4*(4*L*r)^3)*((max M 1*(lam+N))/r^4) := by gcongr
    _ = _ := by field_simp; ring
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
noncomputable section
namespace NeutralAtom

lemma mesh_width_ratio_formula {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    r/(c*(r/3)*(r/3)^packetExponent) =
      (3^(1+packetExponent)/c)*r^(-packetExponent) := by
  rw [Real.div_rpow hr.le (by norm_num : (0:ℝ) ≤ 3),
    Real.rpow_add (by norm_num : (0:ℝ) < 3),Real.rpow_one,
    Real.rpow_neg hr.le]
  field_simp

lemma mesh_width_power_tendsto {c : ℝ} (hc : 0 < c) (k : ℕ)
    (hk : (k:ℝ)*packetExponent < 1) :
    Tendsto (fun r : ℝ => r*(r/(c*(r/3)*(r/3)^packetExponent))^k) (𝓝[>] 0) (𝓝 0) := by
  have H := (tendsto_positive_rpow_zero (show 0 < 1-(k:ℝ)*packetExponent by linarith)).const_mul
    ((3^(1+packetExponent)/c)^k)
  simp only [mul_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr : 0 < r := hr
  rw [mesh_width_ratio_formula hc hr,mul_pow,←Real.rpow_natCast (r^(-packetExponent)) k,
    ←Real.rpow_mul hr.le]
  have he : 1-(k:ℝ)*packetExponent=1+(-packetExponent*(k:ℝ)) := by ring
  rw [he,Real.rpow_add hr,Real.rpow_one]
  ring

lemma mesh_normalized_density_bound {r L τ B D K : ℝ} {ρ : Position → ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hτ : 0 < τ) (hτr : τ ≤ r)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hK : 0 ≤ K)
    {y z : Position} (hy0 : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (hz0 : r ≤ ‖z‖) (hz1 : ‖z‖ ≤ 4*L*r) (hdist : ‖z-y‖ ≤ r^2)
    (hρ0 : 0 ≤ ρ y) (hρ : ρ y ≤ (B/τ^3)*(K/r^3))
    (hlip : |ρ z-ρ y| ≤ (D/τ^4)*‖z-y‖*(K/r^3)) :
    |‖z‖^6*ρ z-‖y‖^6*ρ y| ≤
      ((4*L)^6*(D*K)+6*(4*L)^5*(B*K))*(r*(r/τ)^4) := by
  have ht : 1 ≤ r/τ := (le_div_iff₀ hτ).mpr (by simpa using hτr)
  have hρ' : ρ y ≤ (B*K*(r/τ)^3)/r^6 := hρ.trans_eq (by field_simp)
  have hlip' : |ρ z-ρ y| ≤ ((D*K*(r/τ)^4)/r^7)*‖z-y‖ := hlip.trans_eq (by field_simp)
  have H := normalized_density_difference hr hL (by positivity : 0 ≤ B*K*(r/τ)^3)
    (by positivity : 0 ≤ D*K*(r/τ)^4) hy0 hy1 hz0 hz1 hρ0 hρ' hlip'
  have hpow : (r/τ)^3 ≤ (r/τ)^4 := pow_le_pow_right₀ ht (by omega)
  have hd : ‖z-y‖/r ≤ r := (div_le_iff₀ hr).mpr (by nlinarith)
  calc
    _ ≤ ((4*L)^6*(D*K*(r/τ)^4)+6*(4*L)^5*(B*K*(r/τ)^3))*(‖z-y‖/r) := H
    _ ≤ ((4*L)^6*(D*K*(r/τ)^4)+6*(4*L)^5*(B*K*(r/τ)^4))*r := by gcongr
    _ = _ := by ring

lemma inverse_count_ball_subset {c r₀ s r L : ℝ} {y : Position}
    (hc : 0 < c) (hr₀ : 0 < r₀) (hs : 0 < s) (hr : 0 < r) (hL : 1 ≤ L)
    (hr₀r : r₀ ≤ r) (hy0 : r ≤ ‖y‖) (hy1 : ‖y‖ ≤ 4*L*r)
    (hw : c*s^packetExponent ≤ 1/100) (ha : (Coulomb.atomicCellScale y)^(6/5:ℝ) ≤ Coulomb.atomicCellScale y)
    (he : Real.sqrt 3*r^(101/100:ℝ) ≤ r/12) :
    Metric.closedBall y (2*packetWidth c r₀ s y+2*(Coulomb.atomicCellScale y)^(6/5:ℝ)+
      2*(Real.sqrt 3*r^(101/100:ℝ))) ⊆
        {z : Position | r/4 ≤ ‖z‖ ∧ ‖z‖ ≤ 12*L*r} := by
  have hwidth : packetWidth c r₀ s y ≤ ‖y‖/100 := by
    have H := packetWidth_le c r₀ s hc.le hr₀ hs y
    rw [max_eq_left (hr₀r.trans hy0)] at H
    exact H.trans ((mul_le_mul_of_nonneg_right hw (norm_nonneg y)).trans_eq (by ring))
  have ha' : 2*(Coulomb.atomicCellScale y)^(6/5:ℝ) ≤ ‖y‖/100 := by
    dsimp [Coulomb.atomicCellScale] at ha ⊢
    linarith
  intro z hz
  have hdist : ‖z-y‖ ≤ 3*‖y‖/100+r/6 := by
    have H : ‖z-y‖ ≤ 2*packetWidth c r₀ s y+2*(Coulomb.atomicCellScale y)^(6/5:ℝ)+
        2*(Real.sqrt 3*r^(101/100:ℝ)) := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    linarith
  have hz' := norm_le_norm_add_norm_sub y z
  have hy' := norm_le_norm_add_norm_sub z y
  rw [norm_sub_rev y z] at hz'
  have hLr := mul_le_mul_of_nonneg_right hL hr.le
  constructor <;> nlinarith
end NeutralAtom
end

end

end OAI

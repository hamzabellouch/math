import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeWiener

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def averageCost (n : ℕ) (t r : ℝ) (y u : Point) (β : Noise) : ℝ :=
  (∑j : Fin n,legCost t r y u j β)/(n:ℝ)

lemma legCost_nonneg {n : ℕ} (j : Fin n) {t r : ℝ} (hr : 0≤r) (y u : Point) (β : Noise) :
    0≤legCost t r y u j β := by
  unfold legCost
  exact pow_nonneg (add_nonneg (by norm_num) (div_nonneg (norm_nonneg _) hr)) _
lemma liftedDiameter_continuous (a b : Time) : Continuous (liftedDiameter a b) := by
  apply Continuous.norm
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : EuclideanPath×(Time×Time) ↦ Real.sqrt (∑j,(p.1 j (intervalTime a b p.2.1)-p.1 j (intervalTime a b p.2.2))^2))
  have hi := intervalTime_continuous a b
  fun_prop

lemma legCost_continuous {n : ℕ} (j : Fin n) (t r : ℝ) (y u : Point) : Continuous (legCost t r y u j) := by
  have hζ : Continuous (fun β : Noise ↦ fun i : Fin 3 ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩) := by
    apply continuous_pi
    intro i
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : Noise×Time ↦ leg t y u p.1 (meshTime j p.2) i)
    have hl := leg_continuous t y u
    have hj := meshTime_continuous j
    fun_prop
  exact (continuous_const.add (((liftedDiameter_continuous 0 1).comp hζ).div_const r)).pow 3

lemma averageCost_lintegral {n : ℕ} (hn : 0<n) {t r C : ℝ} (ht : 0≤t) (hr : 0<r)
    (y u : Point) (hC : 0≤C) (hdis : ‖u-y‖≤C) (hdrift : C/(n:ℝ)≤r)
    (hscale : t/(n:ℝ)≤r^2) :
    ∫⁻β,ENNReal.ofReal (averageCost n t r y u β) ∂law≤ENNReal.ofReal bridgeMeanCost := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [averageCost,ENNReal.ofReal_div_of_pos (by exact_mod_cast hn : (0:ℝ)<n),
    ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ legCost_nonneg j hr.le y u _)]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const]
  rotate_left
  · exact Finset.measurable_sum _ (fun j _ ↦ (legCost_continuous j t r y u).measurable.ennreal_ofReal)
  rw [lintegral_finsetSum _ (fun j _ ↦ (legCost_continuous j t r y u).measurable.ennreal_ofReal)]
  simp_rw [←div_eq_mul_inv]
  calc
    _ ≤ (∑_j : Fin n,ENNReal.ofReal bridgeMeanCost)/ENNReal.ofReal (n:ℝ) := by
      exact ENNReal.div_le_div_right (Finset.sum_le_sum (fun j _ ↦ legCost_moment j ht hr y u hC hdis hdrift hscale)) _
    _ = _ := by simp [nsmul_eq_mul,div_eq_mul_inv,mul_comm,mul_assoc,ENNReal.mul_inv_cancel (by exact_mod_cast Nat.ne_of_gt hn : (n:ℝ≥0∞)≠0) (by simp : (n:ℝ≥0∞)≠⊤)]

lemma averageCost_tail {n : ℕ} (hn : 0<n) {t r C R : ℝ} (ht : 0≤t) (hr : 0<r) (hR : 0<R)
    (y u : Point) (hC : 0≤C) (hdis : ‖u-y‖≤C) (hdrift : C/(n:ℝ)≤r)
    (hscale : t/(n:ℝ)≤r^2) :
    law {β | R≤averageCost n t r y u β}≤ENNReal.ofReal bridgeMeanCost/ENNReal.ofReal R := by
  have hm : Measurable (fun β ↦ ENNReal.ofReal (averageCost n t r y u β)) := by
    unfold averageCost
    exact ((continuous_finsetSum _ (fun j _ ↦ legCost_continuous j t r y u)).div_const _).measurable.ennreal_ofReal
  have h := meas_ge_le_lintegral_div (μ:=law) hm.aemeasurable (ne_of_gt (ENNReal.ofReal_pos.mpr hR)) ENNReal.ofReal_ne_top
  have he : {β | ENNReal.ofReal R≤ENNReal.ofReal (averageCost n t r y u β)}={β | R≤averageCost n t r y u β} := by
    ext β
    exact ENNReal.ofReal_le_ofReal_iff (by unfold averageCost; exact div_nonneg (Finset.sum_nonneg (fun j _ ↦ legCost_nonneg j hr.le y u β)) (Nat.cast_nonneg _))
  rw [he] at h
  exact h.trans (ENNReal.div_le_div_right (averageCost_lintegral hn ht hr y u hC hdis hdrift hscale) _)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def fluctuationMoment (p : ℕ) : ℝ := (3^p*3*2^(p+1))*2^p*normPowerMean p
lemma fluctuationMoment_nonneg (p : ℕ) : 0≤ fluctuationMoment p := by
  unfold fluctuationMoment
  exact mul_nonneg (by positivity) (normPowerMean_nonneg p)

lemma incrementFluctuation_power_mean {t r : ℝ} (ht : 0≤ t) (hr : 0< r)
    (s u : Time) (hscale : t*(1-(s:ℝ))*(u:ℝ)≤ r^2) (p : ℕ) (hp : p≠0) :
    ∫β,(incrementFluctuation t r s u β)^p ∂law≤ fluctuationMoment p := by
  have hs : 0≤(1-(s:ℝ))*(u:ℝ) := mul_nonneg (sub_nonneg.mpr s.property.2) u.property.1
  have hroot : Real.sqrt (2*t)/r*Real.sqrt ((1-(s:ℝ))*(u:ℝ))≤2 := by
    rw [div_mul_eq_mul_div,←Real.sqrt_mul (by positivity)]
    apply (div_le_iff₀ hr).mpr
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith
  simp only [incrementFluctuation,mul_pow,integral_const_mul]
  calc
    _ ≤ (Real.sqrt (2*t)/r)^p*((3^p*3*2^(p+1))*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^p*normPowerMean p) :=
      mul_le_mul_of_nonneg_left (incrementSize_power_mean s u p hp) (by positivity)
    _ = (3^p*3*2^(p+1))*(Real.sqrt (2*t)/r*Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^p*normPowerMean p := by ring
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hroot p) (by positivity)) (normPowerMean_nonneg p)

lemma incrementFluctuation_tail {t r R : ℝ} (ht : 0≤ t) (hr : 0< r) (hR : 0< R)
    (s u : Time) (hscale : t*(1-(s:ℝ))*(u:ℝ)≤ r^2) (p : ℕ) (hp : p≠0) :
    law {β | R≤ incrementFluctuation t r s u β}≤ ENNReal.ofReal (fluctuationMoment p)/(ENNReal.ofReal R)^p := by
  have hi : Integrable (fun β ↦ (incrementFluctuation t r s u β)^p) law := by
    unfold incrementFluctuation
    simp only [mul_pow]
    have h := (incrementSize_memLp_power s u p).integrable_norm_pow hp
    simp only [Real.norm_eq_abs,abs_of_nonneg (incrementSize_nonneg s u _)] at h
    exact h.const_mul _
  have hm := ((incrementFluctuation_continuous t r s u).pow p).measurable.ennreal_ofReal
  have h := meas_ge_le_lintegral_div (μ:=law) hm.aemeasurable
    (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hR p))) ENNReal.ofReal_ne_top
  have hsub : {β | R≤ incrementFluctuation t r s u β}⊆{β | ENNReal.ofReal (R^p)≤ ENNReal.ofReal ((incrementFluctuation t r s u β)^p)} := by
    intro β hβ
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hR.le hβ p)
  apply (measure_mono hsub).trans
  apply h.trans
  rw [ENNReal.ofReal_pow hR.le]
  apply ENNReal.div_le_div_right
  change (∫⁻β,ENNReal.ofReal ((incrementFluctuation t r s u β)^p) ∂law)≤_
  rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun β ↦ pow_nonneg (incrementFluctuation_nonneg hr.le s u β) p))]
  exact ENNReal.ofReal_le_ofReal (incrementFluctuation_power_mean ht hr s u hscale p hp)

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def legMeshRatio {n : ℕ} (t r : ℝ) (y u : Point) (j : Fin n) (β : Noise) : ℝ :=
  liftedDiameter 0 1 (fun i ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩)/r

lemma legMeshRatio_tail {n : ℕ} (j : Fin n) {t r C R : ℝ}
    (ht : 0≤ t) (hr : 0< r) (hR : 12≤ R) (y u : Point)
    (hC : 0≤ C) (hdis : ‖u-y‖≤ C) (hdrift : C/(n:ℝ)≤ r) (hscale : t/(n:ℝ)≤ r^2)
    (p : ℕ) (hp : p≠0) :
    law {β | R≤ legMeshRatio t r y u j β}≤
      ENNReal.ofReal (fluctuationMoment p)/(ENNReal.ofReal (R/12))^p := by
  apply (measure_mono (show {β | R≤ legMeshRatio t r y u j β}⊆
    {β | R/12≤ incrementFluctuation t r (meshTime j 0) (meshRemainder j) β} from ?_)).trans
    (incrementFluctuation_tail ht hr (by linarith) _ _ (by rw [mul_assoc,mesh_remaining]; simpa only [div_eq_mul_inv,one_mul] using hscale) p hp)
  intro β hβ
  have h := leg_mesh_diameter j (t:=t) hr y u β hC hdis hdrift
  change R≤ liftedDiameter _ _ _/r at hβ
  change R/12≤ incrementFluctuation t r (meshTime j 0) (meshRemainder j) β
  linarith

lemma legMeshMax_tail {n : ℕ} {t r C R : ℝ}
    (ht : 0≤ t) (hr : 0< r) (hR : 12≤ R) (y u : Point)
    (hC : 0≤ C) (hdis : ‖u-y‖≤ C) (hdrift : C/(n:ℝ)≤ r) (hscale : t/(n:ℝ)≤ r^2)
    (p : ℕ) (hp : p≠0) :
    law {β | ∃j : Fin n,R≤ legMeshRatio t r y u j β}≤
      (n:ℝ≥0∞)*(ENNReal.ofReal (fluctuationMoment p)/(ENNReal.ofReal (R/12))^p) := by
  have he : {β | ∃j : Fin n,R≤ legMeshRatio t r y u j β}=⋃j : Fin n,{β | R≤ legMeshRatio t r y u j β} := by
    ext β; simp
  rw [he]
  exact (measure_iUnion_fintype_le _ _).trans ((Finset.sum_le_sum (fun j _ ↦ legMeshRatio_tail j ht hr hR y u hC hdis hdrift hscale p hp)).trans_eq (by simp [nsmul_eq_mul]))

end HardSphere.Bridge

end
end

end

end OAI

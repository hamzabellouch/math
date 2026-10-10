import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.PathLift
import OAI.Analysis.HardSphere.Bridges.MeshLegHit

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def normPowerMean (p : ℕ) : ℝ := ∫w : C(Time,ℝ),‖w‖^p ∂wiener
lemma normPowerMean_nonneg (p : ℕ) : 0≤normPowerMean p := integral_nonneg (fun _ ↦ by positivity)
lemma integrable_normPower (p : ℕ) (hp : p≠0) : Integrable (fun w : C(Time,ℝ) ↦ ‖w‖^p) wiener :=
  (IsGaussian.memLp_id wiener p (by simp)).integrable_norm_pow hp

lemma loose_add_pow {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (p : ℕ) :
    (a+b)^p≤2^p*(a^p+b^p) := by
  calc
    _ ≤ (2*max a b)^p := pow_le_pow_left₀ (add_nonneg ha hb) (by linarith [le_max_left a b,le_max_right a b]) p
    _ = 2^p*(max a b)^p := mul_pow _ _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total a b with hab|hba
      · rw [max_eq_right hab]
        exact le_add_of_nonneg_left (pow_nonneg ha _)
      · rw [max_eq_left hba]
        exact le_add_of_nonneg_right (pow_nonneg hb _)

lemma prefix_normPower (u : Time) (p : ℕ) :
    ∫w : C(Time,ℝ),‖prefixMap u w‖^p ∂wiener=(Real.sqrt (u:ℝ))^p*normPowerMean p := by
  rw [←integral_map (f:=fun w : C(Time,ℝ) ↦ ‖w‖^p) (prefixMap u).continuous.measurable.aemeasurable (by fun_prop),prefix_wiener_law,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,integral_const_mul,normPowerMean]

lemma increment_wiener_power (s u : Time) (p : ℕ) :
    ∫β : C(Time,ℝ),‖incrementMap s u β‖^p ∂wiener =
      (Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^p*normPowerMean p := by
  change (∫β : C(Time,ℝ),‖prefixMap u (suffixMap s β)‖^p ∂wiener)=_
  rw [←integral_map (f:=fun β : C(Time,ℝ) ↦ ‖prefixMap u β‖^p) (suffixMap s).continuous.measurable.aemeasurable (by fun_prop),suffix_wiener_law,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [map_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,integral_const_mul]
  rw [prefix_normPower,Real.sqrt_mul (sub_nonneg.mpr s.property.2),mul_pow]
  ring

lemma increment_bridge_power (s u : Time) (p : ℕ) (hp : p≠0) :
    ∫β : C(Time,ℝ),‖incrementMap s u β‖^p ∂bridgeLaw ≤
      2^(p+1)*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^p*normPowerMean p := by
  let δ := (1-(s:ℝ))*(u:ℝ)
  have hd : 0≤δ := mul_nonneg (sub_nonneg.mpr s.property.2) u.property.1
  have hd1 : δ≤1 := by dsimp [δ]; nlinarith [s.property.1,s.property.2,u.property.1,u.property.2]
  have hi₁ : Integrable (fun f : C(Time,ℝ) ↦ ‖incrementMap s u (centerMap f)‖^p) wiener :=
    ((IsGaussian.memLp_id wiener p (by simp)).continuousLinearMap_comp ((incrementMap s u).comp centerMap)).integrable_norm_pow hp
  have hi₂ : Integrable (fun f : C(Time,ℝ) ↦ ‖incrementMap s u f‖^p) wiener :=
    ((IsGaussian.memLp_id wiener p (by simp)).continuousLinearMap_comp (incrementMap s u)).integrable_norm_pow hp
  rw [bridgeLaw_center,integral_map centerMap.continuous.measurable.aemeasurable (by fun_prop)]
  calc
    _ ≤ ∫f : C(Time,ℝ),2^p*(‖incrementMap s u f‖^p+δ^p*‖f‖^p) ∂wiener := by
      apply integral_mono hi₁ ((hi₂.add ((integrable_normPower p hp).const_mul _)).const_mul _)
      intro f
      exact (pow_le_pow_left₀ (norm_nonneg _) (increment_center_norm s u f) p).trans
        (by simpa only [Pi.add_apply,mul_pow,δ] using loose_add_pow (norm_nonneg (incrementMap s u f)) (mul_nonneg hd (norm_nonneg f)) p)
    _ = 2^p*((Real.sqrt δ)^p*normPowerMean p+δ^p*normPowerMean p) := by
      rw [integral_const_mul,integral_add hi₂ ((integrable_normPower p hp).const_mul _),integral_const_mul,increment_wiener_power]
      rfl
    _ ≤ _ := by
      have hds : δ≤Real.sqrt δ := Real.le_sqrt_of_sq_le (by nlinarith)
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd hds p) (normPowerMean_nonneg p)
      calc
        _ ≤ 2^p*((Real.sqrt δ)^p*normPowerMean p+(Real.sqrt δ)^p*normPowerMean p) := by gcongr
        _ = _ := by rw [pow_succ]; ring

end HardSphere.Wiener

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking
lemma sum_three_power (f : Fin 3→ℝ) (hf : ∀j,0≤f j) (p : ℕ) :
    (∑j,f j)^p≤3^p*(∑j,f j^p) := by
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image Finset.univ f (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
  have hsum : (∑j,f j)≤3*f i := by
    calc
      _ ≤ ∑_j : Fin 3,f i := Finset.sum_le_sum (fun j hj ↦ hmax j hj)
      _ = _ := by simp [nsmul_eq_mul]
  calc
    _ ≤ (3*f i)^p := pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ ↦ hf j)) hsum p
    _ = 3^p*(f i)^p := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ ↦ pow_nonneg (hf j) p) hi) (by positivity)

lemma incrementSize_memLp_power (s u : Time) (p : ℕ) : MemLp (incrementSize s u) p law := by
  apply memLp_finsetSum
  intro j hj
  have h := ((IsGaussian.memLp_id bridgeLaw p (by simp)).continuousLinearMap_comp (incrementMap s u)).norm
  exact h.comp_measurePreserving (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)

lemma incrementSize_power_mean (s u : Time) (p : ℕ) (hp : p≠0) :
    ∫β,(incrementSize s u β)^p ∂law ≤
      (3^p*3*2^(p+1))*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^p*normPowerMean p := by
  have hi j : Integrable (fun β : Noise ↦ ‖incrementMap s u (β j)‖^p) law := by
    exact (((IsGaussian.memLp_id bridgeLaw p (by simp)).continuousLinearMap_comp (incrementMap s u)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j)).integrable_norm_pow hp
  have hsum : Integrable (fun β ↦ (incrementSize s u β)^p) law := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (incrementSize_nonneg s u _)] using
      (incrementSize_memLp_power s u p).integrable_norm_pow hp
  calc
    _ ≤ ∫β,3^p*(∑j,‖incrementMap s u (β j)‖^p) ∂law := by
      apply integral_mono hsum ((integrable_finsetSum _ (fun j _ ↦ hi j)).const_mul _)
      intro β
      exact sum_three_power _ (fun j ↦ norm_nonneg _) p
    _ = 3^p*(∑j : Fin 3,∫β : C(Time,ℝ),‖incrementMap s u β‖^p ∂bridgeLaw) := by
      rw [integral_const_mul,integral_finsetSum _ (fun j _ ↦ hi j)]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hm := measurePreserving_eval (fun _ : Fin 3 ↦ bridgeLaw) j
      rw [←hm.map_eq,integral_map hm.measurable.aemeasurable (show Continuous (fun β : C(Time,ℝ) ↦ ‖incrementMap s u β‖^p) from (incrementMap s u).continuous.norm.pow p).aestronglyMeasurable]
      rfl
    _ ≤ 3^p*(∑_j : Fin 3,2^(p+1)*(Real.sqrt ((1-(s:ℝ))*(u:ℝ)))^p*normPowerMean p) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun _ _ ↦ increment_bridge_power s u p hp)) (by positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

def pathCoordinates (ω : C(Time,Point)) : Noise := fun j ↦ ⟨fun s ↦ ω s j,by fun_prop⟩

lemma liftedDiameter_coord_le (ζ : EuclideanPath) (a b : Time) {R : ℝ} (hR : 0≤R)
    (h : ∀j s q,|ζ j (intervalTime a b s)-ζ j (intervalTime a b q)|≤R) :
    liftedDiameter a b ζ≤3*R := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  change |Real.sqrt (∑j,(ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2))^2)|≤3*R
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  have hs : (∑j,(ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2))^2)≤3*R^2 := by
    calc
      _ ≤ ∑_j : Fin 3,R^2 := Finset.sum_le_sum (fun j _ ↦ by nlinarith [h j p.1 p.2,abs_nonneg (ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2)),sq_abs (ζ j (intervalTime a b p.1)-ζ j (intervalTime a b p.2))])
      _ = _ := by simp
  nlinarith [sq_nonneg R]

lemma leg_mesh_coord_bound {n : ℕ} (j : Fin n) {t r C : ℝ} (hr : 0<r)
    (y u : Point) (β : Noise) (_hC : 0≤C) (hdis : ‖u-y‖≤C) (hdrift : C/(n:ℝ)≤r)
    (q : Time) (i : Fin 3) :
    |leg t y u β (meshTime j q) i-leg t y u β (meshTime j 0) i|≤
      r*(1+incrementFluctuation t r (meshTime j 0) (meshRemainder j) β) := by
  let s := meshTime j 0
  let w := meshRemainder j
  have hq : (prefixTime w q:ℝ)≤(w:ℝ) := by
    change (w:ℝ)*(q:ℝ)≤(w:ℝ)
    nlinarith [w.property.1,q.property.2]
  rw [←mesh_suffix_time j q,leg_segment_increment]
  have hd : |((1-(s:ℝ))*(prefixTime w q:ℝ))*(u i-y i)|≤r := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) (prefixTime w q).property.1)]
    have hi : |u i-y i|≤C := (norm_le_pi_norm (u-y) i).trans hdis
    calc
       _ ≤ ((1-(s:ℝ))*(w:ℝ))*C := mul_le_mul (mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr s.property.2)) hi (abs_nonneg _) (mul_nonneg (sub_nonneg.mpr s.property.2) w.property.1)
       _ = C/(n:ℝ) := by rw [show (1-(s:ℝ))*(w:ℝ)=1/(n:ℝ) from mesh_remaining j]; ring
       _ ≤ _ := hdrift
  have hn := incrementFluctuation_eval (t:=t) hr s w (prefixTime w q) hq β i
  have he : leg t y u β s i+((1-(s:ℝ))*(prefixTime w q:ℝ))*(u i-y i)+
      Real.sqrt (2*t)*(β i (suffixTime s (prefixTime w q))-β i s)-leg t y u β s i=
      ((1-(s:ℝ))*(prefixTime w q:ℝ))*(u i-y i)+Real.sqrt (2*t)*(β i (suffixTime s (prefixTime w q))-β i s) := by ring
  change |leg t y u β s i+_+_-leg t y u β s i|≤_
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

lemma leg_mesh_diameter {n : ℕ} (j : Fin n) {t r C : ℝ} (hr : 0<r)
    (y u : Point) (β : Noise) (hC : 0≤C) (hdis : ‖u-y‖≤C) (hdrift : C/(n:ℝ)≤r) :
    liftedDiameter 0 1 (fun i ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩)/r≤
      6*(1+incrementFluctuation t r (meshTime j 0) (meshRemainder j) β) := by
  have hR : 0≤r*(1+incrementFluctuation t r (meshTime j 0) (meshRemainder j) β) :=
    mul_nonneg hr.le (by linarith [incrementFluctuation_nonneg (t:=t) hr.le (meshTime j 0) (meshRemainder j) β])
  apply (div_le_iff₀ hr).mpr
  have hh := liftedDiameter_coord_le (fun i ↦ (pathCoordinates (leg t y u β) i).comp ⟨meshTime j,meshTime_continuous j⟩) 0 1 (mul_nonneg (by norm_num : (0:ℝ)≤2) hR)
    (fun i s q ↦ by
      have hs := leg_mesh_coord_bound j (t:=t) hr y u β hC hdis hdrift (intervalTime 0 1 s) i
      have hq := leg_mesh_coord_bound j (t:=t) hr y u β hC hdis hdrift (intervalTime 0 1 q) i
      change |leg t y u β (meshTime j (intervalTime 0 1 s)) i-leg t y u β (meshTime j (intervalTime 0 1 q)) i|≤_
      have he : leg t y u β (meshTime j (intervalTime 0 1 s)) i-leg t y u β (meshTime j (intervalTime 0 1 q)) i=
          (leg t y u β (meshTime j (intervalTime 0 1 s)) i-leg t y u β (meshTime j 0) i)-
          (leg t y u β (meshTime j (intervalTime 0 1 q)) i-leg t y u β (meshTime j 0) i) := by ring
      rw [he]
      exact (abs_sub _ _).trans (by linarith))
  exact hh.trans (le_of_eq (by ring))

end HardSphere.Bridge

end
end

end

end OAI

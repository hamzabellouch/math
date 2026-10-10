import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.MeshEvents

namespace OAI

section

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def diameterRatio {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) := intervalDiameter 0 1 ω/r

def cubicCost {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) := (1+diameterRatio r ω)^3

lemma diameterRatio_continuous (L : Length) (r : ℝ) : Continuous (diameterRatio (L:=L) r) :=
  (intervalDiameter_continuous L 0 1).div_const r
lemma diameterRatio_nonneg {L : Length} {r : ℝ} (hr : 0≤r) (ω : ConfigurationPath 1 L) : 0≤diameterRatio r ω :=
  div_nonneg (intervalDiameter_nonneg 0 1 ω) hr
lemma cubicCost_continuous (L : Length) (r : ℝ) : Continuous (cubicCost (L:=L) r) :=
  (continuous_const.add (diameterRatio_continuous L r)).pow 3
lemma cubicCost_nonneg {L : Length} {r : ℝ} (hr : 0≤r) (ω : ConfigurationPath 1 L) : 0≤cubicCost r ω := by
  unfold cubicCost
  have := diameterRatio_nonneg hr ω
  positivity
lemma cubicCost_reverse {L : Length} (r : ℝ) (ω : ConfigurationPath 1 L) :
    cubicCost r (reverseConfigurationPath 1 L ω)=cubicCost r ω := by
  unfold cubicCost diameterRatio
  rw [intervalDiameter_reverse]
  have h1 : reverseTime 1=0 := by apply Subtype.ext; norm_num [reverseTime]
  have h0 : reverseTime 0=1 := by apply Subtype.ext; norm_num [reverseTime]
  rw [h1,h0]

lemma free_cubicCost_le {L : Length} {r t : ℝ} (hr : 0<r) (ht : t≤r^2)
    (w : CoordinatePaths 1) (X : Configuration 1 L) :
    cubicCost r (freeTrajectory 1 L t w X) ≤ (1+12*noiseSize w)^3 := by
  have hX : X=oneConfiguration (X 0) := by ext i j; have hi : i=0 := Subsingleton.elim _ _; subst i; rfl
  have h := free_diameter_noise L hr ht w (X 0)
  rw [←hX] at h
  unfold cubicCost diameterRatio
  exact pow_le_pow_left₀ (by have := intervalDiameter_nonneg 0 1 (freeTrajectory 1 L t w X); positivity) (add_le_add le_rfl h) 3

lemma free_cubicCost_integrable {L : Length} {r t : ℝ} (hr : 0<r) (ht : t≤r^2)
    (X : Configuration 1 L) :
    Integrable (fun w ↦ cubicCost r (freeTrajectory 1 L t w X)) (coordinateWiener 1) := by
  apply integrable_cubicNoise.mono'
    (((cubicCost_continuous L r).comp ((freeTrajectory_continuous 1 L t).comp
      (continuous_id.prodMk continuous_const))).aestronglyMeasurable)
  exact ae_of_all _ (fun w ↦ by
    change ‖cubicCost r (freeTrajectory 1 L t w X)‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (cubicCost_nonneg hr.le _)]
    exact free_cubicCost_le hr ht w X)

def cubicMean : ℝ := ∫w : CoordinatePaths 1,(1+12*noiseSize w)^3 ∂coordinateWiener 1
lemma cubicMean_nonneg : 0≤cubicMean := integral_nonneg (fun w ↦ by have := noiseSize_nonneg w; positivity)

lemma free_cubicMean_le {L : Length} {r t : ℝ} (hr : 0<r) (ht : t≤r^2) (X : Configuration 1 L) :
    ∫w,cubicCost r (freeTrajectory 1 L t w X) ∂coordinateWiener 1 ≤ cubicMean :=
  integral_mono (free_cubicCost_integrable hr ht X) integrable_cubicNoise (fun w ↦ free_cubicCost_le hr ht w X)

def cappedWeight {L : Length} (r B : ℝ) (ω : ConfigurationPath 1 L) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (min (cubicCost r ω) B/B))
lemma cappedWeight_measurable {L : Length} (r B : ℝ) : Measurable (cappedWeight (L:=L) r B) :=
  (Real.continuous_exp.comp (((cubicCost_continuous L r).min continuous_const).div_const B)).measurable.ennreal_ofReal

def meanCost : ℝ := (Real.exp 1-1)*cubicMean
lemma meanCost_nonneg : 0 ≤ meanCost := by
  unfold meanCost
  have he : 0≤Real.exp 1-1 := by have := Real.add_one_le_exp 1; linarith
  exact mul_nonneg he cubicMean_nonneg

lemma free_cap_moment {L : Length} {r t B : ℝ} (hr : 0<r) (ht : t≤r^2) (hB : 0<B)
    (X : Configuration 1 L) :
    ∫⁻w,cappedWeight r B (freeTrajectory 1 L t w X) ∂coordinateWiener 1 ≤
      ENNReal.ofReal (Real.exp (meanCost/B)) := by
  apply (exp_cap_integral (coordinateWiener 1) (free_cubicCost_integrable hr ht X)
    (ae_of_all _ (fun _ ↦ cubicCost_nonneg hr.le _)) hB).trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  unfold meanCost
  apply div_le_div_of_nonneg_right _ hB.le
  apply mul_le_mul_of_nonneg_left (free_cubicMean_le hr ht X)
  have := Real.add_one_le_exp 1
  linarith

end HardSphere.PathCutoff

end
end

section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff
open Wiener FreeVisits
attribute [local irreducible] torusDistance freeTrajectory

def capSum {L : Length} (m : ℕ) (r B : ℝ) (ω : ConfigurationPath 1 L) : ℝ :=
  ∑j : Fin m, min (cubicCost r (meshSegment j ω)) B
lemma capSum_continuous {L : Length} (m : ℕ) (r B : ℝ) : Continuous (capSum (L:=L) m r B) := by
  unfold capSum
  exact continuous_finsetSum _ (fun j _ ↦ ((cubicCost_continuous L r).comp (meshSegment_continuous L j)).min continuous_const)

lemma cap_product_eq {L : Length} (m : ℕ) (r B : ℝ) (ω : ConfigurationPath 1 L) :
    meshProduct m (cappedWeight r B) ω=ENNReal.ofReal (Real.exp (capSum m r B ω/B)) := by
  simp only [meshProduct,cappedWeight,capSum,Finset.sum_div,Real.exp_sum,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ Real.exp_nonneg _)]

lemma orig_exp_pow (x : ℝ) (m : ℕ) :
    (ENNReal.ofReal (Real.exp x))^m=ENNReal.ofReal (Real.exp ((m:ℝ)*x)) := by
  rw [←ENNReal.ofReal_pow (Real.exp_nonneg x),←Real.exp_nat_mul]

lemma mesh_cap_moment {L : Length} {r τ B : ℝ} (hr : 0<r) (hτ : 0<τ) (hτr : τ ≤ r^2) (hB : 0<B)
    (m : ℕ) (hm : 0 < m) (X : Configuration 1 L) :
    ∫⁻w,ENNReal.ofReal (Real.exp (capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)/B)) ∂coordinateWiener 1 ≤
      ENNReal.ofReal (Real.exp ((m:ℝ)*meanCost/B)) := by
  have h := meshProduct_free_bound (cappedWeight r B) (cappedWeight_measurable r B) hτ
    (ENNReal.ofReal (Real.exp (meanCost/B))) (fun Y ↦ free_cap_moment hr hτr hB Y) m hm X
  simpa only [cap_product_eq,orig_exp_pow,mul_div_assoc] using h

lemma mesh_cap_tail {L : Length} {r τ B : ℝ} (hr : 0<r) (hτ : 0<τ) (hτr : τ ≤ r^2) (hB : 0<B)
    (m : ℕ) (hm : 0 < m) (X : Configuration 1 L) :
    coordinateWiener 1 {w | (meanCost+1)*(m:ℝ) ≤ capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ≤
      ENNReal.ofReal (Real.exp (-(m:ℝ)/B)) := by
  let F : CoordinatePaths 1 → ℝ≥0∞ := fun w ↦
    ENNReal.ofReal (Real.exp (capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)/B))
  let v : ℝ≥0∞ := ENNReal.ofReal (Real.exp (((meanCost+1)*(m:ℝ))/B))
  have hF : Measurable F :=
    (Real.continuous_exp.comp (((capSum_continuous m r B).comp ((freeTrajectory_continuous 1 L ((m:ℝ)*τ)).comp
      (continuous_id.prodMk continuous_const))).div_const B)).measurable.ennreal_ofReal
  have hv : v≠0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hv' : v≠⊤ := ENNReal.ofReal_ne_top
  have hsub : {w | (meanCost+1)*(m:ℝ) ≤ capSum m r B (freeTrajectory 1 L ((m:ℝ)*τ) w X)} ⊆ {w | v ≤ F w} := by
    intro w hw
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hw hB.le))
  calc
    _ ≤ coordinateWiener 1 {w | v ≤ F w} := measure_mono hsub
    _ ≤ (∫⁻w,F w ∂coordinateWiener 1)/v := meas_ge_le_lintegral_div hF.aemeasurable hv hv'
    _ ≤ ENNReal.ofReal (Real.exp ((m:ℝ)*meanCost/B))/v :=
      ENNReal.div_le_div_right (mesh_cap_moment hr hτ hτr hB m hm X) v
    _ = ENNReal.ofReal (Real.exp (-(m:ℝ)/B)) := by
      dsimp only [v]
      rw [←ENNReal.ofReal_div_of_pos (Real.exp_pos _),←Real.exp_sub]
      congr 2
      ring

end HardSphere.PathCutoff

end
end

end

end OAI

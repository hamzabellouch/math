import Mathlib
import OAI.Analysis.HardSphere.Bridges.BridgeAssemble

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking

lemma midpointPoint_continuous (t : ℝ) (y z : Point) : Continuous (midpointPoint t y z) := by
  unfold midpointPoint
  fun_prop

def midpointLaw (t : ℝ) (y z : Point) : Measure Point := midpointNoise.map (midpointPoint t y z)
instance midpointLaw_probability (t : ℝ) (y z : Point) : IsProbabilityMeasure (midpointLaw t y z) := by
  unfold midpointLaw
  infer_instance

lemma trial_product (μ : Measure Point) [SFinite μ] (t : ℝ) (y z : Point) :
    (μ.compProd (trialKernel t y z)).map Prod.snd=
      (μ.prod (law.prod law)).map (fun p ↦ trialPath t y z p.1 p.2) := by
  ext B hB
  rw [Measure.map_apply measurable_snd hB,Measure.compProd_apply (hB.preimage measurable_snd),
    Measure.map_apply (trialPath_continuous t y z).measurable hB,
    Measure.prod_apply (hB.preimage (trialPath_continuous t y z).measurable)]
  apply lintegral_congr
  intro u
  change (trialKernel t y z u) B = (law.prod law) ((fun p ↦ trialPath t y z u p) ⁻¹' B)
  rw [trialKernel_apply]
  have hm : Continuous (trialPath t y z u) := (trialPath_continuous t y z).comp (continuous_const.prodMk continuous_id)
  exact Measure.map_apply hm.measurable hB

lemma full_bridge_midpoint {t : ℝ} (ht : 0≤t) (y z : Point) :
    ((midpointLaw t y z).compProd (trialKernel t y z)).map Prod.snd=
      law.map (leg (2*t) y z) := by
  rw [trial_product]
  have hpin : MeasurePreserving pinned law law := ⟨pinned_continuous.measurable,pinned_law⟩
  have hn := ((MeasurePreserving.id midpointNoise).prod hpin).prod (reverseNoise_preserving.comp hpin)
  have ha := assembleNoise_preserving.comp hn
  have hl := congrArg (fun μ : Measure Noise ↦ μ.map (leg (2*t) y z)) ha.map_eq
  rw [Measure.map_map (leg_continuous (2*t) y z).measurable ha.measurable] at hl
  have hm : MeasurePreserving (midpointPoint t y z) midpointNoise (midpointLaw t y z) :=
    ⟨(midpointPoint_continuous t y z).measurable,rfl⟩
  have hp := hm.prod (MeasurePreserving.id (law.prod law))
  have he := congrArg (fun μ : Measure (Point×(Noise×Noise)) ↦ μ.map (fun p ↦ trialPath t y z p.1 p.2)) hp.map_eq
  rw [Measure.map_map (trialPath_continuous t y z).measurable hp.measurable] at he
  rw [←he,← Measure.prodAssoc_prod (μ := midpointNoise) (ν := law) (τ := law),
    Measure.map_map ((trialPath_continuous t y z).measurable.comp hp.measurable) MeasurableEquiv.prodAssoc.measurable]
  convert hl using 1
  congr 1
  funext p
  exact trial_assemble t ht y z p.1.1 p.1.2 p.2

lemma midpointLaw_gaussian {t : ℝ} (ht : 0≤t) (y z : Point) :
    midpointLaw t y z=Measure.pi (fun j : Fin 3 ↦ gaussianReal ((y j+z j)/2) (Real.toNNReal t)) := by
  unfold midpointLaw midpointNoise midpointPoint
  rw [Measure.pi_map_pi (fun _ ↦ (by fun_prop : Measurable (fun v : ℝ ↦ (_ : ℝ)+Real.sqrt (4*t)*v)).aemeasurable)]
  congr 1
  funext j
  have h : HasLaw id (gaussianReal 0 (Real.toNNReal (1/4:ℝ))) (gaussianReal 0 (Real.toNNReal (1/4:ℝ))) := ⟨measurable_id.aemeasurable,Measure.map_id⟩
  have he := (gaussianReal_const_add (gaussianReal_const_mul h (Real.sqrt (4*t))) ((y j+z j)/2)).map_eq
  simp only [mul_zero,zero_add] at he
  change _ = _ at he
  change (Measure.map (fun v ↦ (y j+z j)/2+Real.sqrt (4*t)*v) _) = _
  simp only [id_eq] at he
  rw [he]
  apply congrArg (gaussianReal ((y j+z j)/2))
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul,NNReal.coe_mk,Real.coe_toNNReal _ ht,
    Real.coe_toNNReal _ (show 0≤(1/4:ℝ) by norm_num),Real.sq_sqrt (show 0≤4*t by positivity)]
  ring

end HardSphere.Bridge

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.GaussianPacking

def densityLower (b C : ℝ) : ℝ := (Real.sqrt (b/Real.pi))^3*Real.exp (-b*(3*C^2))
lemma densityLower_pos {b : ℝ} (hb : 0<b) (C : ℝ) : 0<densityLower b C := by
  unfold densityLower
  exact mul_pos (pow_pos (Real.sqrt_pos.mpr (div_pos hb Real.pi_pos)) _) (Real.exp_pos _)

lemma density_lower {b C : ℝ} (hb : 0≤b) (hC : 0≤C) (x : Point) (hx : ‖x‖≤C) :
    densityLower b C≤density b x := by
  have hs : square x≤3*C^2 := by
    unfold square
    calc
      _ ≤ ∑_j : Fin 3,C^2 := Finset.sum_le_sum (fun j _ ↦ by
        have h := (norm_le_pi_norm x j).trans hx
        simpa only [Real.norm_eq_abs,sq_abs] using (sq_le_sq₀ (norm_nonneg (x j)) hC).mpr h)
      _ = _ := by simp
  unfold density densityLower kernel
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)

lemma gaussian_dominates_local {v : ℝ≥0} (hv : v≠0) (q : Point) {C : ℝ} (hC : 0≤C)
    {B : Set Point} (hB : MeasurableSet B) (hbound : ∀x∈B,‖x-q‖≤C) :
    ENNReal.ofReal (densityLower ((2*(v:ℝ))⁻¹) C) • (volume.restrict B) ≤
      Measure.pi (fun j : Fin 3 ↦ gaussianReal (q j) v) := by
  rw [gaussian_pi_eq q hv]
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hA,
    withDensity_apply _ hA]
  calc
    _ = ∫⁻x in A∩B,ENNReal.ofReal (densityLower ((2*(v:ℝ))⁻¹) C) := by simp [lintegral_const]
    _ ≤ ∫⁻x in A∩B,ENNReal.ofReal (density ((2*(v:ℝ))⁻¹) (x-q)) := by
      apply setLIntegral_mono' (hA.inter hB)
      intro x hx
      exact ENNReal.ofReal_le_ofReal (density_lower (by positivity) hC (x-q) (hbound x hx.2))
    _ ≤ _ := lintegral_mono_set inter_subset_left

end HardSphere.GaussianPacking

end
end

end

end OAI

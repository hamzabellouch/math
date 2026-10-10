import OAI.Geometry.Kahler.BasePatchPhase

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
noncomputable section

open Set Filter Topology MeasureTheory
namespace PinchedHartogs.BaseConstruction

def bracketUnit (p ξ : Sphere) : unitInterval := radialUnit (sphereAction (adaptedIsometry p) ξ)

lemma bracketUnit_continuous (p : Sphere) : Continuous (bracketUnit p) :=
  radialUnit_continuous.comp (sphereAction _).continuous

lemma bracketUnit_coe (p ξ : Sphere) : (bracketUnit p ξ:ℝ)=‖bracket (ξ:Base) (p:Base)‖^2 :=
  adapted_radialU ξ p

lemma bracketUnit_preserves (p : Sphere) : MeasurePreserving (bracketUnit p) sigma volume :=
  (show MeasurePreserving radialUnit sigma volume from ⟨radialUnit_continuous.measurable,radial_law⟩).comp
    (sphereAction_preserves (adaptedIsometry p))

lemma peakPatch_iff_radial {k : ℕ} (hk : 0 < k) (R : ℝ) (p ξ : Sphere) :
    ξ ∈ peakPatch k R p ↔ Real.exp (-2*R/k) < (bracketUnit p ξ:ℝ) := by
  rw [bracketUnit_coe]
  have he : Real.exp (-2*R/k)=Real.exp (-R/k)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp [show (k:ℝ) ≠ 0 by exact_mod_cast hk.ne']
    ring
  rw [he]
  exact (sq_lt_sq₀ (Real.exp_pos _).le (norm_nonneg _)).symm

lemma densityHeight_radial (k : ℕ) (p ξ : Sphere) :
    densityHeight k p ξ=-(k:ℝ)/2*Real.log (bracketUnit p ξ:ℝ) := by
  rw [bracketUnit_coe,Real.log_pow,densityHeight]
  ring

lemma radial_patch_integral {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R)
    (p : Sphere) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ ξ in peakPatch k R p, g (densityHeight k p ξ) ∂sigma)=
      ∫ t in Real.exp (-2*R/k)..1, g (-(k:ℝ)/2*Real.log t) := by
  classical
  let a := Real.exp (-2*R/k)
  let G : ℝ → ℝ := fun t => g (-(k:ℝ)/2*Real.log t)
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (by exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hk0.le)
  have hG : AEStronglyMeasurable (fun t : unitInterval => (Ioi a).indicator G t) volume := by
    apply Measurable.aestronglyMeasurable
    exact ((hg.measurable.comp (measurable_const.mul Real.measurable_log)).indicator measurableSet_Ioi).comp measurable_subtype_coe
  have he : (fun ξ : Sphere => (peakPatch k R p).indicator (fun ξ => g (densityHeight k p ξ)) ξ) =
      fun ξ : Sphere => (Ioi a).indicator G (bracketUnit p ξ) := by
    funext ξ
    simp only [indicator_apply,peakPatch_iff_radial hk,mem_Ioi]
    split_ifs <;> simp only [G,densityHeight_radial]
  rw [← integral_indicator (peakPatch_open k R p).measurableSet,he]
  have hm := (bracketUnit_preserves p).map_eq
  calc
    _ = ∫ t : unitInterval, (Ioi a).indicator G t := by
      rw [← hm,integral_map (bracketUnit_continuous p).measurable.aemeasurable]
      rwa [hm]
    _ = ∫ t in Icc (0:ℝ) 1, (Ioi a).indicator G t := by
      rw [unitInterval.volume_def,integral_subtype_comap measurableSet_Icc]
    _ = ∫ t in Ioc a 1, G t := by
      rw [integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
      have hs : Ioi a ∩ Icc (0:ℝ) 1 = Ioc a 1 := by
        ext t
        simp only [mem_inter_iff,mem_Ioi,mem_Icc,mem_Ioc]
        constructor
        · rintro ⟨ht,_,ht1⟩
          exact ⟨ht,ht1⟩
        · rintro ⟨ht,ht1⟩
          exact ⟨ht,ha.le.trans ht.le,ht1⟩
      rw [hs]
    _ = _ := (intervalIntegral.integral_of_le ha1).symm

lemma log_radial_substitution_real {k R : ℝ} (hk : 0 < k) (hR : 0 < R)
    {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ t in Real.exp (-2*R/k)..1, t⁻¹*F (-k/2*Real.log t)) =
      2/k*(∫ y in 0..R, F y) := by
  have hh := log_radial_substitution hk hR (Complex.continuous_ofReal.comp hF)
  change (∫ t in Real.exp (-2*R/k)..1, (t⁻¹:ℝ) • (F (-k/2*Real.log t):ℂ)) = _ at hh
  simp only [Function.comp_apply,Complex.real_smul,← Complex.ofReal_mul] at hh
  rw [intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal,← Complex.ofReal_mul] at hh
  exact Complex.ofReal_injective hh

lemma radial_patch_integral_exp {k : ℕ} (hk : 0 < k) {R : ℝ} (hR : 0 < R)
    (p : Sphere) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ ξ in peakPatch k R p, g (densityHeight k p ξ) ∂sigma)=
      2/(k:ℝ)*(∫ y in 0..R, Real.exp (-2*y/k)*g y) := by
  rw [radial_patch_integral hk hR p hg]
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hc : Continuous (fun y : ℝ => Real.exp (-2*y/k)*g y) := (by fun_prop : Continuous (fun y : ℝ => Real.exp (-2*y/k))).mul hg
  have hh := log_radial_substitution_real hk0 hR hc
  rw [← hh]
  apply intervalIntegral.integral_congr
  intro t ht
  have ha1 : Real.exp (-2*R/(k:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hk0.le)
  rw [uIcc_of_le ha1] at ht
  have ht0 : 0 < t := (Real.exp_pos _).trans_le ht.1
  have he : -2*(-(k:ℝ)/2*Real.log t)/k=Real.log t := by field_simp
  dsimp only
  rw [he,Real.exp_log ht0,← mul_assoc,inv_mul_cancel₀ ht0.ne',one_mul]

end PinchedHartogs.BaseConstruction

end

end OAI

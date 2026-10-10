import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology
open scoped ENNReal

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} {D : Set X}

def lpZeroExtensionL (hD : MeasurableSet D) : Lp E 2 (μ.restrict D) →ₗ[ℝ] Lp E 2 μ where
  toFun f := ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).toLp (D.indicator f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [((memLp_indicator_iff_restrict hD).mpr (Lp.memLp (f+g))).coeFn_toLp,
      ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).coeFn_toLp,
      ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp g)).coeFn_toLp,
      Lp.coeFn_add (((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).toLp (D.indicator f))
        (((memLp_indicator_iff_restrict hD).mpr (Lp.memLp g)).toLp (D.indicator g)),
      (ae_restrict_iff' hD).mp (Lp.coeFn_add f g)] with x hfg hf hg he hadd
    rw [hfg,he]
    simp only [Pi.add_apply,hf,hg]
    by_cases hx : x∈D
    · simp only [indicator_of_mem hx,hadd hx,Pi.add_apply]
    · simp [hx]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [((memLp_indicator_iff_restrict hD).mpr (Lp.memLp (c•f))).coeFn_toLp,
      ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).coeFn_toLp,
      Lp.coeFn_smul c (((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).toLp (D.indicator f)),
      (ae_restrict_iff' hD).mp (Lp.coeFn_smul c f)] with x hcf hf he hsmul
    change _=(c • _ : Lp E 2 μ) x
    rw [hcf,he]
    simp only [Pi.smul_apply,hf]
    by_cases hx : x∈D
    · simp only [indicator_of_mem hx,hsmul hx,Pi.smul_apply]
    · simp [hx]

lemma lpZeroExtensionL_ae (hD : MeasurableSet D) (f : Lp E 2 (μ.restrict D)) :
    lpZeroExtensionL hD f=ᵐ[μ] D.indicator f :=
  ((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).coeFn_toLp

lemma lpZeroExtensionL_norm (hD : MeasurableSet D) (f : Lp E 2 (μ.restrict D)) :
    ‖lpZeroExtensionL hD f‖=‖f‖ := by
  change ‖((memLp_indicator_iff_restrict hD).mpr (Lp.memLp f)).toLp (D.indicator f)‖=_
  rw [Lp.norm_toLp,eLpNorm_indicator_eq_eLpNorm_restrict hD,Lp.norm_def]

def lpZeroExtensionCLM (hD : MeasurableSet D) : Lp E 2 (μ.restrict D) →L[ℝ] Lp E 2 μ :=
  (lpZeroExtensionL hD).mkContinuous 1 (by intro f; rw [lpZeroExtensionL_norm,one_mul])

lemma lpZeroExtensionCLM_ae (hD : MeasurableSet D) (f : Lp E 2 (μ.restrict D)) :
    lpZeroExtensionCLM hD f=ᵐ[μ] D.indicator f := lpZeroExtensionL_ae hD f

lemma lpZeroExtensionCLM_ae_of_ae (hD : MeasurableSet D) (f : Lp E 2 (μ.restrict D))
    {g : X → E} (hg : f=ᵐ[μ.restrict D] g) :
    lpZeroExtensionCLM hD f=ᵐ[μ] D.indicator g := by
  filter_upwards [lpZeroExtensionCLM_ae hD f,(ae_restrict_iff' hD).mp hg] with x hx hg
  rw [hx]
  by_cases h : x∈D
  · simp only [indicator_of_mem h,hg h]
  · simp [h]

def lpRestrictionCLM (D : Set X) : Lp E 2 μ →L[ℝ] Lp E 2 (μ.restrict D) :=
  Lp.LpToLpOfMeasureLeSMul (c:=1) (by simp) (by simpa using Measure.restrict_le_self (μ:=μ) (s:=D))

lemma lpRestrictionCLM_ae (D : Set X) (f : Lp E 2 μ) :
    lpRestrictionCLM D f=ᵐ[μ.restrict D] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (c:=1) (by simp) (by simpa using Measure.restrict_le_self (μ:=μ) (s:=D)) f

end

open Set MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
  {χ : X → ℝ} {C : ℝ} (hχ : AEStronglyMeasurable χ μ) (hb : ∀ᵐ x∂μ,‖χ x‖≤C)

include hχ hb in
lemma lpMultiplier_mem (f : Lp ℝ 2 μ) : MemLp (fun x => χ x*f x) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c:=C) (hχ.mul (Lp.memLp f).aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖χ x*f x‖≤C*‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

def lpMultiplierL : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ where
  toFun f := (lpMultiplier_mem hχ hb f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(lpMultiplier_mem hχ hb (f+g)).coeFn_toLp,
      (lpMultiplier_mem hχ hb f).coeFn_toLp,(lpMultiplier_mem hχ hb g).coeFn_toLp,
      Lp.coeFn_add f g,Lp.coeFn_add ((lpMultiplier_mem hχ hb f).toLp _)
        ((lpMultiplier_mem hχ hb g).toLp _)] with x hfg hf hg hi he
    rw [hfg,he]
    simp only [Pi.add_apply,hf,hg,hi,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(lpMultiplier_mem hχ hb (c•f)).coeFn_toLp,
      (lpMultiplier_mem hχ hb f).coeFn_toLp,Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((lpMultiplier_mem hχ hb f).toLp _)] with x hcf hf hi he
    change _=(c • _ : Lp ℝ 2 μ) x
    rw [hcf,he]
    simp only [Pi.smul_apply,smul_eq_mul,hf,hi]
    ring

def lpMultiplierCLM : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (lpMultiplierL hχ hb).mkContinuous C (by
    intro f
    change ‖(lpMultiplier_mem hχ hb f).toLp _‖≤C*‖f‖
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(lpMultiplier_mem hχ hb f).coeFn_toLp,hb] with x hx hb
    rw [hx,norm_mul]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma lpMultiplierCLM_ae (f : Lp ℝ 2 μ) :
    lpMultiplierCLM hχ hb f=ᵐ[μ] (fun x => χ x*f x) :=
  (lpMultiplier_mem hχ hb f).coeFn_toLp

def compactMultiplierCLM [TopologicalSpace X] [BorelSpace X]
    (hχ : Continuous χ) (hc : HasCompactSupport χ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  lpMultiplierCLM hχ.aestronglyMeasurable
    (Eventually.of_forall (hc.exists_bound_of_continuous hχ).choose_spec)

lemma compactMultiplierCLM_ae [TopologicalSpace X] [BorelSpace X]
    (hχ : Continuous χ) (hc : HasCompactSupport χ) (f : Lp ℝ 2 μ) :
    compactMultiplierCLM hχ hc f=ᵐ[μ] (fun x => χ x*f x) :=
  lpMultiplierCLM_ae _ _ f

end ScalarConductivity

end

end OAI

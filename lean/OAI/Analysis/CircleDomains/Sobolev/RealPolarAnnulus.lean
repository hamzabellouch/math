import OAI.Analysis.CircleDomains.Sobolev.PolarAnnulusEnergy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

namespace OAI

/-! Real polar integration, specialized to continuous energy densities on
bounded annuli. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem integral_polar_annulus {g : ℂ → ℝ} (hg : Continuous g)
    {a b : ℝ} (ha : 0 ≤ a) :
    (∫ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, g z) =
      ∫ r in Ioo a b, ∫ θ in Ioo (-Real.pi) Real.pi,
        r * g (Complex.polarCoord.symm (r, θ)) := by
  let A := {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}
  let S := Ioo a b
  let T := Ioo (-Real.pi) Real.pi
  let f : ℝ × ℝ → ℝ := fun p => p.1 * g (Complex.polarCoord.symm p)
  have hA : MeasurableSet A := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have hP : MeasurableSet polarCoord.target := polarCoord.open_target.measurableSet
  have hf : Continuous f := by
    apply Continuous.mul continuous_fst
    apply hg.comp
    change Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p)
    simp_rw [Complex.polarCoord_symm_apply]
    fun_prop
  have hfi : IntegrableOn f (S ×ˢ T) :=
    ((hf.continuousOn.integrableOn_compact
      ((isCompact_Icc : IsCompact (Icc a b)).prod isCompact_Icc))).mono_set
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hpolar := Complex.integral_comp_polarCoord_symm (A.indicator g)
  rw [integral_indicator hA] at hpolar
  calc
    _ = ∫ p in polarCoord.target,
        p.1 * (A.indicator g) (Complex.polarCoord.symm p) := hpolar.symm
    _ = ∫ p, (S ×ˢ T).indicator f p := by
      rw [← integral_indicator hP]
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ polarCoord.target
      · have hp0 : 0 < p.1 := hp.1
        have hmem : Complex.polarCoord.symm p ∈ A ↔ p.1 ∈ S := by
          simp only [A, S, mem_ofPred_eq, mem_Ioo, Complex.norm_polarCoord_symm,
            abs_of_pos hp0]
        by_cases hS : p.1 ∈ S
        · have hST : p ∈ S ×ˢ T := ⟨hS, hp.2⟩
          rw [indicator_of_mem hp, indicator_of_mem hST, indicator_of_mem (hmem.mpr hS)]
        · have hST : p ∉ S ×ˢ T := fun h => hS h.1
          rw [indicator_of_mem hp, indicator_of_notMem hST,
            indicator_of_notMem (fun h => hS (hmem.mp h)), mul_zero]
      · have hST : p ∉ S ×ˢ T := by
          rintro ⟨hS, hT⟩
          exact hp ⟨lt_of_le_of_lt ha hS.1, hT⟩
        rw [indicator_of_notMem hp, indicator_of_notMem hST]
    _ = ∫ p in S ×ˢ T, f p := integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)
    _ = _ := setIntegral_prod f hfi

 theorem integral_polar_annulus_circle {g : ℂ → ℝ} (hg : Continuous g)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, g z) =
      ∫ r in a..b, r * (∫ θ in (0 : ℝ)..(2*Real.pi), g (circleMap 0 r θ)) := by
  rw [integral_polar_annulus hg ha, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _
  have hp := ((periodic_circleMap 0 r).comp g).intervalIntegral_add_eq (-Real.pi) 0
  have hends : -Real.pi + 2*Real.pi = Real.pi := by ring
  simp only [hends, zero_add, Function.comp_def] at hp
  dsimp only
  rw [← hp, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _
  simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]

 theorem integral_polar_annulus_center {g : ℂ → ℝ} (hg : Continuous g)
    (c : ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ z in {z : ℂ | a < dist z c ∧ dist z c < b}, g z) =
      ∫ r in a..b, r * (∫ θ in (0 : ℝ)..(2*Real.pi), g (circleMap c r θ)) := by
  let A := {z : ℂ | a < dist z c ∧ dist z c < b}
  have he : ((fun z : ℂ => c+z) ⁻¹' A) = {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
    ext z
    simp [A, dist_eq_norm]
  have ht := (measurePreserving_add_left volume c).setIntegral_preimage_emb
    (Homeomorph.addLeft c).measurableEmbedding g A
  rw [he] at ht
  have hh := integral_polar_annulus_circle (g := fun z => g (c+z))
    (hg.comp (continuous_const.add continuous_id)) ha hab
  rw [← ht, hh]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp [circleMap]

end CircleDomainRigidity

end

end OAI

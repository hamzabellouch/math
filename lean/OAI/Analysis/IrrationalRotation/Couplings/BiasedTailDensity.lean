import OAI.Analysis.IrrationalRotation.Model.BiasedTailDensity
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace Invariant233.BiasedTailDensity

variable {P Z : Type*} [MeasurableSpace P] [MeasurableSpace Z]
  {μ : Measure P} {ν : Measure Z}

theorem sq_integral_le_integral_sq [IsProbabilityMeasure μ] {f : P → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun u => f u ^ 2) μ) :
    (∫ u, f u ∂μ) ^ 2 ≤ ∫ u, f u ^ 2 ∂μ := by
  let a := ∫ u, f u ∂μ
  have hn : 0 ≤ ∫ u, (f u - a) ^ 2 ∂μ :=
    integral_nonneg fun u => sq_nonneg _
  have heq : (fun u => (f u - a) ^ 2) =
      fun u => (f u ^ 2 - (2 * a) * f u) + a ^ 2 := by
    funext u
    ring
  rw [heq] at hn
  rw [integral_add (f := fun u => f u ^ 2 - (2 * a) * f u)
      (g := fun _ => a ^ 2) (hf2.sub (hf.const_mul (2 * a))) (integrable_const _),
    integral_sub (f := fun u => f u ^ 2) (g := fun u => (2 * a) * f u)
      hf2 (hf.const_mul (2 * a)), integral_const_mul, integral_const] at hn
  simp only [probReal_univ, one_smul] at hn
  change a ^ 2 ≤ _
  change 0 ≤ (∫ u, f u ^ 2 ∂μ) - (2 * a) * a + a ^ 2 at hn
  nlinarith

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem integrable_tailDensity {g : P × Z → ℝ} (hg : MemLp g 2 (μ.prod ν)) :
    Integrable (tailDensity μ g) ν :=
  (hg.integrable (by norm_num)).integral_prod_right

theorem ae_sq_tailDensity_le {g : P × Z → ℝ} (hg : MemLp g 2 (μ.prod ν)) :
    ∀ᵐ z ∂ν, tailDensity μ g z ^ 2 ≤ ∫ u, g (u, z) ^ 2 ∂μ := by
  filter_upwards [(hg.integrable (by norm_num)).prod_left_ae,
    hg.integrable_sq.prod_left_ae] with z hz hz2
  exact sq_integral_le_integral_sq hz hz2

theorem memLp_tailDensity {g : P × Z → ℝ} (hg : MemLp g 2 (μ.prod ν)) :
    MemLp (tailDensity μ g) 2 ν := by
  apply (memLp_two_iff_integrable_sq (integrable_tailDensity hg).aestronglyMeasurable).2
  apply Integrable.mono hg.integrable_sq.integral_prod_right
    ((integrable_tailDensity hg).aestronglyMeasurable.pow 2)
  filter_upwards [ae_sq_tailDensity_le hg] with z hz
  change |tailDensity μ g z ^ 2| ≤ |∫ u, g (u, z) ^ 2 ∂μ|
  rw [abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (integral_nonneg fun u => sq_nonneg (g (u, z)))]
  exact hz

theorem integral_sq_tailDensity_le {g : P × Z → ℝ} (hg : MemLp g 2 (μ.prod ν)) :
    (∫ z, tailDensity μ g z ^ 2 ∂ν) ≤ ∫ p, g p ^ 2 ∂μ.prod ν := by
  calc
    _ ≤ ∫ z, ∫ u, g (u, z) ^ 2 ∂μ ∂ν :=
      integral_mono_ae (memLp_tailDensity hg).integrable_sq
        hg.integrable_sq.integral_prod_right (ae_sq_tailDensity_le hg)
    _ = _ := (integral_prod_symm _ hg.integrable_sq).symm

theorem eLpNorm_tailDensity_le {g : P × Z → ℝ} (hg : MemLp g 2 (μ.prod ν)) :
    eLpNorm (tailDensity μ g) 2 ν ≤ eLpNorm g 2 (μ.prod ν) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      (memLp_tailDensity hg),
    MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hg]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _)
    (integral_sq_tailDensity_le hg) (by positivity)

theorem integral_tailDensity {g : P × Z → ℝ} (hg : MemLp g 2 (μ.prod ν)) :
    (∫ z, tailDensity μ g z ∂ν) = ∫ p, g p ∂μ.prod ν :=
  (integral_prod_symm _ (hg.integrable (by norm_num))).symm

theorem map_snd_withDensity_lintegral {g : P × Z → ℝ≥0∞}
    (hg : AEMeasurable g (μ.prod ν)) :
    ((μ.prod ν).withDensity g).map Prod.snd =
      ν.withDensity (fun z => ∫⁻ u, g (u, z) ∂μ) := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs,
    withDensity_apply _ (measurable_snd hs), withDensity_apply _ hs]
  have heq : Prod.snd ⁻¹' s = (Set.univ : Set P) ×ˢ s := by
    ext x
    simp
  rw [heq, setLIntegral_prod_symm _ hg.restrict]
  simp only [Measure.restrict_univ]

theorem ae_nonneg_tailDensity {g : P × Z → ℝ}
    (hn : 0 ≤ᵐ[μ.prod ν] g) : 0 ≤ᵐ[ν] tailDensity μ g := by
  have hs : ∀ᵐ q ∂ν.prod μ, 0 ≤ g (q.2, q.1) :=
    measurePreserving_swap.quasiMeasurePreserving.ae hn
  filter_upwards [ae_ae_of_ae_prod hs] with z hz
  exact integral_nonneg_of_ae hz

theorem map_snd_withDensity_tailDensity {g : P × Z → ℝ}
    (hg : MemLp g 2 (μ.prod ν)) (hn : 0 ≤ᵐ[μ.prod ν] g) :
    ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (g p))).map Prod.snd =
      ν.withDensity (fun z => ENNReal.ofReal (tailDensity μ g z)) := by
  rw [map_snd_withDensity_lintegral hg.aemeasurable.ennreal_ofReal]
  apply withDensity_congr_ae
  have hs : ∀ᵐ q ∂ν.prod μ, 0 ≤ g (q.2, q.1) :=
    measurePreserving_swap.quasiMeasurePreserving.ae hn
  filter_upwards [(hg.integrable (by norm_num)).prod_left_ae,
    ae_ae_of_ae_prod hs] with z hz hzn
  exact (ofReal_integral_eq_lintegral_ofReal hz hzn).symm

theorem tailDensity_spec {g : P × Z → ℝ}
    (hg : MemLp g 2 (μ.prod ν)) (hn : 0 ≤ᵐ[μ.prod ν] g)
    (hmass : ∫ p, g p ∂μ.prod ν = 1) :
    MemLp (tailDensity μ g) 2 ν ∧
      0 ≤ᵐ[ν] tailDensity μ g ∧
      (∫ z, tailDensity μ g z ∂ν) = 1 ∧
      eLpNorm (tailDensity μ g) 2 ν ≤ eLpNorm g 2 (μ.prod ν) ∧
      ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (g p))).map Prod.snd =
        ν.withDensity (fun z => ENNReal.ofReal (tailDensity μ g z)) := by
  exact ⟨memLp_tailDensity hg, ae_nonneg_tailDensity hn,
    (integral_tailDensity hg).trans hmass, eLpNorm_tailDensity_le hg,
    map_snd_withDensity_tailDensity hg hn⟩

end Invariant233.BiasedTailDensity

end

end OAI

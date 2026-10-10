import OAI.MeasureTheory.Falconer.Slicing.GaussianRows
import OAI.MeasureTheory.Falconer.Recursion.PotentialFrostman

namespace OAI

/-! # Second moments of the actual Gaussian direction bands -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d h : ℕ}

noncomputable def gaussianDirectionBand (A : Fin h → Space d) (r : ℝ) : Set (Sphere d) :=
  {w | ∀ i, |inner ℝ (w:Space d) (A i)| ≤ r}

theorem gaussianDirectionBand_measurable (A : Fin h → Space d) (r : ℝ) :
    MeasurableSet (gaussianDirectionBand A r) := by
  simp only [gaussianDirectionBand,ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le (by fun_prop) measurable_const

theorem gaussian_direction_band_second_moment (ν : Measure (Sphere d)) [IsFiniteMeasure ν] (r : ℝ) :
    (∫⁻ A : Fin h → Space d, (ν (gaussianDirectionBand A r))^2 ∂gaussianRows d h) =
      ∫⁻ z : Sphere d × Sphere d,
        gaussianRows d h {A | ∀ i,
          |inner ℝ (z.1:Space d) (A i)| ≤ r ∧ |inner ℝ (z.2:Space d) (A i)| ≤ r} ∂ν.prod ν := by
  let S : Set ((Fin h → Space d) × (Sphere d × Sphere d)) := {p | ∀ i,
    |inner ℝ (p.2.1:Space d) (p.1 i)| ≤ r ∧ |inner ℝ (p.2.2:Space d) (p.1 i)| ≤ r}
  have hS : MeasurableSet S := by
    simp only [S,ofPred_forall,ofPred_and]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hsection (A : Fin h → Space d) : Prod.mk A ⁻¹' S =
      (gaussianDirectionBand A r) ×ˢ (gaussianDirectionBand A r) := by
    ext z
    simp only [S,gaussianDirectionBand,mem_preimage,mem_ofPred_eq,mem_prod]
    exact forall_and
  calc
    _ = ∫⁻ A : Fin h → Space d, (ν.prod ν) (Prod.mk A ⁻¹' S) ∂gaussianRows d h := by
      apply lintegral_congr
      intro A
      rw [hsection,Measure.prod_prod,pow_two]
    _ = ((gaussianRows d h).prod (ν.prod ν)) S := (Measure.prod_apply hS).symm
    _ = _ := Measure.prod_apply_symm hS

theorem gaussian_direction_band_second_moment_bound (ν : Measure (Sphere d)) [IsFiniteMeasure ν]
    {r : ℝ} (hr : 0 < r)
    (hchart : ∀ᵐ z : Sphere d × Sphere d ∂ν.prod ν, 0 ≤ inner ℝ (z.1:Space d) (z.2:Space d)) :
    (∫⁻ A : Fin h → Space d, (ν (gaussianDirectionBand A r))^2 ∂gaussianRows d h) ≤
      ∫⁻ z : Sphere d × Sphere d,
        ENNReal.ofReal ((2*gaussianPairBandConstant*r^2/(dist z.1 z.2+r))^h) ∂ν.prod ν := by
  rw [gaussian_direction_band_second_moment]
  apply lintegral_mono_ae
  filter_upwards [hchart] with z hz
  simpa only [Subtype.dist_eq] using gaussianRows_pair_band_chart (h := h)
    (sphere_norm z.1) (sphere_norm z.2) hz hr

end Falconer

end OAI

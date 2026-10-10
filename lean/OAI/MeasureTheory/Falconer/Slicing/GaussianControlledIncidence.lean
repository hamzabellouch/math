import OAI.MeasureTheory.Falconer.Slicing.GaussianControlledRows
import OAI.MeasureTheory.Falconer.Slicing.GaussianIncidenceAverage

namespace OAI

/-! # Original-label incidence on the uniformly controlled row chart -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {n h : ℕ}

theorem incidence_direction_ae (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space (n+1) × Sphere (n+1))) {P : Sphere (n+1) → Prop}
    (hP : ∀ᵐ w ∂ν, P w) :
    ∀ᵐ w ∂(((μ.prod ν).restrict E).map Prod.snd), P w := by
  have hd : ((μ.prod ν).restrict E).map Prod.snd ≤ (μ univ) • ν := by
    calc
      _ ≤ (μ.prod ν).map Prod.snd := Measure.map_mono Measure.restrict_le_self measurable_snd
      _ = _ := Measure.map_snd_prod
  exact (Measure.absolutelyContinuous_of_le hd).ae_le (Measure.ae_smul_measure hP _)

theorem gaussian_controlled_incidence_mean_lower (B : Fin h → Space (n+1))
    (hB : ∀ i, ‖B i‖ ≤ 1)
    (μ : Measure (Space (n+1))) (ν : Measure (Sphere (n+1)))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set (Space (n+1) × Sphere (n+1))) (hE : MeasurableSet E)
    {r ρ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hρ : 0 ≤ ρ)
    (hwB : ∀ᵐ (w : Sphere (n+1)) ∂ν, ∀ i, |inner ℝ (w:Space (n+1)) (B i)| ≤ ρ) :
    ENNReal.ofReal ((2:ℝ)^h)*ENNReal.ofReal (gaussianLocalBandConstant n ρ^h)*(μ.prod ν) E ≤
      ∫⁻ A : Fin h → Space (n+1), (∫⁻ z : Space h,
        (gaussianPointSliceMeasure μ A z r).prod (gaussianDirectionSliceMeasure ν A r) E)
        ∂(gaussianRows (n+1) h).restrict (gaussianRowNeighborhood B ((n+1:ℝ)*(2*ρ))) := by
  simp_rw [gaussian_slice_incidence_point_average μ ν E hE _ hr]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hh := gaussian_controlled_direction_mean_lower B hB
    (((μ.prod ν).restrict E).map Prod.snd) hr hrρ hρ (incidence_direction_ae μ ν E hwB)
  rw [Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ,
    Measure.restrict_apply_univ] at hh
  simpa only [mul_assoc] using mul_le_mul_right hh (ENNReal.ofReal ((2:ℝ)^h))

theorem controlled_row_kernel_geometry (e : Space h →ₗᵢ[ℝ] Space (n+1))
    {A : Fin h → Space (n+1)} {ρ : ℝ}
    (hρ : (h:ℝ)*((n+1:ℝ)*(2*ρ)) ≤ 1/2)
    (hA : A ∈ gaussianRowNeighborhood (fun i => e (EuclideanSpace.basisFun (Fin h) ℝ i))
      ((n+1:ℝ)*(2*ρ))) :
    Module.finrank ℝ (gaussianRowMap A).ker = n+1-h ∧
      ∀ x : Space (n+1), ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖ :=
  ⟨row_kernel_finrank A e hA hρ, row_kernel_projection_bound A e hA hρ⟩

end Falconer

end OAI

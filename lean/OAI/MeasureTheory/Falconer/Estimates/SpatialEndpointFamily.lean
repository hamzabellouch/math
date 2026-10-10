import OAI.MeasureTheory.Falconer.Estimates.SpatialEndpoint
import OAI.MeasureTheory.Falconer.Shells.SpatialSharedShell

namespace OAI

/-! # The actual endpoint family in the spatial Fourier shell bound

Spatial frequencies are parameters of bounded modulus-one multipliers.
The original endpoint laws and model masses are unchanged.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate
variable {d : ℕ}

noncomputable def spatialEndpointFamily (μ : Measure (Space d)) (M s : ℝ)
    (b : Space d → Sphere d → ℂ) (p : Space d × (ℝ × Sphere d)) : ℂ :=
  endpointTransform μ M (fun x w => spatialFourierPhase s p.1 x*b x w) p.2.1 p.2.2

theorem spatialEndpointFamily_measurable (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (M s : ℝ) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) : Measurable (spatialEndpointFamily μ M s b) := by
  have hm : Measurable (fun z : (Space d × (ℝ × Sphere d)) × Space d =>
      Complex.exp (Complex.I * (z.1.2.1 : ℂ) * (inner ℝ (z.1.2.2 : Space d) z.2 : ℂ)) *
        (spatialFourierPhase s z.1.1 z.2*b z.2 z.1.2.2)) := by
    apply Measurable.mul
    · fun_prop
    · apply Measurable.mul
      · unfold spatialFourierPhase
        fun_prop
      · exact hb.comp (measurable_snd.prodMk measurable_fst.snd.snd)
  have hi : Measurable (fun p : Space d × (ℝ × Sphere d) =>
      ∫ x, Complex.exp (Complex.I * (p.2.1 : ℂ) *
        (inner ℝ (p.2.2 : Space d) x : ℂ)) *
        (spatialFourierPhase s p.1 x*b x p.2.2) ∂μ) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  exact hi.const_smul (M⁻¹ : ℝ)

theorem spatialEndpointFamily_norm_le (μ : Measure (Space d)) [IsFiniteMeasure μ]
    {M : ℝ} (hM : 0 < M) (s : ℝ) (b : Space d → Sphere d → ℂ)
    {B : ℝ} (hB : ∀ x w, ‖b x w‖ ≤ B) (p : Space d × (ℝ × Sphere d)) :
    ‖spatialEndpointFamily μ M s b p‖ ≤ B*μ.real univ/M := by
  apply endpointTransform_norm_le μ hM _ _ p.2.1 p.2.2
  intro x w
  rw [norm_mul,spatialFourierPhase_norm,one_mul]
  exact hB x w

theorem spatial_endpoint_shared_shell_le
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (s a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbB : ∀ x w, ‖b x w‖ ≤ B) (hcC : ∀ x w, ‖c x w‖ ≤ C)
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) (E : ℝ)
    (hE : ∀ ξ : Space d, independentAngularEnergy a v Ψ
      (fun p => spatialEndpointFamily μ M s b (ξ,p))
      (fun p => spatialEndpointFamily ν P s c (ξ,p)) ≤ E) :
    (2:ℝ)^((d:ℝ)*(v-a)) *
      (∫ r, ‖spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL j)
        (spatialEndpointFamily μ M s b) (spatialEndpointFamily ν P s c) r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (spatialFourierCost (d := d) δ L hδ hL j)^2*E := by
  exact spatial_fourier_shared_shell_le a v Ψ δ L hδ hL j
    (spatialEndpointFamily μ M s b) (spatialEndpointFamily ν P s c)
    (spatialEndpointFamily_measurable μ M s b hb) (spatialEndpointFamily_measurable ν P s c hc)
    (div_nonneg (mul_nonneg hB measureReal_nonneg) hM.le)
    (div_nonneg (mul_nonneg hC measureReal_nonneg) hP.le)
    (spatialEndpointFamily_norm_le μ hM s b hbB)
    (spatialEndpointFamily_norm_le ν hP s c hcC) E hE

end Falconer

end OAI

import OAI.MeasureTheory.Falconer.Shells.FiniteShellIntegrability
import OAI.MeasureTheory.Falconer.Fourier.StationaryFactorShell

namespace OAI

/-! # Source-shell square integrability of normalized stationary factors -/

namespace Falconer
open Set MeasureTheory
variable {d : ℕ}

theorem stationary_factor_shell_sq_integrable {ι : Type*} (S : Finset ι)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P)
    (a v t : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j p q : ι → ℕ) (A E : ι → ℝ) {D h : ℝ} (hD : 1 ≤ D) (hh : 0 ≤ h)
    (hpq : ∀ i ∈ S, p i+q i ≤ 2*j i)
    (hA : ∀ i ∈ S, 0 ≤ A i) (hE : ∀ i ∈ S, 0 ≤ E i)
    (b f : ι → Space d → Sphere d → ℂ)
    (hb : ∀ i ∈ S, Measurable (Function.uncurry (b i)))
    (hf : ∀ i ∈ S, Measurable (Function.uncurry (f i)))
    (hb1 : ∀ i ∈ S, ∀ x w, ‖b i x w‖ ≤ 1)
    (hf1 : ∀ i ∈ S, ∀ x w, ‖f i x w‖ ≤ 1)
    (hregime : ∀ᵐ r ∂PlanarFalconer.sourceAngularShellMeasure v Ψ,
      0 < r*t ∧ D^2 ≤ r*t ∧ r*t ≤ 4*(2:ℝ)^(v-a))
 :
    Integrable (fun r => ‖∑ i ∈ S,
        ((((r*t)^h*((r*t)^(j i))⁻¹*
            ((A i*D^(p i))*(E i*D^(q i)))/(2:ℝ)^((v-a)*h)) : ℝ) : ℂ)*
          spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL (j i))
            (spatialEndpointFamily μ M t (b i))
            (spatialEndpointFamily ν P t (fun x w => star (f i x w))) r‖^2)
      (PlanarFalconer.sourceAngularShellMeasure v Ψ) := by
  have hpow : ((2:ℝ)^(v-a))^h = (2:ℝ)^((v-a)*h) :=
    (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
  apply finite_spatial_shell_sq_integrable S v Ψ δ L hδ hL j
    (fun i => spatialEndpointFamily μ M t (b i))
    (fun i => spatialEndpointFamily ν P t (fun x w => star (f i x w)))
    (fun i hi => spatialEndpointFamily_measurable μ M t (b i) (hb i hi))
    (fun i hi => spatialEndpointFamily_measurable ν P t _
      (continuous_star.measurable.comp (hf i hi)))
    (fun _ => μ.real univ/M) (fun _ => ν.real univ/P)
    (fun _ _ => div_nonneg measureReal_nonneg hM.le)
    (fun _ _ => div_nonneg measureReal_nonneg hP.le)
    (fun i hi z => by simpa only [one_mul] using
      spatialEndpointFamily_norm_le μ hM t (b i) (hb1 i hi) z)
    (fun i hi z => by
      have hr : ∀ x w, ‖star (f i x w)‖ ≤ 1 := by
        intro x w
        simpa only [norm_star] using hf1 i hi x w
      simpa only [one_mul] using
        spatialEndpointFamily_norm_le ν hP t (fun x w => star (f i x w)) hr z)
    _ (fun i => A i*E i*4^h)
  · intro i _
    fun_prop
  · intro i hi
    exact mul_nonneg (mul_nonneg (hA i hi) (hE i hi)) (Real.rpow_nonneg (by norm_num) _)
  · filter_upwards [hregime] with r hr
    intro i hi
    rw [Complex.norm_real,Real.norm_eq_abs,← hpow]
    exact restored_normalized_stationary_coefficient_le (hpq i hi) (hA i hi) (hE i hi)
      hr.1 hD (by positivity) hh hr.2.1 hr.2.2

end Falconer

end OAI

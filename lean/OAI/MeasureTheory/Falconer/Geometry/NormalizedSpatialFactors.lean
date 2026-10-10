import OAI.MeasureTheory.Falconer.Geometry.NormalizedInverseFactors
import OAI.MeasureTheory.Falconer.Estimates.SpatialEndpointFamily

namespace OAI

/-! # Exact restoration of normalized factors under the original endpoint integrals

The positive endpoint sizes are constants in every spatial, spherical and
radial variable. Pulling them through the integrals preserves the original
measures and gives their exact squared cost in the shell estimate.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

variable {d : ℕ}

theorem endpointTransform_const_mul (μ : Measure (Space d)) (M : ℝ)
    (b : Space d → Sphere d → ℂ) (c : ℂ) (r : ℝ) (w : Sphere d) :
    endpointTransform μ M (fun x w => c*b x w) r w =
      c*endpointTransform μ M b r w := by
  unfold endpointTransform
  have he : (fun x => Complex.exp (Complex.I*(r : ℂ)*(inner ℝ (w : Space d) x : ℂ))*
      (c*b x w)) = fun x => c*(Complex.exp
        (Complex.I*(r : ℂ)*(inner ℝ (w : Space d) x : ℂ))*b x w) := by
    funext x
    ring
  rw [he,integral_const_mul,mul_smul_comm]

theorem spatialEndpointFamily_const_mul (μ : Measure (Space d)) (M s : ℝ)
    (b : Space d → Sphere d → ℂ) (c : ℂ) (p : Space d × (ℝ × Sphere d)) :
    spatialEndpointFamily μ M s (fun x w => c*b x w) p =
      c*spatialEndpointFamily μ M s b p := by
  unfold spatialEndpointFamily
  have he : (fun x w => spatialFourierPhase s p.1 x*(c*b x w)) =
      fun x w => c*(spatialFourierPhase s p.1 x*b x w) := by
    funext x w
    ring
  rw [he,endpointTransform_const_mul]

theorem normalizedEndpoint_conj (a : ℝ) (b : Space d → Sphere d → ℂ) :
    normalizedEndpoint a (fun x w => star (b x w)) =
      fun x w => star (normalizedEndpoint a b x w) := by
  funext x w
  simp only [normalizedEndpoint,star_mul',Complex.star_def,Complex.conj_ofReal]

theorem spatialEndpointFamily_normalized (μ : Measure (Space d)) (M s : ℝ)
    {a : ℝ} (ha : 0 < a) (b : Space d → Sphere d → ℂ)
    (p : Space d × (ℝ × Sphere d)) :
    spatialEndpointFamily μ M s b p =
      (a : ℂ)*spatialEndpointFamily μ M s (normalizedEndpoint a b) p := by
  rw [← spatialEndpointFamily_const_mul]
  congr 1
  funext x w
  exact (normalizedEndpoint_restore ha b x w).symm

theorem spatialSharedAmplitude_const_mul (c : Space d → ℂ)
    (U V : Space d × (ℝ × Sphere d) → ℂ) (A E : ℂ) (r : ℝ) :
    spatialSharedAmplitude c (fun z => A*U z) (fun z => E*V z) r =
      (A*star E)*spatialSharedAmplitude c U V r := by
  unfold spatialSharedAmplitude
  have he (w : Sphere d) :
      (fun ξ : Space d => c ξ*((A*U (ξ,(r,w)))*star (E*V (ξ,(r,w))))) =
      fun ξ => (A*star E)*(c ξ*(U (ξ,(r,w))*star (V (ξ,(r,w))))) := by
    funext ξ
    rw [star_mul]
    ring
  simp_rw [he,integral_const_mul]

theorem spatialSharedAmplitude_normalized
    (c : Space d → ℂ) (μ ν : Measure (Space d)) (M P s : ℝ)
    {a e : ℝ} (ha : 0 < a) (he : 0 < e)
    (b f : Space d → Sphere d → ℂ) (r : ℝ) :
    spatialSharedAmplitude c (spatialEndpointFamily μ M s b)
      (spatialEndpointFamily ν P s (fun x w => star (f x w))) r =
    ((a*e : ℝ) : ℂ)*spatialSharedAmplitude c
      (spatialEndpointFamily μ M s (normalizedEndpoint a b))
      (spatialEndpointFamily ν P s (fun x w => star (normalizedEndpoint e f x w))) r := by
  have hb : spatialEndpointFamily μ M s b =
      fun p => (a : ℂ)*spatialEndpointFamily μ M s (normalizedEndpoint a b) p := by
    funext p
    exact spatialEndpointFamily_normalized μ M s ha b p
  have hf : spatialEndpointFamily ν P s (fun x w => star (f x w)) =
      fun p => (e : ℂ)*spatialEndpointFamily ν P s
        (fun x w => star (normalizedEndpoint e f x w)) p := by
    funext p
    simpa only [normalizedEndpoint_conj] using
      spatialEndpointFamily_normalized ν P s he (fun x w => star (f x w)) p
  rw [hb,hf,spatialSharedAmplitude_const_mul]
  simp only [Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul]

theorem spatial_normalized_shared_shell_le
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (s a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    {A E : ℝ} (hA : 0 < A) (hE : 0 < E)
    (b f : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry (normalizedEndpoint A b)))
    (hf : Measurable (Function.uncurry (normalizedEndpoint E f)))
    (hb1 : ∀ x w, ‖normalizedEndpoint A b x w‖ ≤ 1)
    (hf1 : ∀ x w, ‖normalizedEndpoint E f x w‖ ≤ 1)
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) (H : ℝ)
    (hH : ∀ ξ : Space d, independentAngularEnergy a v Ψ
      (fun p => spatialEndpointFamily μ M s (normalizedEndpoint A b) (ξ,p))
      (fun p => spatialEndpointFamily ν P s
        (fun x w => star (normalizedEndpoint E f x w)) (ξ,p)) ≤ H) :
    (2:ℝ)^((d:ℝ)*(v-a)) *
      (∫ r, ‖spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL j)
        (spatialEndpointFamily μ M s b)
        (spatialEndpointFamily ν P s (fun x w => star (f x w))) r‖^2
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ) ≤
      (A*E)^2*(spatialFourierCost (d := d) δ L hδ hL j)^2*H := by
  have hbound := spatial_endpoint_shared_shell_le μ ν hM hP s a v Ψ
    (normalizedEndpoint A b) (fun x w => star (normalizedEndpoint E f x w)) hb
    (continuous_star.measurable.comp hf) (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 1) hb1
    (fun x w => by simpa only [norm_star] using hf1 x w) δ L hδ hL j H hH
  calc
    _ = (A*E)^2*((2:ℝ)^((d:ℝ)*(v-a))*
        (∫ r, ‖spatialSharedAmplitude (spatialFourierCoeff δ L hδ hL j)
          (spatialEndpointFamily μ M s (normalizedEndpoint A b))
          (spatialEndpointFamily ν P s (fun x w => star (normalizedEndpoint E f x w))) r‖^2
          ∂PlanarFalconer.sourceAngularShellMeasure v Ψ)) := by
      simp_rw [spatialSharedAmplitude_normalized _ μ ν M P s hA hE b f,
        norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (mul_pos hA hE),mul_pow]
      rw [integral_const_mul]
      ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound (sq_nonneg (A*E))

end Falconer

end OAI

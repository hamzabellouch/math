import OAI.MeasureTheory.Falconer.Angular.InverseSphereFubini
import OAI.MeasureTheory.Falconer.Estimates.PatchedInverseFactors

namespace OAI

/-! # Integration of the actual finite separated inverse

The original endpoint laws are retained. Each finite angular factor is
integrated through the one-order spatial Fourier identity, with its actual
conjugation convention and no additional integrability assumptions.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate

variable {d : ℕ}

private theorem separated_factor_measurable
    {F : Space d → Space d → ℂ} (hF : Measurable (Function.uncurry F)) :
    Measurable (fun p : Space d × Sphere d => F p.1 p.2) :=
  hF.comp (measurable_fst.prodMk (continuous_subtype_val.measurable.comp measurable_snd))

private theorem separated_sphere_integrable
    (S : SmoothSeparation (Space d) (Space d) (Space d))
    (hmeas : ∀ i : S.index, Measurable (Function.uncurry (S.left i)) ∧
      Measurable (Function.uncurry (S.right i)))
    (B C : S.index → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hbB : ∀ i x (w : Sphere d), ‖S.left i x w‖ ≤ B i)
    (hcC : ∀ i x (w : Sphere d), ‖S.right i x w‖ ≤ C i)
    (r : ℝ) (i : S.index) (z : Space d × Space d) :
    Integrable (fun w : Sphere d =>
      Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
        (S.left i z.1 w*S.right i z.2 w)) (sphereMeasure d) := by
  have hm : Measurable (fun w : Sphere d =>
      Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
        (S.left i z.1 w*S.right i z.2 w)) := by
    apply Measurable.mul
    · fun_prop
    · exact ((separated_factor_measurable (hmeas i).1).comp
        (measurable_const.prodMk measurable_id)).mul
        ((separated_factor_measurable (hmeas i).2).comp
          (measurable_const.prodMk measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable (B i*C i)
  filter_upwards with w
  have he : ‖Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))‖ = 1 := by
    simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  simp only [norm_mul,he,one_mul]
  exact mul_le_mul (hbB i z.1 w) (hcC i z.2 w) (norm_nonneg _) (hB i)

theorem separated_inverse_term_integrable
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (s : ℝ)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s)
    (S : SmoothSeparation (Space d) (Space d) (Space d))
    (hmeas : ∀ i : S.index, Measurable (Function.uncurry (S.left i)) ∧
      Measurable (Function.uncurry (S.right i)))
    (B C : S.index → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hbB : ∀ i x (w : Sphere d), ‖S.left i x w‖ ≤ B i)
    (hcC : ∀ i x (w : Sphere d), ‖S.right i x w‖ ≤ C i) (r : ℝ) :
    Integrable (fun z : Space d × Space d =>
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            S.value z.1 z.2 w ∂sphereMeasure d) (μ.prod ν) := by
  let b := fun i : S.index => fun x (w : Sphere d) => S.left i x w
  let c := fun i : S.index => fun x (w : Sphere d) => star (S.right i x w)
  have hb (i : S.index) : Measurable (Function.uncurry (b i)) :=
    separated_factor_measurable (hmeas i).1
  have hc (i : S.index) : Measurable (Function.uncurry (c i)) :=
    continuous_star.measurable.comp (separated_factor_measurable (hmeas i).2)
  have hc' (i : S.index) (x : Space d) (w : Sphere d) : ‖c i x w‖ ≤ C i := by
    simpa only [c,norm_star] using hcC i x w
  have hi (i : S.index) : Integrable (fun z : Space d × Space d =>
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            (S.left i z.1 w*S.right i z.2 w) ∂sphereMeasure d) (μ.prod ν) := by
    simpa only [b,c,star_star] using spatial_inverse_sphere_term_integrable
      δ hδ j s μ ν hsep (b i) (c i) (hb i) (hc i) (hB i) (hbB i) (hc' i) r
  have he (z : Space d × Space d) :
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        (∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            S.value z.1 z.2 w ∂sphereMeasure d) =
      ∑ i : S.index, (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            (S.left i z.1 w*S.right i z.2 w) ∂sphereMeasure d := by
    simp only [SmoothSeparation.value,Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _ => separated_sphere_integrable S hmeas B C hB hbB hcC r i z),
      Finset.mul_sum]
  simp_rw [he]
  exact integrable_finsetSum Finset.univ (fun i _ => hi i)

theorem separated_sphere_spatial_integration
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ L)
    (M P : ℝ) (S : SmoothSeparation (Space d) (Space d) (Space d))
    (hmeas : ∀ i : S.index, Measurable (Function.uncurry (S.left i)) ∧
      Measurable (Function.uncurry (S.right i)))
    (B C : S.index → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hbB : ∀ i x (w : Sphere d), ‖S.left i x w‖ ≤ B i)
    (hcC : ∀ i x (w : Sphere d), ‖S.right i x w‖ ≤ C i) (r : ℝ) :
    (M⁻¹*P⁻¹) • ∫ z : Space d × Space d,
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            S.value z.1 z.2 w ∂sphereMeasure d ∂μ.prod ν =
    ∑ i : S.index, ∫ w : Sphere d, (∫ ξ : Space d,
      spatialFourierCoeff (d := d) δ L hδ hL j ξ *
        (endpointTransform μ M (fun x w => spatialFourierPhase s ξ x*S.left i x w) r w *
          star (endpointTransform ν P
            (fun x w => spatialFourierPhase s ξ x*star (S.right i x w)) r w)))
      ∂sphereMeasure d := by
  let b := fun i : S.index => fun x (w : Sphere d) => S.left i x w
  let c := fun i : S.index => fun x (w : Sphere d) => star (S.right i x w)
  have hb (i : S.index) : Measurable (Function.uncurry (b i)) :=
    separated_factor_measurable (hmeas i).1
  have hc (i : S.index) : Measurable (Function.uncurry (c i)) :=
    continuous_star.measurable.comp (separated_factor_measurable (hmeas i).2)
  have hc' (i : S.index) (x : Space d) (w : Sphere d) : ‖c i x w‖ ≤ C i := by
    simpa only [c,norm_star] using hcC i x w
  have hi (i : S.index) : Integrable (fun z : Space d × Space d =>
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            (S.left i z.1 w*S.right i z.2 w) ∂sphereMeasure d) (μ.prod ν) := by
    simpa only [b,c,star_star] using spatial_inverse_sphere_term_integrable
      δ hδ j s μ ν (hsep.mono (fun _ hz => hz.1)) (b i) (c i) (hb i) (hc i) (hB i) (hbB i) (hc' i) r
  have he (z : Space d × Space d) :
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        (∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            S.value z.1 z.2 w ∂sphereMeasure d) =
      ∑ i : S.index, (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            (S.left i z.1 w*S.right i z.2 w) ∂sphereMeasure d := by
    simp only [SmoothSeparation.value,Finset.mul_sum]
    rw [integral_finsetSum Finset.univ (fun i _ => separated_sphere_integrable S hmeas B C hB hbB hcC r i z),
      Finset.mul_sum]
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [b,c,star_star] using spatial_inverse_sphere_separation
    δ L hδ hL j hs μ ν hsep M P (b i) (c i) (hb i) (hc i) (hB i) (hbB i) (hc' i) r

theorem separated_inverse_integration
    (m : ℕ) (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ L)
    (M P : ℝ) (S : SmoothSeparation (Space (m+3)) (Space (m+3)) (Space (m+3)))
    (A D : Space (m+3) → Space (m+3) → ℂ)
    (hvalue : ∀ x y (w : Sphere (m+3)),
      localInverseAmplitude m (fun z => A x z*D y z) j w = S.value x y w)
    (hmeas : ∀ i : S.index, Measurable (Function.uncurry (S.left i)) ∧
      Measurable (Function.uncurry (S.right i)))
    (B C : S.index → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hbB : ∀ i x (w : Sphere (m+3)), ‖S.left i x w‖ ≤ B i)
    (hcC : ∀ i x (w : Sphere (m+3)), ‖S.right i x w‖ ≤ C i) (r : ℝ) :
    (M⁻¹*P⁻¹) • ∫ z : Space (m+3) × Space (m+3),
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere (m+3),
          Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            localInverseAmplitude m (fun v => A z.1 v*D z.2 v) j w
          ∂sphereMeasure (m+3) ∂μ.prod ν =
    ∑ i : S.index, ∫ w : Sphere (m+3), (∫ ξ : Space (m+3),
      spatialFourierCoeff (d := m+3) δ L hδ hL j ξ *
        (endpointTransform μ M (fun x w => spatialFourierPhase s ξ x*S.left i x w) r w *
          star (endpointTransform ν P
            (fun x w => spatialFourierPhase s ξ x*star (S.right i x w)) r w)))
      ∂sphereMeasure (m+3) := by
  simp_rw [hvalue]
  exact separated_sphere_spatial_integration δ L hδ hL j hs μ ν hsep M P S hmeas B C hB hbB hcC r

end Falconer

end OAI

import OAI.MeasureTheory.Falconer.Estimates.SpatialEndpoint

namespace OAI

/-! # Original-pair and sphere integration of one inverse term

The spatial inverse power is separated after exchanging the sphere and
original endpoint integrations. All measures on the endpoints remain the
original restrictions; the Fourier multipliers have modulus one.
-/

namespace Falconer
open Set MeasureTheory
open scoped ComplexConjugate
variable {d : ℕ}

theorem spatial_inverse_sphere_joint_integrable
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (s : ℝ)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (hcC : ∀ x w, ‖c x w‖ ≤ C) (r : ℝ) :
    Integrable (fun p : Sphere d × (Space d × Space d) =>
      (↑((dist p.2.1 p.2.2/s)^j)⁻¹ : ℂ) *
        (Complex.exp (Complex.I*((r*inner ℝ (p.1 : Space d) (p.2.1-p.2.2) : ℝ) : ℂ))*
          (b p.2.1 p.1*star (c p.2.2 p.1)))) ((sphereMeasure d).prod (μ.prod ν)) := by
  let K : Sphere d × (Space d × Space d) → ℂ := fun p =>
    (↑((dist p.2.1 p.2.2/s)^j)⁻¹ : ℂ) *
      (Complex.exp (Complex.I*((r*inner ℝ (p.1 : Space d) (p.2.1-p.2.2) : ℝ) : ℂ))*
        (b p.2.1 p.1*star (c p.2.2 p.1)))
  have hK : Measurable K := by
    apply Measurable.mul
    · exact Complex.measurable_ofReal.comp
        (((measurable_snd.fst.dist measurable_snd.snd).div_const s).pow_const j).inv
    · apply Measurable.mul
      · fun_prop
      · exact (hb.comp (measurable_snd.fst.prodMk measurable_fst)).mul
          (continuous_star.measurable.comp (hc.comp (measurable_snd.snd.prodMk measurable_fst)))
  have hbound : ∀ᵐ p ∂(sphereMeasure d).prod (μ.prod ν), ‖K p‖ ≤ (δ^j)⁻¹*(B*C) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hsep] with p hp
    have hp0 : 0 ≤ dist p.2.1 p.2.2/s := (hδ.trans_le hp).le
    have hpower : ((dist p.2.1 p.2.2/s)^j)⁻¹ ≤ (δ^j)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hδ j)
        (pow_le_pow_left₀ hδ.le hp j)
    have hphase : ‖Complex.exp
        (Complex.I*((r*inner ℝ (p.1 : Space d) (p.2.1-p.2.2) : ℝ) : ℂ))‖ = 1 := by
      simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
    simp only [K,norm_mul,hphase,one_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hp0 j))]
    exact mul_le_mul hpower (mul_le_mul (hbB _ _) (hcC _ _) (norm_nonneg _) hB)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (inv_nonneg.mpr (pow_nonneg hδ.le j))
  exact Integrable.of_bound hK.aestronglyMeasurable ((δ^j)⁻¹*(B*C)) hbound

theorem spatial_inverse_sphere_term_integrable
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (s : ℝ)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s)
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (hcC : ∀ x w, ‖c x w‖ ≤ C) (r : ℝ) :
    Integrable (fun z : Space d × Space d =>
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            (b z.1 w*star (c z.2 w)) ∂sphereMeasure d) (μ.prod ν) := by
  simpa only [integral_const_mul] using
    (spatial_inverse_sphere_joint_integrable δ hδ j s μ ν hsep b c hb hc hB hbB hcC r).integral_prod_right

theorem spatial_inverse_sphere_separation
    (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L) (j : ℕ) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ L)
    (M P : ℝ) (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (hcC : ∀ x w, ‖c x w‖ ≤ C) (r : ℝ) :
    (M⁻¹*P⁻¹) • ∫ z : Space d × Space d,
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            (b z.1 w*star (c z.2 w)) ∂sphereMeasure d ∂μ.prod ν =
    ∫ w : Sphere d, (∫ ξ : Space d, spatialFourierCoeff (d := d) δ L hδ hL j ξ *
      (endpointTransform μ M (fun x w => spatialFourierPhase s ξ x*b x w) r w *
        star (endpointTransform ν P (fun x w => spatialFourierPhase s ξ x*c x w) r w)))
      ∂sphereMeasure d := by
  let K : Sphere d × (Space d × Space d) → ℂ := fun p =>
    (↑((dist p.2.1 p.2.2/s)^j)⁻¹ : ℂ) *
      (Complex.exp (Complex.I*((r*inner ℝ (p.1 : Space d) (p.2.1-p.2.2) : ℝ) : ℂ))*
        (b p.2.1 p.1*star (c p.2.2 p.1)))
  have hi : Integrable K ((sphereMeasure d).prod (μ.prod ν)) :=
    spatial_inverse_sphere_joint_integrable δ hδ j s μ ν
      (hsep.mono fun _ hz => hz.1) b c hb hc hB hbB hcC r
  have hswap := (integral_integral_swap (f := fun w z => K (w,z)) hi).symm
  have he : (∫ z : Space d × Space d,
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere d,
          Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
            (b z.1 w*star (c z.2 w)) ∂sphereMeasure d ∂μ.prod ν) =
        ∫ w : Sphere d, ∫ z : Space d × Space d, K (w,z) ∂μ.prod ν ∂sphereMeasure d := by
    simpa only [K,integral_const_mul] using hswap
  rw [he,← integral_smul]
  apply integral_congr_ae
  filter_upwards with w
  exact spatial_inverse_endpoint_separation δ L hδ hL j hs μ ν hsep M P b c hb hc hB hbB hcC r w

end Falconer

end OAI

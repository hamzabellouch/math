import OAI.MeasureTheory.Falconer.Angular.FourPointCaps
import OAI.MeasureTheory.Falconer.Angular.VectorSphereKernel

namespace OAI

/-! # Exact original-point spherical kernel before the far decomposition -/

namespace Falconer
open Set MeasureTheory

theorem expandedCapTerm_spatial_kernel {d : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)]
    (v₁ v₂ : X → Space d) (hv₁ : Measurable v₁) (hv₂ : Measurable v₂)
    (b₁ b₂ : X → Sphere d → ℂ)
    (hb₁ : Measurable (Function.uncurry b₁)) (hb₂ : Measurable (Function.uncurry b₂))
    {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hbound₁ : ∀ x w, ‖b₁ x w‖ ≤ B₁) (hbound₂ : ∀ x w, ‖b₂ x w‖ ≤ B₂) :
    expandedCapTerm μ v Ψ v₁ v₂ b₁ b₂ =
      ∫ x, ∫ r,
        (∫ w, sphereOscillator r (v₁ x) w*b₁ x w ∂sphereMeasure d)*
        (∫ w, sphereOscillator r (v₂ x) w*b₂ x w ∂sphereMeasure d)
        ∂PlanarFalconer.sourceAngularShellMeasure v Ψ ∂μ := by
  have hm (u : X → Space d) (hu : Measurable u) (b : X → Sphere d → ℂ)
      (hb : Measurable (Function.uncurry b)) :
      Measurable (fun p : ℝ × X => ∫ w, sphereOscillator p.1 (u p.2) w*b p.2 w
        ∂sphereMeasure d) := by
    have hh : Measurable (fun p : (ℝ × X) × Sphere d =>
        sphereOscillator p.1.1 (u p.1.2) p.2*b p.1.2 p.2) := by
      apply Measurable.mul
      · unfold sphereOscillator
        fun_prop
      · exact hb.comp (measurable_fst.snd.prodMk measurable_snd)
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  have hbound (u : X → Space d) (b : X → Sphere d → ℂ) (C : ℝ)
      (hb : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (x : X) :
      ‖∫ w, sphereOscillator r (u x) w*b x w ∂sphereMeasure d‖ ≤
        C*(sphereMeasure d).real univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards with w
    simpa only [norm_mul,sphereOscillator_norm,one_mul] using hb x w
  let G : ℝ × X → ℂ := fun p =>
    (∫ w, sphereOscillator p.1 (v₁ p.2) w*b₁ p.2 w ∂sphereMeasure d)*
    (∫ w, sphereOscillator p.1 (v₂ p.2) w*b₂ p.2 w ∂sphereMeasure d)
  have hG : Measurable G := (hm v₁ hv₁ b₁ hb₁).mul (hm v₂ hv₂ b₂ hb₂)
  have hi : Integrable G ((PlanarFalconer.sourceAngularShellMeasure v Ψ).prod μ) := by
    apply Integrable.of_bound hG.aestronglyMeasurable
      ((B₁*(sphereMeasure d).real univ)*(B₂*(sphereMeasure d).real univ))
    filter_upwards with p
    exact (norm_mul _ _).le.trans (mul_le_mul (hbound v₁ b₁ B₁ hbound₁ p.1 p.2)
      (hbound v₂ b₂ B₂ hbound₂ p.1 p.2) (norm_nonneg _) (by positivity))
  calc
    _ = ∫ r, ∫ x, G (r,x) ∂μ ∂PlanarFalconer.sourceAngularShellMeasure v Ψ := by
      apply integral_congr_ae
      filter_upwards with r
      exact angular_pair_spatial_swap μ r v₁ v₂ hv₁ hv₂ b₁ b₂ hb₁ hb₂ hB₁ hB₂ hbound₁ hbound₂
    _ = _ := integral_integral_swap hi

theorem independentAngularEnergy_eq_capCrossTerm {d : ℕ}
    (μ ν : Measure (Space d)) (M P a v : ℝ) (Ψ : ℝ → ℝ)
    (b c : Space d → Sphere d → ℂ) :
    (independentAngularEnergy a v Ψ
      (fun z => endpointTransform μ M b z.1 z.2)
      (fun z => endpointTransform ν P c z.1 z.2) : ℂ) =
    ((2:ℝ)^((d:ℝ)*(v-a))) •
      endpointCapCrossTerm μ μ ν ν M M P P v Ψ b b c c (fun _ => 1) (fun _ => 1) := by
  unfold independentAngularEnergy endpointCapCrossTerm
  rw [Complex.ofReal_mul, Complex.real_smul]
  congr 1
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with r
  unfold sphereMoment
  rw [← sphere_product_square_integral]
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Complex.ofReal_one,one_mul,Complex.star_def,Complex.mul_conj',Complex.ofReal_pow]

end Falconer

end OAI

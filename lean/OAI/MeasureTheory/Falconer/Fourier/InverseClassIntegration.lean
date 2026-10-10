import OAI.MeasureTheory.Falconer.Estimates.InverseClassExpansion
import OAI.MeasureTheory.Falconer.Angular.InverseSphereFubini
import OAI.MeasureTheory.Falconer.Estimates.SpatialEndpointFamily

namespace OAI

/-! # Original-pair integration of the exact inverse symbol family

The finite factors are the actual output symbols. The original endpoint
measures, both normalizing masses, and every descriptor remain explicit.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

private theorem bounded_sphere_phase_integrable {d : ℕ}
    (b c : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) (hc : Measurable (Function.uncurry c))
    {B C : ℝ} (hB : 0 ≤ B) (hbB : ∀ x w, ‖b x w‖ ≤ B)
    (hcC : ∀ x w, ‖c x w‖ ≤ C) (r : ℝ) (z : Space d × Space d) :
    Integrable (fun w : Sphere d =>
      Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
        (b z.1 w*c z.2 w)) (sphereMeasure d) := by
  have hm : Measurable (fun w : Sphere d =>
      Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))*
        (b z.1 w*c z.2 w)) := by
    apply Measurable.mul
    · fun_prop
    · exact (hb.comp (measurable_const.prodMk measurable_id)).mul
        (hc.comp (measurable_const.prodMk measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable (B*C)
  filter_upwards with w
  have he : ‖Complex.exp (Complex.I*((r*inner ℝ (w : Space d) (z.1-z.2) : ℝ) : ℂ))‖ = 1 := by
    simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  rw [norm_mul,he,one_mul,norm_mul]
  exact mul_le_mul (hbB z.1 w) (hcC z.2 w) (norm_nonneg _) hB

namespace DescriptorInverseSymbols
variable {m KL KR L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) KL L F D}
  {g : DescriptorJetSymbol (m+1) KR L G D} {j R : ℕ} {A B : ℝ}

noncomputable def coefficient (_T : DescriptorInverseSymbols f g j R A B)
    (N : ℕ) (σ Af Ag U V : ℝ) (a : DescriptorInverseIndex f g j) : ℝ :=
  descriptorInverseWeight f g j N σ a * (U*A) * (V*B) * Af⁻¹ * Ag⁻¹

theorem coefficient_abs_le (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (N : ℕ) (σ Af Ag U V : ℝ) {E : ℝ}
    (hE : 1 ≤ E) (hDE : D ≤ E)
    (hF : ∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (hG : ∀ b ∈ G, (descriptorMaskRadius N σ b)⁻¹ ≤ E)
    (a : DescriptorInverseIndex f g j) :
    |T.coefficient N σ Af Ag U V a| ≤
      E^(2*j) * |U*A| * |V*B| * |Af⁻¹| * |Ag⁻¹| := by
  calc
    _ = descriptorInverseWeight f g j N σ a * |U*A| * |V*B| * |Af⁻¹| * |Ag⁻¹| := by
      simp only [coefficient,abs_mul,
        abs_of_nonneg (descriptorInverseWeight_nonneg f g hD j N σ a)]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (descriptorInverseWeight_le f g hD j N σ hE hDE hF hG a) (abs_nonneg (U*A)))
          (abs_nonneg (V*B))) (abs_nonneg (Af⁻¹))) (abs_nonneg (Ag⁻¹))

theorem integration (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U V : ℝ} (hU : 0 < U) (hV : 0 < V)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    (M P r : ℝ) :
    (M⁻¹*P⁻¹) • ∫ z : Space (m+3) × Space (m+3),
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere (m+3),
          Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            localInverseAmplitude m
              (fun t => f.ambient Q ρ profile N σ J i S Af z.1 t *
                g.ambient Q ρ profile N σ J i S Ag z.2 t) j w
          ∂sphereMeasure (m+3) ∂μ.prod ν =
      ∑ a : DescriptorInverseIndex f g j, (T.coefficient N σ Af Ag U V a : ℂ) *
        spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW j)
          (spatialEndpointFamily μ M s ((T.left a).value Q ρ profile N σ J i S U))
          (spatialEndpointFamily ν P s
            (fun x w => star ((T.right a).value Q ρ profile N σ J i S V x w))) r := by
  let b := fun a : DescriptorInverseIndex f g j => (T.left a).value Q ρ profile N σ J i S U
  let c := fun a : DescriptorInverseIndex f g j => (T.right a).value Q ρ profile N σ J i S V
  let α := fun a : DescriptorInverseIndex f g j => (T.coefficient N σ Af Ag U V a : ℂ)
  let Z := fun (a : DescriptorInverseIndex f g j) (z : Space (m+3) × Space (m+3)) =>
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w) ∂sphereMeasure (m+3)
  let C₁ := (descriptorJetBound (m+3) (KL+2*j))^(KL+2*j)*U⁻¹
  let C₂ := (descriptorJetBound (m+3) (KR+2*j))^(KR+2*j)*V⁻¹
  have hC₁ : 0 ≤ C₁ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hU.le)
  have hb (a : DescriptorInverseIndex f g j) : Measurable (Function.uncurry (b a)) :=
    (T.left a).value_measurable Q ρ profile N σ J i S U
  have hc (a : DescriptorInverseIndex f g j) : Measurable (Function.uncurry (c a)) :=
    (T.right a).value_measurable Q ρ profile N σ J i S V
  have hbB (a : DescriptorInverseIndex f g j) (x) (w) : ‖b a x w‖ ≤ C₁ :=
    (T.left a).value_norm_le Q ρ profile N σ J i S hF hU x w
  have hcC (a : DescriptorInverseIndex f g j) (x) (w) : ‖c a x w‖ ≤ C₂ :=
    (T.right a).value_norm_le Q ρ profile N σ J i S hG hV x w
  have hi (a : DescriptorInverseIndex f g j) : Integrable (Z a) (μ.prod ν) := by
    simpa only [Z,star_star] using spatial_inverse_sphere_term_integrable δ hδ j s μ ν
      (hsep.mono fun _ hz => hz.1) (b a) (fun x w => star (c a x w))
      (hb a) (continuous_star.measurable.comp (hc a)) hC₁ (hbB a)
      (fun x w => (norm_star _).le.trans (hcC a x w)) r
  have hsphere (a : DescriptorInverseIndex f g j) (z : Space (m+3) × Space (m+3)) :
      Integrable (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w)) (sphereMeasure (m+3)) :=
    bounded_sphere_phase_integrable (b a) (c a) (hb a) (hc a) hC₁ (hbB a) (hcC a) r z
  have he (z : Space (m+3) × Space (m+3)) :
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        (∫ w : Sphere (m+3),
          Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            localInverseAmplitude m
              (fun t => f.ambient Q ρ profile N σ J i S Af z.1 t *
                g.ambient Q ρ profile N σ J i S Ag z.2 t) j w
          ∂sphereMeasure (m+3)) = ∑ a : DescriptorInverseIndex f g j, α a*Z a z := by
    have hf : (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          localInverseAmplitude m
            (fun t => f.ambient Q ρ profile N σ J i S Af z.1 t *
              g.ambient Q ρ profile N σ J i S Ag z.2 t) j w) =
        fun w : Sphere (m+3) => ∑ a : DescriptorInverseIndex f g j, α a*
          (Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            (b a z.1 w*c a z.2 w)) := by
      funext w
      rw [T.expansion hD hA hB Q ρ profile N σ J i S Af Ag hU hV]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      change _*(α a*(b a z.1 w*c a z.2 w)) = _
      ring
    rw [hf,integral_finsetSum Finset.univ (fun a _ => (hsphere a z).const_mul (α a))]
    simp only [integral_const_mul,Finset.mul_sum,Z]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun a _ => (hi a).const_mul (α a)),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_const_mul]
  have hsep' := spatial_inverse_sphere_separation δ W hδ hW j hs μ ν hsep M P
    (b a) (fun x w => star (c a x w)) (hb a) (continuous_star.measurable.comp (hc a))
    hC₁ (hbB a) (fun x w => (norm_star _).le.trans (hcC a x w)) r
  simp only [star_star] at hsep'
  calc
    _ = α a*((M⁻¹*P⁻¹) • ∫ z, Z a z ∂μ.prod ν) := by
      simp only [Complex.real_smul]; ring
    _ = _ := by rw [hsep']; rfl

end DescriptorInverseSymbols
end Falconer

end OAI

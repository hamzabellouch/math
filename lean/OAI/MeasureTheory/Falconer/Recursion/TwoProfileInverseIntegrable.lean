import OAI.MeasureTheory.Falconer.Fourier.TwoProfileInverseIntegration
import OAI.MeasureTheory.Falconer.Fourier.ScaledInverseIntegration

namespace OAI

/-! # Integrability of the two-profile original inverse family -/

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
variable {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
  {f : DescriptorJetSymbol (m+1) K L F D}
  {g : DescriptorJetSymbol (m+1) K L G D} {j R : ℕ} {A B : ℝ}

noncomputable def twoProfilePairIntegral (_T : DescriptorInverseSymbols f g j R A B)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (Af Ag s : ℝ) (μ ν : Measure (Space (m+3))) (M P r : ℝ) : ℂ :=
  (M⁻¹*P⁻¹) • ∫ z : Space (m+3) × Space (m+3),
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          localInverseAmplitude m
            (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
              g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) j w
        ∂sphereMeasure (m+3) ∂μ.prod ν

theorem two_profile_original_term_integrable (T : DescriptorInverseSymbols f g j R A B)
    (hD : 0 < D) (hA : 0 < A) (hB : 0 < B)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (r : ℝ) :
    Integrable (scaledInverseTerm m j s r
      (fun x y z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
        g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z)) (μ.prod ν) := by
  let b := fun a : DescriptorInverseIndex f g j => (T.left a).value Q₁ ρ₁ profile₁ N σ J i S₁ U
  let c := fun a : DescriptorInverseIndex f g j => (T.right a).value Q₂ ρ₂ profile₂ N σ J i S₂ U
  let α := fun a : DescriptorInverseIndex f g j => (T.coefficient N σ Af Ag U U a : ℂ)
  let Z := fun (a : DescriptorInverseIndex f g j) (z : Space (m+3) × Space (m+3)) =>
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w) ∂sphereMeasure (m+3)
  let C₀ := (descriptorJetBound (m+3) (K+2*j))^(K+2*j)*U⁻¹
  have hC₀ : 0 ≤ C₀ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hU.le)
  have hb (a : DescriptorInverseIndex f g j) : Measurable (Function.uncurry (b a)) :=
    (T.left a).value_measurable Q₁ ρ₁ profile₁ N σ J i S₁ U
  have hc (a : DescriptorInverseIndex f g j) : Measurable (Function.uncurry (c a)) :=
    (T.right a).value_measurable Q₂ ρ₂ profile₂ N σ J i S₂ U
  have hbB (a : DescriptorInverseIndex f g j) (x) (w) : ‖b a x w‖ ≤ C₀ :=
    (T.left a).value_norm_le Q₁ ρ₁ profile₁ N σ J i S₁ hF hU x w
  have hcC (a : DescriptorInverseIndex f g j) (x) (w) : ‖c a x w‖ ≤ C₀ :=
    (T.right a).value_norm_le Q₂ ρ₂ profile₂ N σ J i S₂ hG hU x w
  have hi (a : DescriptorInverseIndex f g j) : Integrable (Z a) (μ.prod ν) := by
    simpa only [Z,star_star] using spatial_inverse_sphere_term_integrable δ hδ j s μ ν
      hsep (b a) (fun x w => star (c a x w))
      (hb a) (continuous_star.measurable.comp (hc a)) hC₀ (hbB a)
      (fun x w => (norm_star _).le.trans (hcC a x w)) r
  have hsphere (a : DescriptorInverseIndex f g j) (z : Space (m+3) × Space (m+3)) :
      Integrable (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w)) (sphereMeasure (m+3)) :=
    bounded_sphere_phase_integrable (b a) (c a) (hb a) (hc a) hC₀ (hbB a) (hcC a) r z
  have he : scaledInverseTerm m j s r
      (fun x y z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
        g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z) =
      fun z => ∑ a : DescriptorInverseIndex f g j, α a*Z a z := by
    funext z
    unfold scaledInverseTerm
    have hf : (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          localInverseAmplitude m
            (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
              g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) j w) =
        fun w : Sphere (m+3) => ∑ a : DescriptorInverseIndex f g j, α a*
          (Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            (b a z.1 w*c a z.2 w)) := by
      funext w
      rw [T.two_profile_expansion hD hA hB Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ Af Ag hU hU]
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
  rw [he]
  exact integrable_finsetSum _ (fun a _ => (hi a).const_mul (α a))

end DescriptorInverseSymbols

theorem two_profile_scaled_inverse_integrable {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D} (k R : ℕ)
    (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D) (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (r : ℝ) :
    Integrable (fun z : Space (m+3) × Space (m+3) =>
      scaledWeightedInverseSum m k s r (z.1-z.2)
        (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
          g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t)) (μ.prod ν) := by
  let V := fun x y z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
    g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z
  have hi (j : Fin (k+1)) : Integrable (scaledInverseTerm m j.val s r V) (μ.prod ν) :=
    (T j).two_profile_original_term_integrable hD (hA j) (hB j) Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hF hG
      Af Ag hU δ hδ s μ ν hsep r
  have hs : Integrable (fun z => ∑ j ∈ Finset.range (k+1),
      (((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^j)⁻¹ : ℝ) : ℂ)*
        scaledInverseTerm m j s r V z) (μ.prod ν) := by
    apply integrable_finsetSum
    intro j hj
    exact (hi ⟨j,Finset.mem_range.mp hj⟩).const_mul _
  apply hs.congr
  filter_upwards with z
  exact (scaledWeightedInverseSum_eq_terms m k s r V z).symm

theorem two_profile_scaled_inverse_integration {m K L : ℕ} {F G : Finset PolicyDescriptor} {D : ℝ}
    {f : DescriptorJetSymbol (m+1) K L F D}
    {g : DescriptorJetSymbol (m+1) K L G D} (k R : ℕ)
    (A B : Fin (k+1) → ℝ)
    (T : (j : Fin (k+1)) → DescriptorInverseSymbols f g j.val R (A j) (B j))
    (hD : 0 < D) (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
    (Q₁ Q₂ : DyadicCube (m+3)) (ρ₁ ρ₂ : Measure (Space (m+3))) (profile₁ profile₂ : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S₁ S₂ : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S₁ b, ∀ z ∈ S₁ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S₂ b, ∀ z ∈ S₂ b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (Af Ag : ℝ) {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (M P r : ℝ) :
    (M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
      scaledWeightedInverseSum m k s r (z.1-z.2)
        (fun t => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af z.1 t *
          g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag z.2 t) ∂μ.prod ν) =
      ∑ j : Fin (k+1), (((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^j.val)⁻¹ : ℝ) : ℂ)*
        (T j).twoProfilePairIntegral Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ Af Ag s μ ν M P r := by
  let V := fun x y z => f.ambient Q₁ ρ₁ profile₁ N σ J i S₁ Af x z *
    g.ambient Q₂ ρ₂ profile₂ N σ J i S₂ Ag y z
  have hi (j : Fin (k+1)) : Integrable (scaledInverseTerm m j.val s r V) (μ.prod ν) :=
    (T j).two_profile_original_term_integrable hD (hA j) (hB j) Q₁ Q₂ ρ₁ ρ₂ profile₁ profile₂ N σ J i S₁ S₂ hF hG
      Af Ag hU δ hδ s μ ν hsep r
  change (M⁻¹*P⁻¹) • (∫ z, scaledWeightedInverseSum m k s r (z.1-z.2) (V z.1 z.2) ∂μ.prod ν) = _
  simp_rw [scaledWeightedInverseSum_eq_terms,← Fin.sum_univ_eq_sum_range]
  rw [integral_finsetSum Finset.univ (fun j _ => (hi j).const_mul _),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,← mul_smul_comm]
  rfl

end Falconer

end OAI

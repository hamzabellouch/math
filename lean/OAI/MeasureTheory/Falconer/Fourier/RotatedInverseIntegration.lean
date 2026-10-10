import OAI.MeasureTheory.Falconer.Estimates.RotatedInverseExpansion
import OAI.MeasureTheory.Falconer.Estimates.RotatedWeightedInverse
import OAI.MeasureTheory.Falconer.Fourier.InverseClassIntegration

namespace OAI

/-! # Integration of the rotated finite inverse on the original pair laws -/

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

namespace RotatedRootSymbols
variable {m j L : ℕ} {F : Finset PolicyDescriptor}
  {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} {A : ℝ}

theorem integration (H : RotatedRootSymbols m j L F T A) (hA : 0 < A)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) {s : ℝ} (hs : 0 < s)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s ∧ dist z.1 z.2/s ≤ W)
    (M P r : ℝ) :
    (M⁻¹*P⁻¹) • ∫ z : Space (m+3) × Space (m+3),
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        ∫ w : Sphere (m+3),
          Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            rotatedInverseAmplitude m T
              (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) j w
          ∂sphereMeasure (m+3) ∂μ.prod ν =
      ∑ a : RootInverseIndex m j F, ((rootInverseWeight m j F N σ a*(U*A)*U : ℝ) : ℂ) *
        spatialSharedAmplitude (spatialFourierCoeff δ W hδ hW j)
          (spatialEndpointFamily μ M s ((H.left a).value Q ρ profile N σ J i S U))
          (spatialEndpointFamily ν P s
            (fun x w => star ((H.right a).value Q ρ profile N σ J i S U x w))) r := by
  let b := fun a : RootInverseIndex m j F => (H.left a).value Q ρ profile N σ J i S U
  let c := fun a : RootInverseIndex m j F => (H.right a).value Q ρ profile N σ J i S U
  let α := fun a : RootInverseIndex m j F => ((rootInverseWeight m j F N σ a*(U*A)*U : ℝ) : ℂ)
  let Z := fun (a : RootInverseIndex m j F) (z : Space (m+3) × Space (m+3)) =>
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w) ∂sphereMeasure (m+3)
  let C₁ := (descriptorJetBound (m+3) (2*j))^(2*j)*U⁻¹
  let C₂ := (descriptorJetBound (m+3) (2*j))^(2*j)*U⁻¹
  have hC₁ : 0 ≤ C₁ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hU.le)
  have hb (a : RootInverseIndex m j F) : Measurable (Function.uncurry (b a)) :=
    (H.left a).value_measurable Q ρ profile N σ J i S U
  have hc (a : RootInverseIndex m j F) : Measurable (Function.uncurry (c a)) :=
    (H.right a).value_measurable Q ρ profile N σ J i S U
  have hbB (a : RootInverseIndex m j F) (x) (w) : ‖b a x w‖ ≤ C₁ :=
    (H.left a).value_norm_le Q ρ profile N σ J i S hF hU x w
  have hcC (a : RootInverseIndex m j F) (x) (w) : ‖c a x w‖ ≤ C₂ :=
    (H.right a).value_norm_le Q ρ profile N σ J i S hF hU x w
  have hi (a : RootInverseIndex m j F) : Integrable (Z a) (μ.prod ν) := by
    simpa only [Z,star_star] using spatial_inverse_sphere_term_integrable δ hδ j s μ ν
      (hsep.mono fun _ hz => hz.1) (b a) (fun x w => star (c a x w))
      (hb a) (continuous_star.measurable.comp (hc a)) hC₁ (hbB a)
      (fun x w => (norm_star _).le.trans (hcC a x w)) r
  have hsphere (a : RootInverseIndex m j F) (z : Space (m+3) × Space (m+3)) :
      Integrable (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w)) (sphereMeasure (m+3)) :=
    bounded_sphere_phase_integrable (b a) (c a) (hb a) (hc a) hC₁ (hbB a) (hcC a) r z
  have he (z : Space (m+3) × Space (m+3)) :
      (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
        (∫ w : Sphere (m+3),
          Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            rotatedInverseAmplitude m T
              (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) j w
          ∂sphereMeasure (m+3)) = ∑ a : RootInverseIndex m j F, α a*Z a z := by
    have hf : (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          rotatedInverseAmplitude m T
            (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) j w) =
        fun w : Sphere (m+3) => ∑ a : RootInverseIndex m j F, α a*
          (Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            (b a z.1 w*c a z.2 w)) := by
      funext w
      rw [H.expansion hA Q ρ profile N σ J i S hU]
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

theorem original_term_integrable (H : RotatedRootSymbols m j L F T A) (hA : 0 < A)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (r : ℝ) :
    Integrable (rotatedScaledInverseTerm m j T s r
      (descriptorPairAmplitude Q ρ profile N σ J i F S)) (μ.prod ν) := by
  let b := fun a : RootInverseIndex m j F => (H.left a).value Q ρ profile N σ J i S U
  let c := fun a : RootInverseIndex m j F => (H.right a).value Q ρ profile N σ J i S U
  let α := fun a : RootInverseIndex m j F => ((rootInverseWeight m j F N σ a*(U*A)*U : ℝ) : ℂ)
  let Z := fun (a : RootInverseIndex m j F) (z : Space (m+3) × Space (m+3)) =>
    (↑((dist z.1 z.2/s)^j)⁻¹ : ℂ) *
      ∫ w : Sphere (m+3),
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w) ∂sphereMeasure (m+3)
  let C₀ := (descriptorJetBound (m+3) (2*j))^(2*j)*U⁻¹
  have hC₀ : 0 ≤ C₀ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hU.le)
  have hb (a : RootInverseIndex m j F) : Measurable (Function.uncurry (b a)) :=
    (H.left a).value_measurable Q ρ profile N σ J i S U
  have hc (a : RootInverseIndex m j F) : Measurable (Function.uncurry (c a)) :=
    (H.right a).value_measurable Q ρ profile N σ J i S U
  have hbB (a : RootInverseIndex m j F) (x) (w) : ‖b a x w‖ ≤ C₀ :=
    (H.left a).value_norm_le Q ρ profile N σ J i S hF hU x w
  have hcC (a : RootInverseIndex m j F) (x) (w) : ‖c a x w‖ ≤ C₀ :=
    (H.right a).value_norm_le Q ρ profile N σ J i S hF hU x w
  have hi (a : RootInverseIndex m j F) : Integrable (Z a) (μ.prod ν) := by
    simpa only [Z,star_star] using spatial_inverse_sphere_term_integrable δ hδ j s μ ν
      hsep (b a) (fun x w => star (c a x w))
      (hb a) (continuous_star.measurable.comp (hc a)) hC₀ (hbB a)
      (fun x w => (norm_star _).le.trans (hcC a x w)) r
  have hsphere (a : RootInverseIndex m j F) (z : Space (m+3) × Space (m+3)) :
      Integrable (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          (b a z.1 w*c a z.2 w)) (sphereMeasure (m+3)) :=
    bounded_sphere_phase_integrable (b a) (c a) (hb a) (hc a) hC₀ (hbB a) (hcC a) r z
  have he : rotatedScaledInverseTerm m j T s r
      (descriptorPairAmplitude Q ρ profile N σ J i F S) =
      fun z => ∑ a : RootInverseIndex m j F, α a*Z a z := by
    funext z
    unfold rotatedScaledInverseTerm
    have hf : (fun w : Sphere (m+3) =>
        Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
          rotatedInverseAmplitude m T
            (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) j w) =
        fun w : Sphere (m+3) => ∑ a : RootInverseIndex m j F, α a*
          (Complex.exp (Complex.I*((r*inner ℝ (w : Space (m+3)) (z.1-z.2) : ℝ) : ℂ))*
            (b a z.1 w*c a z.2 w)) := by
      funext w
      rw [H.expansion hA Q ρ profile N σ J i S hU]
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

end RotatedRootSymbols

theorem rotated_inverse_jet_integrable {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (hA : ∀ j, 0 < A j)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (r : ℝ) :
    Integrable (fun z : Space (m+3) × Space (m+3) =>
      rotatedScaledWeightedInverseSum m k T s r (z.1-z.2)
        (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2)) (μ.prod ν) := by
  let V := descriptorPairAmplitude Q ρ profile N σ J i F S
  have hi (j : Fin (k+1)) : Integrable (rotatedScaledInverseTerm m j.val T s r V) (μ.prod ν) :=
    (H j).original_term_integrable (hA j) Q ρ profile N σ J i S hF hU δ hδ s μ ν hsep r
  have hs : Integrable (fun z => ∑ j ∈ Finset.range (k+1),
      (((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^j)⁻¹ : ℝ) : ℂ)*
        rotatedScaledInverseTerm m j T s r V z) (μ.prod ν) := by
    apply integrable_finsetSum
    intro j hj
    exact (hi ⟨j,Finset.mem_range.mp hj⟩).const_mul _
  apply hs.congr
  filter_upwards with z
  exact (rotatedScaledWeightedInverseSum_eq_terms m k T s r V z).symm

theorem rotated_inverse_jet_integration {m L : ℕ} {F : Finset PolicyDescriptor}
    {T : Space (m+3) ≃ₗᵢ[ℝ] Space (m+3)} (k : ℕ)
    (A : Fin (k+1) → ℝ)
    (H : (j : Fin (k+1)) → RotatedRootSymbols m j.val L F T (A j))
    (hA : ∀ j, 0 < A j)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {U : ℝ} (hU : 0 < U)
    (δ : ℝ) (hδ : 0 < δ) (s : ℝ)
    (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hsep : ∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2/s) (M P r : ℝ) :
    (M⁻¹*P⁻¹) • (∫ z : Space (m+3) × Space (m+3),
      rotatedScaledWeightedInverseSum m k T s r (z.1-z.2)
        (descriptorPairAmplitude Q ρ profile N σ J i F S z.1 z.2) ∂μ.prod ν) =
      ∑ j : Fin (k+1), (((r*s)^(((m+2:ℕ):ℝ)/2)*((r*s)^j.val)⁻¹ : ℝ) : ℂ)*
        ((M⁻¹*P⁻¹) • ∫ z : Space (m+3) × Space (m+3),
          rotatedScaledInverseTerm m j.val T s r
            (descriptorPairAmplitude Q ρ profile N σ J i F S) z ∂μ.prod ν) := by
  let V := descriptorPairAmplitude Q ρ profile N σ J i F S
  have hi (j : Fin (k+1)) : Integrable (rotatedScaledInverseTerm m j.val T s r V) (μ.prod ν) :=
    (H j).original_term_integrable (hA j) Q ρ profile N σ J i S hF hU δ hδ s μ ν hsep r
  change (M⁻¹*P⁻¹) • (∫ z, rotatedScaledWeightedInverseSum m k T s r (z.1-z.2) (V z.1 z.2) ∂μ.prod ν) = _
  simp_rw [rotatedScaledWeightedInverseSum_eq_terms,← Fin.sum_univ_eq_sum_range]
  rw [integral_finsetSum Finset.univ (fun j _ => (hi j).const_mul _),Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul,← mul_smul_comm]

end Falconer

end OAI

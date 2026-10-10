import OAI.MeasureTheory.Falconer.Angular.RetainedSmallSphere
import OAI.MeasureTheory.Falconer.Fourier.JetStateFarExpansion

namespace OAI

/-! # Noncomparable radial decay with the original descriptor amplitudes

The larger displacement uses the finite stationary expansion. The smaller
one remains its exact sphere integral, with every original mask retained.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem DescriptorJetSymbol.single_radial_support {m K L : ℕ}
    {F : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F D)
    (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3))) (profile : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (A : ℝ) (x x' : Space (m+3)) (e : Sphere (m+3)) (Ψ : ℝ → ℝ)
    (j : ℕ) (Λ s : ℝ) (ε : Bool)
    (hne : singleSignedRadialCoefficient m j Ψ
      (f.pairAmbient Q ρ profile N σ J i S A x x') e Λ ε s ≠ 0) :
    ∀ b ∈ F, (x,e) ∈ descriptorEndpointGood Q ρ profile N σ J (i+1) b ∧
      (x',e) ∈ descriptorEndpointGood Q ρ profile N σ J (i+1) b := by
  apply f.signed_stationary_support Q ρ profile N σ J i S A x x' e j Λ ε
  intro hz
  exact hne (by simp only [singleSignedRadialCoefficient,hz,mul_zero,zero_mul])

theorem exists_jetState_noncomparable_radial_kernel (m K L J q : ℕ) (hJL : 2*J ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B H : ℝ, 1 ≤ B ∧ 0 ≤ H ∧
      ∀ (F G : Finset PolicyDescriptor) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (S : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A A' : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A → 0 < A' →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
        (x x' y y' : Space (m+3)) (e e' : Sphere (m+3)),
      ∀ R large small : ℝ, 0 < R → 0 < large → 0 ≤ small → 2*small ≤ large →
      (2*(E+Dq))^2 ≤ R*large →
      ‖∫ s : ℝ, (Ψ s:ℂ)*
        stationarySphereApprox m J (R*s*large) (f.pairAmbient Q ρ profile N σ J₀ i S A x x') e*
        sphereOscillation (R*s*small) e'
          (fun w => g.pairAmbient Q ρ profile N σ J₀ i S A' y y' w)‖ ≤
      H*(B^K*A⁻¹)^2*((descriptorJetBound (m+3) K)^K*A'⁻¹)^2*
        (sphereMeasure (m+3)).real univ*(R*large)^(-((m+2:ℕ):ℝ)/2)/(R*large/2)^q := by
  obtain ⟨B,hB,hbudget⟩ := exists_descriptorJetSymbol_pair_budget (m+1) K L
  obtain ⟨H,hH,hkernel⟩ := single_sphere_retained_bound hΨ hs m J q
  refine ⟨B,H,hB,hH,?_⟩
  intro F G Q ρ profile N σ J₀ i S hF hG Dq Dmask E A A' hDq hDm hA hA' hD
    hscale hE f g x x' y y' e e' R large small hR hl hsmall hsep hlarge
  have hder (k : ℕ) (hk : k ≤ 2*J) (w : Sphere (m+3)) :=
    hbudget F Q ρ profile N σ J₀ i S hF Dq Dmask E A hDq hDm hA hscale hE f x x' k
      (hk.trans hJL) w
  have hsmallBound (w : Sphere (m+3)) :
      ‖g.pairAmbient Q ρ profile N σ J₀ i S A' y y' w‖ ≤
        ((descriptorJetBound (m+3) K)^K*A'⁻¹)^2 := by
    rw [g.pairAmbient_sphere,norm_mul,norm_star,pow_two]
    exact mul_le_mul (g.value_norm_le Q ρ profile N σ J₀ i S hG hA' y w)
      (g.value_norm_le Q ρ profile N σ J₀ i S hG hA' y' w) (norm_nonneg _)
      (mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
        (inv_nonneg.mpr hA'.le))
  exact hkernel _ (f.pairAmbient_smooth Q ρ profile N σ J₀ i S A x x')
    _ _ R large small _ (sq_nonneg _) hD hR hl hsmall hsep hlarge hder e e'
    (fun w => g.pairAmbient Q ρ profile N σ J₀ i S A' y y' w)
    ((g.pairAmbient_smooth Q ρ profile N σ J₀ i S A' y y').continuous.measurable.comp
      continuous_subtype_val.measurable) hsmallBound

end Falconer

end OAI

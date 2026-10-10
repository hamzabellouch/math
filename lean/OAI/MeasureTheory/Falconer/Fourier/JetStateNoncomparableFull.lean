import OAI.MeasureTheory.Falconer.Angular.NoncomparableSphereKernel
import OAI.MeasureTheory.Falconer.Fourier.JetStateNoncomparable

namespace OAI

/-! # Noncomparable decay for the original two descriptor-state spheres -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

theorem exists_jetState_noncomparable_full_kernel
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L J q : ℕ) (hJ : 1 ≤ J) (hJL : 2*J+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B H S : ℝ, 1 ≤ B ∧ 0 ≤ H ∧ 0 ≤ S ∧
      ∀ (F G : Finset PolicyDescriptor) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (T : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      (∀ b ∈ G, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A A' : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A → 0 < A' →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
        (x x' y y' : Space (m+3)) (e e' : Sphere (m+3))
        (v large small base κ : ℝ),
      0 < large → 0 ≤ small → 2*small ≤ large → 1 ≤ base →
      (2*(E+Dq))^2 ≤ (2:ℝ)^v*large → 2*(E+Dq) ≤ base^2 →
      (∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
        1 ≤ r*large ∧ (2*(E+Dq))^2/(r*large) ≤ base^(-κ)) →
      let C₁ := (B^K*A⁻¹)^2
      let C₂ := ((descriptorJetBound (m+3) K)^K*A'⁻¹)^2
      let ε := S*C₁*base^(-κ*(J:ℝ)+2*(m+3))
      ‖((2:ℝ)^v)⁻¹ • (∫ r : ℝ, (Ψ (r/(2:ℝ)^v):ℂ)*
        sphereOscillation (r*large) e (fun w => f.value Q ρ profile N σ J₀ i T A x w*
          star (f.value Q ρ profile N σ J₀ i T A x' w))*
        sphereOscillation (r*small) e' (fun w => g.value Q ρ profile N σ J₀ i T A' y w*
          star (g.value Q ρ profile N σ J₀ i T A' y' w)))‖ ≤
        H*C₁*C₂*(sphereMeasure (m+3)).real univ*
          ((2:ℝ)^v*large)^(-((m+2:ℕ):ℝ)/2)/((2:ℝ)^v*large/2)^q +
        4*W*(ε*(2*(max C₁ C₂*(sphereMeasure (m+3)).real univ)+ε)) := by
  obtain ⟨B,hB,hbudget⟩ := exists_descriptorJetSymbol_pair_budget (m+1) K L
  obtain ⟨H,S,hH,hS,hkernel⟩ := exists_noncomparable_sphere_kernel
    hgnomonic hquadratic m J q hJ hΨ hpos hs hW hΨW
  refine ⟨B,H,S,hB,hH,hS,?_⟩
  intro F G Q ρ profile N σ J₀ i T hF hG Dq Dmask E A A' hDq hDm hA hA' hD
    hscale hE f g x x' y y' e e' v large small base κ hl hsmall hsep hbase hlead hDbase hregime
  have hder (k : ℕ) (hk : k ≤ 2*J+(m+2)+1) (w : Sphere (m+3)) :=
    hbudget F Q ρ profile N σ J₀ i T hF Dq Dmask E A hDq hDm hA hscale hE f x x' k
      (hk.trans hJL) w
  have hsmallBound (w : Sphere (m+3)) :
      ‖g.pairAmbient Q ρ profile N σ J₀ i T A' y y' w‖ ≤
        ((descriptorJetBound (m+3) K)^K*A'⁻¹)^2 := by
    rw [g.pairAmbient_sphere,norm_mul,norm_star,pow_two]
    exact mul_le_mul (g.value_norm_le Q ρ profile N σ J₀ i T hG hA' y w)
      (g.value_norm_le Q ρ profile N σ J₀ i T hG hA' y' w) (norm_nonneg _)
      (mul_nonneg (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _)
        (inv_nonneg.mpr hA'.le))
  have h := hkernel (f.pairAmbient Q ρ profile N σ J₀ i T A x x')
    (f.pairAmbient_smooth Q ρ profile N σ J₀ i T A x x') _ _ (sq_nonneg _) hD hder
    (fun w => g.pairAmbient Q ρ profile N σ J₀ i T A' y y' w)
    ((g.pairAmbient_smooth Q ρ profile N σ J₀ i T A' y y').continuous.measurable.comp
      continuous_subtype_val.measurable) _ (sq_nonneg _) hsmallBound
    e e' v large small base κ hl hsmall hsep hbase hlead hDbase hregime
  simpa only [DescriptorJetSymbol.pairAmbient_sphere] using h

end Falconer

end OAI

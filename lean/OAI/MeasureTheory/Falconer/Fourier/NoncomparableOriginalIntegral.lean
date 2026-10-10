import OAI.MeasureTheory.Falconer.Fourier.JetStateNoncomparableFull
import OAI.MeasureTheory.Falconer.Estimates.NoncomparableKernelScale
import OAI.MeasureTheory.Falconer.Estimates.FourPointPartition
import OAI.MeasureTheory.Falconer.Shells.OriginalShellIntegral

namespace OAI

/-! # The noncomparable contribution on the original four-point law -/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff
open PlanarFalconer (PolicyDescriptor)

noncomputable def jetStateOriginalKernel {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq)
    (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (T : PolicyDescriptor → Finset (Sphere (m+3))) (Af Ag v : ℝ) (Ψ : ℝ → ℝ)
    (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))) : ℂ :=
  ∫ r : ℝ,
    sphereOscillation (r*dist z.1.1 z.1.2) (normalizeToSphere w₀ (z.1.1-z.1.2))
      (fun w => f.value Q ρ profile N σ J i T Af z.1.1 w *
        star (f.value Q ρ profile N σ J i T Af z.1.2 w)) *
    sphereOscillation (r*dist z.2.1 z.2.2) (normalizeToSphere w₀ (z.2.1-z.2.2))
      (fun w => g.value Q ρ profile N σ J i T Ag z.2.1 w *
        star (g.value Q ρ profile N σ J i T Ag z.2.2 w))
    ∂PlanarFalconer.sourceAngularShellMeasure v Ψ

theorem jetStateOriginalKernel_eq_volume {m K L : ℕ}
    {F G : Finset PolicyDescriptor} {Dq : ℝ}
    (f : DescriptorJetSymbol (m+1) K L F Dq)
    (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (T : PolicyDescriptor → Finset (Sphere (m+3))) (Af Ag v : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hzero : ∀ s ≤ 0, Ψ s = 0)
    (z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))) :
    jetStateOriginalKernel f g w₀ Q ρ profile N σ J i T Af Ag v Ψ z =
      ((2:ℝ)^v)⁻¹ • (∫ r : ℝ, (Ψ (r/(2:ℝ)^v):ℂ)*
        sphereOscillation (r*dist z.1.1 z.1.2) (normalizeToSphere w₀ (z.1.1-z.1.2))
          (fun w => f.value Q ρ profile N σ J i T Af z.1.1 w *
            star (f.value Q ρ profile N σ J i T Af z.1.2 w)) *
        sphereOscillation (r*dist z.2.1 z.2.2) (normalizeToSphere w₀ (z.2.1-z.2.2))
          (fun w => g.value Q ρ profile N σ J i T Ag z.2.1 w *
            star (g.value Q ρ profile N σ J i T Ag z.2.2 w))) := by
  rw [jetStateOriginalKernel,PlanarFalconer.sourceAngularShellMeasure_integral v hΨ hpos hzero]
  simp only [Complex.real_smul,mul_assoc]

theorem exists_jetState_noncomparable_original_integral
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
      ∀ Dq Dmask E Af Ag : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < Af → 0 < Ag →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
        (w₀ : Sphere (m+3)) (P₁ P₂ : DyadicCube (m+3))
        (μ ν : Measure (Space (m+3))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
        (v base κ loss : ℝ),
      1 ≤ base → 0 ≤ loss → loss ≤ κ*(((m+2:ℕ):ℝ)/2+(q:ℝ)) →
      -κ*(J:ℝ)+2*(m+3) ≤ -loss → 2*(E+Dq) ≤ base^2 →
      ∀ U : Set ((Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3))),
      MeasurableSet U →
      (∀ z ∈ U, 0 < dist z.1.1 z.1.2 ∧
        2*dist z.2.1 z.2.2 ≤ dist z.1.1 z.1.2 ∧
        (2*(E+Dq))^2 ≤ (2:ℝ)^v*dist z.1.1 z.1.2 ∧
        base^κ ≤ (2:ℝ)^v*dist z.1.1 z.1.2 ∧
        ∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
          1 ≤ r*dist z.1.1 z.1.2 ∧ (2*(E+Dq))^2/(r*dist z.1.1 z.1.2) ≤ base^(-κ)) →
      let C₁ := (B^K*Af⁻¹)^2
      let C₂ := ((descriptorJetBound (m+3) K)^K*Ag⁻¹)^2
      let M := (sphereMeasure (m+3)).real univ
      ‖∫ z in U, jetStateOriginalKernel f g w₀ Q ρ profile N σ J₀ i T Af Ag v Ψ z
        ∂originalFourPointMeasure P₁ P₂ μ ν‖ ≤
        ((H*C₁*C₂*M*(2:ℝ)^q + 4*W*S*C₁*(2*(max C₁ C₂*M)+S*C₁))*base^(-loss))*
          (originalFourPointMeasure P₁ P₂ μ ν).real U := by
  obtain ⟨B,H,S,hB,hH,hS,hkernel⟩ := exists_jetState_noncomparable_full_kernel
    hgnomonic hquadratic m K L J q hJ hJL hΨ hpos hs hW hΨW
  refine ⟨B,H,S,hB,hH,hS,?_⟩
  intro F G Q ρ profile N σ J₀ i T hF hG Dq Dmask E Af Ag hDq hDm hAf hAg hD
    hscale hE f g w₀ P₁ P₂ μ ν _ _ v base κ loss hbase hloss hlead hexp hupper U hU hgeo
  have hzero (s : ℝ) (h : s ≤ 0) : Ψ s = 0 := by
    by_contra hn
    have hp := (hs s hn).1
    linarith
  have : IsFiniteMeasure (originalFourPointMeasure P₁ P₂ μ ν) := by
    unfold originalFourPointMeasure
    infer_instance
  dsimp only
  rw [← measureReal_restrict_apply_univ (μ := originalFourPointMeasure P₁ P₂ μ ν) U]
  apply norm_integral_le_of_norm_le_const
  filter_upwards [ae_restrict_mem hU] with z hz
  obtain ⟨hl,hsep,hDlarge,hfreq,hr⟩ := hgeo z hz
  rw [jetStateOriginalKernel_eq_volume f g w₀ Q ρ profile N σ J₀ i T Af Ag v
    hΨ.continuous.measurable hpos hzero z]
  have hp := hkernel F G Q ρ profile N σ J₀ i T hF hG Dq Dmask E Af Ag
    hDq hDm hAf hAg hD hscale hE f g z.1.1 z.1.2 z.2.1 z.2.2
    (normalizeToSphere w₀ (z.1.1-z.1.2)) (normalizeToSphere w₀ (z.2.1-z.2.2))
    v _ _ base κ hl dist_nonneg hsep hbase hDlarge hupper hr
  exact hp.trans (noncomparable_kernel_scale hbase hfreq hloss hlead hexp hH hW hS
    (sq_nonneg _) (sq_nonneg _) measureReal_nonneg)

end Falconer

end OAI

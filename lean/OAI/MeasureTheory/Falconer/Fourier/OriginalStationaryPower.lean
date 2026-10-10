import OAI.MeasureTheory.Falconer.Fourier.OriginalStationaryReplacement

namespace OAI

/-! # A uniform power loss for the actual radial replacement

The constant and derivative scale are selected before the descriptor list.
The four endpoint normalization factors remain explicit.
-/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

theorem exists_jetState_original_stationary_power
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m K L J : ℕ) (hJ : 1 ≤ J) (hJL : 2*J+(m+2)+1 ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : Measurable Ψ) (hpos : ∀ s, 0 ≤ Ψ s)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ s, Ψ s ≤ W) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (F : Finset PolicyDescriptor) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (T : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ T b, ∀ z ∈ T b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq) (w₀ : Sphere (m+3))
        (v base κ loss : ℝ), 1 ≤ base → 0 ≤ loss →
      -κ*(J:ℝ)+2*(m+3) ≤ -loss → 2*(E+Dq) ≤ base^2 →
      ∀ z : (Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)),
      (∀ r, Ψ (r/(2:ℝ)^v) ≠ 0 →
        (1 ≤ r*dist z.1.1 z.1.2 ∧ (2*(E+Dq))^2/(r*dist z.1.1 z.1.2) ≤ base^(-κ)) ∧
        (1 ≤ r*dist z.2.1 z.2.2 ∧ (2*(E+Dq))^2/(r*dist z.2.1 z.2.2) ≤ base^(-κ))) →
      ‖jetStateOriginalKernel f g w₀ Q ρ profile N σ J₀ i T A A v Ψ z -
        jetStateStationaryKernel f g w₀ Q ρ profile N σ J₀ i T A J ((2:ℝ)^v) Ψ z‖ ≤
        C*(B^K*A⁻¹)^4*base^(-loss) := by
  obtain ⟨B₀,C₀,hB₀,hC₀,hreplace⟩ := exists_jetState_original_stationary_replacement
    hgnomonic hquadratic m K L J hJ hJL hΨ hpos hs hW hΨW
  let B := max B₀ (descriptorJetBound (m+3) K)
  let C := 4*W*C₀*(2*(sphereMeasure (m+3)).real univ+C₀)
  have hB : 1 ≤ B := hB₀.trans (le_max_left _ _)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨B,C,hB,hC,?_⟩
  intro F Q ρ profile N σ J₀ i T hF Dq Dmask E A hDq hDm hA hD hscale hE
    f g w₀ v base κ loss hbase hloss hexp hupper z hregime
  have hE₀ : (F.card:ℝ)*B₀*Dmask ≤ E := by
    apply le_trans _ hE
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_left B₀ _) (Nat.cast_nonneg _))
      (zero_le_one.trans hDm)
  have hp := hreplace F Q ρ profile N σ J₀ i T hF Dq Dmask E A
    hDq hDm hA hD hscale hE₀ f g w₀ v base κ hbase hupper z hregime
  have hi : 0 ≤ A⁻¹ := inv_nonneg.mpr hA.le
  have hB₀pos : 0 ≤ B₀ := zero_le_one.trans hB₀
  have hJpos : 0 ≤ descriptorJetBound (m+3) K :=
    zero_le_one.trans (descriptorJetBound_one_le _ _)
  have hpow₀ : (B₀^K*A⁻¹)^2 ≤ (B^K*A⁻¹)^2 :=
    pow_le_pow_left₀ (mul_nonneg (pow_nonneg hB₀pos _) hi)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB₀pos (le_max_left _ _) _) hi) 2
  have hpowJ : ((descriptorJetBound (m+3) K)^K*A⁻¹)^2 ≤ (B^K*A⁻¹)^2 :=
    pow_le_pow_left₀ (mul_nonneg (pow_nonneg hJpos _) hi)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hJpos (le_max_right _ _) _) hi) 2
  have herr := noncomparable_stationary_error_scale
    (S := C₀) (C := (B₀^K*A⁻¹)^2)
    (M := ((descriptorJetBound (m+3) K)^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ)
    hbase hloss hexp hW hC₀ (sq_nonneg _) (by positivity)
  have hpoly : 4*W*C₀*(B₀^K*A⁻¹)^2*
      (2*(((descriptorJetBound (m+3) K)^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ)+
        C₀*(B₀^K*A⁻¹)^2) ≤ C*(B^K*A⁻¹)^4 := by
    calc
      _ ≤ 4*W*C₀*(B^K*A⁻¹)^2*
          (2*((B^K*A⁻¹)^2*(sphereMeasure (m+3)).real univ)+C₀*(B^K*A⁻¹)^2) := by
        gcongr
      _ = _ := by dsimp [C]; ring
  exact hp.trans (herr.trans (mul_le_mul_of_nonneg_right hpoly (by positivity)))

end Falconer

end OAI

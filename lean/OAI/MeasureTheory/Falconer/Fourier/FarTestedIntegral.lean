import OAI.MeasureTheory.Falconer.Fourier.JetStateFarSupport
import OAI.MeasureTheory.Falconer.Estimates.FourPointPartition
import OAI.MeasureTheory.Falconer.Geometry.FarNormalization

namespace OAI

/-! # The actual far kernel is bounded on the original tested pair laws -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal ContDiff
open PlanarFalconer (PolicyDescriptor)

private theorem lintegral_supported_pair_bound {d : ℕ}
    (μ ν : Measure (Space d × Space d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (G H : Set (Space d × Space d))
    (hG : MeasurableSet G) (hH : MeasurableSet H)
    (U : Set ((Space d × Space d) × (Space d × Space d))) (hU : MeasurableSet U)
    (F : ((Space d × Space d) × (Space d × Space d)) → ℂ)
    (k : ((Space d × Space d) × (Space d × Space d)) → ℝ≥0∞)
    (hk : Measurable k) (C : ℝ≥0∞)
    (hb : ∀ z ∈ U, ENNReal.ofReal ‖F z‖ ≤ C*k z)
    (hs : ∀ z ∈ U, z ∉ G ×ˢ H → F z = 0) :
    (∫⁻ z in U, ENNReal.ofReal ‖F z‖ ∂μ.prod ν) ≤
      C*(∫⁻ z in U, k z ∂(μ.restrict G).prod (ν.restrict H)) := by
  have hT : MeasurableSet (G ×ˢ H) := hG.prod hH
  have he : (∫⁻ z in U, ENNReal.ofReal ‖F z‖ ∂μ.prod ν) =
      ∫⁻ z in U, (G ×ˢ H).indicator (fun z => ENNReal.ofReal ‖F z‖) z ∂μ.prod ν := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hU] with z hz
    by_cases ht : z ∈ G ×ˢ H
    · simp only [indicator_of_mem ht]
    · simp only [indicator_of_notMem ht, hs z hz ht, norm_zero, ENNReal.ofReal_zero]
  rw [he, lintegral_indicator hT, Measure.prod_restrict,
    Measure.restrict_restrict hT, Measure.restrict_restrict hU, inter_comm (G ×ˢ H) U]
  calc
    _ ≤ ∫⁻ z in U ∩ (G ×ˢ H), C*k z ∂μ.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (hU.inter hT)] with z hz
      exact hb z hz.1
    _ = _ := lintegral_const_mul C hk

theorem exists_jetState_far_tested_integral (m K L J : ℕ) (hJL : 2*J ≤ L)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hs : ∀ s, Ψ s ≠ 0 → s ∈ Ioo (1/4:ℝ) 4) :
    ∃ B C : ℝ, 1 ≤ B ∧ 0 ≤ C ∧
      ∀ (F H : Finset PolicyDescriptor), H ⊆ F →
      ∀ (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
        [IsFiniteMeasure ρ] (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J₀ i : ℕ)
        (S : PolicyDescriptor → Finset (Sphere (m+3))),
      (∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z) →
      ∀ Dq Dmask E A : ℝ, 0 ≤ Dq → 1 ≤ Dmask → 0 < A →
      1 ≤ 2*(E+Dq) → (∀ b ∈ F, (descriptorMaskRadius N σ b)⁻¹ ≤ Dmask) →
      (F.card:ℝ)*B*Dmask ≤ E →
      ∀ (f g : DescriptorJetSymbol (m+1) K L F Dq) (v b : ℝ)
        (P₁ P₂ Q₁ Q₂ : DyadicCube (m+3))
        (U : Set ((Space (m+3) × Space (m+3)) × (Space (m+3) × Space (m+3)))),
      MeasurableSet U →
      (∀ z ∈ U, (2:ℝ)^(-b) ≤ dist z.1.1 z.1.2 ∧ (2:ℝ)^(-b) ≤ dist z.2.1 z.2.2 ∧
        (2*(E+Dq))^2 ≤ (2:ℝ)^v*dist z.1.1 z.1.2 ∧
        (2*(E+Dq))^2 ≤ (2:ℝ)^v*dist z.2.1 z.2.2) →
      (∫⁻ z in U, ENNReal.ofReal ‖jetStateStationaryKernel f g w₀ Q ρ profile N σ J₀ i S A J
        ((2:ℝ)^v) Ψ z‖
        ∂((ρ.restrict P₁.carrier).prod (ρ.restrict P₂.carrier)).prod
          ((ρ.restrict Q₁.carrier).prod (ρ.restrict Q₂.carrier))) ≤
      ENNReal.ofReal (C*(B^K*A⁻¹)^4*(2:ℝ)^(-((m+2:ℕ):ℝ)*(v-b))) *
        (∫⁻ z in U, ENNReal.ofReal
          (1/(1+(2:ℝ)^v*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2)
          ∂(testedCellPair ρ ρ P₁ P₂ (descriptorPairTests w₀ Q ρ profile N σ J₀ (i+1) H)).prod
            (testedCellPair ρ ρ Q₁ Q₂ (descriptorPairTests w₀ Q ρ profile N σ J₀ (i+1) H))) := by
  obtain ⟨B,C,hB,hC,hkernel⟩ := exists_jetState_far_radial_kernel m K L J hJL hΨ hs
  refine ⟨B,C,hB,hC,?_⟩
  intro F H hHF w₀ Q ρ _ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE
    f g v b P₁ P₂ Q₁ Q₂ U hU hgeo
  apply lintegral_supported_pair_bound _ _ _ _
    (descriptorPairTests_measurable w₀ Q ρ profile N σ J₀ (i+1) H)
    (descriptorPairTests_measurable w₀ Q ρ profile N σ J₀ (i+1) H)
    U hU _ _ (by fun_prop)
  · intro z hz
    obtain ⟨h₁,h₂,hD₁,hD₂⟩ := hgeo z hz
    have hd₁ : 0 < dist z.1.1 z.1.2 := (Real.rpow_pos_of_pos (by norm_num) (-b)).trans_le h₁
    have hd₂ : 0 < dist z.2.1 z.2.2 := (Real.rpow_pos_of_pos (by norm_num) (-b)).trans_le h₂
    have hb := hkernel F Q ρ profile N σ J₀ i S hsep Dq Dmask E A hDq hDm hA hD hscale hE
      f g z.1.1 z.1.2 z.2.1 z.2.2 (normalizeToSphere w₀ (z.1.1-z.1.2))
        (normalizeToSphere w₀ (z.2.1-z.2.2)) ((2:ℝ)^v) _ _ (by positivity) hd₁ hd₂ hD₁ hD₂
    have hgain := far_sphere_gain m (v := v) h₁ h₂
    have hCb : 0 ≤ C*(B^K*A⁻¹)^4 := mul_nonneg hC (by positivity)
    have hb' := hb.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgain hCb) (by positivity))
    change ENNReal.ofReal ‖jetStateStationaryKernel f g w₀ Q ρ profile N σ J₀ i S A J
      ((2:ℝ)^v) Ψ z‖ ≤ _
    rw [← ENNReal.ofReal_mul (mul_nonneg hCb (by positivity))]
    apply ENNReal.ofReal_le_ofReal
    simpa only [jetStateStationaryKernel, div_eq_mul_inv, one_div, one_mul, mul_assoc] using hb'
  · intro z hz hbad
    obtain ⟨h₁,h₂,_,_⟩ := hgeo z hz
    exact jetStateStationaryKernel_eq_zero_of_not_tested f g hHF w₀ Q ρ profile N σ J₀ i S A J
      (by positivity) Ψ hs z ((Real.rpow_pos_of_pos (by norm_num) (-b)).trans_le h₁)
      ((Real.rpow_pos_of_pos (by norm_num) (-b)).trans_le h₂) hbad

end Falconer

end OAI

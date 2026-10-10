import OAI.MeasureTheory.Falconer.Fourier.JetStateCrossKernel
import OAI.MeasureTheory.Falconer.Estimates.NearFarSplit
import OAI.MeasureTheory.Falconer.Fourier.JetStateNear

namespace OAI

/-! # The near/far decomposition for actual recursive angular states

All descriptor factors remain in the far integrals. The intermediate
child model masses cancel exactly when these integrals are opened.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
open PlanarFalconer (PolicyDescriptor)
attribute [local instance] Classical.propDecidable

 theorem jetState_energy_near_far {m K L : ℕ} {Dq : ℝ}
    {F G : Finset PolicyDescriptor}
    (f : DescriptorJetSymbol (m+1) K L F Dq) (g : DescriptorJetSymbol (m+1) K L G Dq)
    (w₀ : Sphere (m+3)) (Q : DyadicCube (m+3)) (ρ : Measure (Space (m+3)))
    [IsFiniteMeasure ρ] (profile : ℝ → ℝ) (N : ℕ) (σ : ℝ) (J i : ℕ)
    (S : PolicyDescriptor → Finset (Sphere (m+3)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (P₁ P₂ : DyadicCube (m+3))
    (a h : ℕ) (v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    jetStateEnergy Q ρ (fun s => profile (s/N)) N σ J i S A
      (ρ.restrict P₁.carrier) (ρ.restrict P₂.carrier)
      (profileModelMass profile N a) (profileModelMass profile N a) a v Ψ f g ≤
    profileNearEnergy P₁ P₂ ρ profile N a h v Ψ
      (f.value Q ρ (fun s => profile (s/N)) N σ J i S A)
      (g.value Q ρ (fun s => profile (s/N)) N σ J i S A) +
    ((2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*(profileModelMass profile N a)⁻¹^4)*
      ∑ row ∈ P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a),
        ∑ col ∈ P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a),
          if nearDyadicEdge P₁ P₂ (10*(((m+3:ℕ):ℝ)+1)/(2:ℝ)^h) row col then 0 else
            ‖∫ z, jetStateOriginalKernel f g w₀ Q ρ (fun s => profile (s/N)) N σ J i S A A v Ψ z
              ∂fourPointChildMeasure P₁ P₂ ρ ρ (row.1,col.1) (row.2,col.2)‖ := by
  let Ma := profileModelMass profile N a
  let Mh := profileModelMass profile N h
  let V := P₁.occupiedPaths ρ (h-a) ×ˢ P₂.occupiedPaths ρ (h-a)
  let b := f.value Q ρ (fun s => profile (s/N)) N σ J i S A
  let c := g.value Q ρ (fun s => profile (s/N)) N σ J i S A
  have hB : 0 ≤ (descriptorJetBound (m+3) K)^K*A⁻¹ := mul_nonneg
    (pow_nonneg (zero_le_one.trans (descriptorJetBound_one_le _ _)) _) (inv_nonneg.mpr hA.le)
  have hMa : 0 < Ma := by dsimp [Ma,profileModelMass]; positivity
  have hMh : 0 < Mh := by dsimp [Mh,profileModelMass]; positivity
  have hs := profile_energy_near_far P₁ P₂ ρ profile N a h v Ψ b c
    (f.value_measurable _ _ _ _ _ _ _ _ _) (g.value_measurable _ _ _ _ _ _ _ _ _) hB
    (f.value_norm_le _ _ _ _ _ _ _ _ hF hA) (g.value_norm_le _ _ _ _ _ _ _ _ hG hA)
  have hweight : 0 ≤ (Mh⁻¹*Mh⁻¹)*(Mh⁻¹*Mh⁻¹) := by positivity
  have hterm (row col : List (Fin (m+3) → Bool) × List (Fin (m+3) → Bool)) :
      ‖∫ z, dyadicPairTransform P₁ P₂ ρ ρ Mh Mh b c row z *
        star (dyadicPairTransform P₁ P₂ ρ ρ Mh Mh b c col z)
        ∂angularProductMeasure (m+3) v Ψ‖ =
      ((Mh⁻¹*Mh⁻¹)*(Mh⁻¹*Mh⁻¹))*
        ‖∫ z, jetStateOriginalKernel f g w₀ Q ρ (fun s => profile (s/N)) N σ J i S A A v Ψ z
          ∂fourPointChildMeasure P₁ P₂ ρ ρ (row.1,col.1) (row.2,col.2)‖ := by
    rw [dyadic_jetState_original_kernel f g w₀ Q ρ (fun s => profile (s/N)) N σ J i S
      hF hG hA P₁ P₂ hMh v Ψ row col,norm_smul,Real.norm_eq_abs,abs_of_nonneg hweight]
  have hsum :
      (∑ row ∈ V, ∑ col ∈ V,
        if nearDyadicEdge P₁ P₂ (10*(((m+3:ℕ):ℝ)+1)/(2:ℝ)^h) row col then 0 else
          ‖∫ z, dyadicPairTransform P₁ P₂ ρ ρ Mh Mh b c row z *
            star (dyadicPairTransform P₁ P₂ ρ ρ Mh Mh b c col z)
            ∂angularProductMeasure (m+3) v Ψ‖) =
      ((Mh⁻¹*Mh⁻¹)*(Mh⁻¹*Mh⁻¹))*
      ∑ row ∈ V, ∑ col ∈ V,
        if nearDyadicEdge P₁ P₂ (10*(((m+3:ℕ):ℝ)+1)/(2:ℝ)^h) row col then 0 else
          ‖∫ z, jetStateOriginalKernel f g w₀ Q ρ (fun s => profile (s/N)) N σ J i S A A v Ψ z
            ∂fourPointChildMeasure P₁ P₂ ρ ρ (row.1,col.1) (row.2,col.2)‖ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro row _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro col _
    by_cases hn : nearDyadicEdge P₁ P₂ (10*(((m+3:ℕ):ℝ)+1)/(2:ℝ)^h) row col
    · simp only [ite_eq_left hn,mul_zero]
    · simpa only [ite_eq_right hn] using hterm row col
  have hcancel : ((Mh/Ma)^4*(2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)))*
      ((Mh⁻¹*Mh⁻¹)*(Mh⁻¹*Mh⁻¹)) =
      (2:ℝ)^(((m+3:ℕ):ℝ)*(v-a))*Ma⁻¹^4 := by
    field_simp
  change _ ≤ _ + ((Mh/Ma)^4*(2:ℝ)^(((m+3:ℕ):ℝ)*(v-a)))*_ at hs
  rw [hsum,← mul_assoc,hcancel] at hs
  exact hs

end Falconer

end OAI

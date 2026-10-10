import OAI.MeasureTheory.Falconer.Fourier.JetStateBudgetOrder
import OAI.MeasureTheory.Falconer.Geometry.NormalizedSpatialFactors

namespace OAI

/-! # Changing the fixed normalization of the exact jet envelope -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol

theorem value_renormalize {n K L : ℕ} {F : Finset PolicyDescriptor} {D : ℝ}
    (f : DescriptorJetSymbol n K L F D)
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    {A B : ℝ} (hB : B ≠ 0) :
    f.value Q ρ m N σ J i S A =
      fun x w => ((B/A : ℝ) : ℂ)*f.value Q ρ m N σ J i S B x w := by
  funext x w
  unfold value multiplier
  simp only [Complex.ofReal_div,Complex.ofReal_inv]
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB
  field_simp

end DescriptorJetSymbol

theorem jetStateEnvelope_renormalize {n K L : ℕ} {D : ℝ} {F G : Finset PolicyDescriptor}
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    jetStateEnvelope n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ ≤
      (B/A)^4*jetStateEnvelope n K L D F G Q ρ m N σ J i S B μ ν M P a v Ψ := by
  have hratio : 0 ≤ B/A := div_nonneg hB.le hA.le
  have hbound : 0 ≤ (descriptorJetBound (n+2) K)^K*B⁻¹ := by
    have := descriptorJetBound_one_le (n+2) K
    positivity
  have henv : 0 ≤ jetStateEnvelope n K L D F G Q ρ m N σ J i S B μ ν M P a v Ψ :=
    le_csSup (jetStateValues_bddAbove Q ρ m N σ J i S hF hG hB μ ν hM hP a v Ψ) (Or.inl rfl)
  apply csSup_le (show (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ).Nonempty
    from ⟨0,Or.inl rfl⟩)
  intro x hx
  rcases hx with rfl | ⟨f,g,rfl⟩
  · exact mul_nonneg (pow_nonneg hratio _) henv
  · have hf := f.value_renormalize Q ρ m N σ J i S (A := A) hB.ne'
    have hg := g.value_renormalize Q ρ m N σ J i S (A := A) hB.ne'
    have h := independentAngularEnergy_endpoint_remove_factors μ ν hM hP
      (f.value Q ρ m N σ J i S B) (g.value Q ρ m N σ J i S B)
      (f.value_measurable Q ρ m N σ J i S B) (g.value_measurable Q ρ m N σ J i S B)
      hbound hbound (f.value_norm_le Q ρ m N σ J i S hF hB)
      (g.value_norm_le Q ρ m N σ J i S hG hB)
      (fun _ => ((B/A : ℝ) : ℂ)) (fun _ => ((B/A : ℝ) : ℂ))
      measurable_const measurable_const hratio hratio
      (fun _ => by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hratio,le_refl])
      (fun _ => by simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hratio,le_refl]) a v Ψ
    have hpow : (B/A)^2*(B/A)^2 = (B/A)^4 := by ring
    rw [hpow] at h
    have he : jetStateEnergy Q ρ m N σ J i S A μ ν M P a v Ψ f g ≤
        (B/A)^4*jetStateEnergy Q ρ m N σ J i S B μ ν M P a v Ψ f g := by
      unfold jetStateEnergy
      rw [hf,hg]
      simpa only [endpointTransform_const_mul] using h
    exact he.trans (mul_le_mul_of_nonneg_left
      (jetStateEnergy_le_envelope Q ρ m N σ J i S hF hG hB μ ν hM hP a v Ψ f g)
      (pow_nonneg hratio _))

end Falconer

end OAI

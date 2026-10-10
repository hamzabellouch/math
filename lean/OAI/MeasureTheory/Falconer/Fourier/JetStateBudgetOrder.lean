import OAI.MeasureTheory.Falconer.Fourier.JetStateEnvelope

namespace OAI

/-! # Embedding actual states in the fixed recursive derivative budget -/

namespace Falconer
open Set MeasureTheory
open PlanarFalconer (PolicyDescriptor)

namespace DescriptorJetSymbol

noncomputable def relax {n K K' L L' : ℕ} {F : Finset PolicyDescriptor} {D D' : ℝ}
    (f : DescriptorJetSymbol n K L F D) (hK : K ≤ K') (hL : L' ≤ L)
    (hD : 0 ≤ D) (hDD' : D ≤ D') : DescriptorJetSymbol n K' L' F D' where
  jet := f.jet
  order_le := f.order_le.trans hK
  angular := f.angular
  angular_smooth := f.angular_smooth
  angular_derivative := fun t ht w => (f.angular_derivative t (ht.trans hL) w).trans
    (pow_le_pow_left₀ hD hDD' t)
  angular_control := {
    measurable := f.angular_control.measurable
    bound := f.angular_control.bound
    smooth := f.angular_control.smooth
    derivative := by
      intro e t ht x y hy u hu
      exact (f.angular_control.derivative e t (ht.trans hL) x y hy u hu).trans
        (by simpa only [one_mul] using pow_le_pow_left₀ hD hDD' t) }
  spatial := f.spatial
  spatial_measurable := f.spatial_measurable
  spatial_bound := f.spatial_bound

theorem relax_value {n K K' L L' : ℕ} {F : Finset PolicyDescriptor} {D D' : ℝ}
    (f : DescriptorJetSymbol n K L F D) (hK : K ≤ K') (hL : L' ≤ L)
    (hD : 0 ≤ D) (hDD' : D ≤ D')
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2))) (A : ℝ) :
    (f.relax hK hL hD hDD').value Q ρ m N σ J i S A = f.value Q ρ m N σ J i S A := rfl

end DescriptorJetSymbol

theorem jetStateValues_budget_subset {n K K' L L' : ℕ} {D D' : ℝ}
    {F G : Finset PolicyDescriptor} (hK : K ≤ K') (hL : L' ≤ L)
    (hD : 0 ≤ D) (hDD' : D ≤ D')
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (A : ℝ) (μ ν : Measure (Space (n+2))) (M P a v : ℝ) (Ψ : ℝ → ℝ) :
    jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ ⊆
      jetStateValues n K' L' D' F G Q ρ m N σ J i S A μ ν M P a v Ψ := by
  intro h hh
  rcases hh with rfl | ⟨f,g,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨f.relax hK hL hD hDD',g.relax hK hL hD hDD',rfl⟩

theorem jetStateEnvelope_budget_mono {n K K' L L' : ℕ} {D D' : ℝ}
    {F G : Finset PolicyDescriptor} (hK : K ≤ K') (hL : L' ≤ L)
    (hD : 0 ≤ D) (hDD' : D ≤ D')
    (Q : DyadicCube (n+2)) (ρ : Measure (Space (n+2))) (m : ℝ → ℝ)
    (N : ℕ) (σ : ℝ) (J i : ℕ) (S : PolicyDescriptor → Finset (Sphere (n+2)))
    (hF : ∀ b ∈ F, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    (hG : ∀ b ∈ G, ∀ w ∈ S b, ∀ z ∈ S b, w ≠ z → descriptorMaskRadius N σ b/2 ≤ dist w z)
    {A : ℝ} (hA : 0 < A) (μ ν : Measure (Space (n+2))) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {M P : ℝ} (hM : 0 < M) (hP : 0 < P) (a v : ℝ) (Ψ : ℝ → ℝ)
    [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)] :
    jetStateEnvelope n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ ≤
      jetStateEnvelope n K' L' D' F G Q ρ m N σ J i S A μ ν M P a v Ψ := by
  apply csSup_le (show (jetStateValues n K L D F G Q ρ m N σ J i S A μ ν M P a v Ψ).Nonempty
    from ⟨0,Or.inl rfl⟩)
  intro h hh
  exact le_csSup (jetStateValues_bddAbove (K := K') (L := L') (D := D') Q ρ m N σ J i S
    hF hG hA μ ν hM hP a v Ψ)
    (jetStateValues_budget_subset hK hL hD hDD' Q ρ m N σ J i S A μ ν M P a v Ψ hh)

end Falconer

end OAI

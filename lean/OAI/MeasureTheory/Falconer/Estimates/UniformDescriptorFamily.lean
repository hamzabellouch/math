import OAI.MeasureTheory.Falconer.Geometry.NormalizedDescriptorFamily

namespace OAI

/-! # A common scale threshold for every inverse order used in the shell

The finite inverse family and all normalization constants are selected before
any scale label. Taking the finite maximum of their thresholds keeps that
quantifier order through the scalar shell application.
-/

namespace Falconer
open Set MeasureTheory

theorem normalized_descriptor_inverse_orders {I : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    (n J K P : ℕ) {σ : ℝ} (hσ : 0 < σ)
    (Q : I → DyadicCube (n+3)) (hQ : ∀ a, 0 < (Q a).side)
    (ρ : I → Measure (Space (n+3))) (f : I → ℝ → ℝ) (N L J₀ i t : I → ℕ)
    (B : I → Finset PlanarFalconer.PolicyDescriptor)
    (hB : ∀ a b, b ∈ B a → PlanarFalconer.descriptorAnchor b ≤ t a)
    (S : I → PlanarFalconer.PolicyDescriptor → Finset (Sphere (n+3)))
    (hcard : ∀ a, (B a).card ≤ (N a+1)^P)
    (hlength : ∀ a b, b ∈ B a → PlanarFalconer.descriptorLength b ≤ L a)
    (hsep : ∀ a b, b ∈ B a → ∀ w ∈ S a b, ∀ z ∈ S a b, w ≠ z →
      descriptorMaskRadius (N a) σ b/2 ≤ dist w z) :
    let F : I × Space (n+3) → Space (n+3) → ℂ := fun u z =>
      (descriptorAmbientProduct (Q u.1) (ρ u.1) (f u.1) (N u.1)
        σ (J₀ u.1) (i u.1) (B u.1) (S u.1) u.2 z : ℂ)
    ∃ N₀ : ℕ,
      ∃ T : ℕ → SmoothSeparation (I × Space (n+3)) (I × Space (n+3)) (Space (n+3)),
      ∃ p q : (j : ℕ) → (T j).index → ℕ, ∃ A E : (j : ℕ) → (T j).index → ℝ,
      (∀ j, ∀ k : (T j).index,
        Measurable (Function.uncurry ((T j).left k)) ∧
          Measurable (Function.uncurry ((T j).right k))) ∧
      (∀ j, ∀ k, p j k+q j k ≤ 2*j ∧ 1 ≤ A j k ∧ 1 ≤ E j k) ∧
      (∀ j x y z, localInverseAmplitude n (fun w => F x w*F y w) j z = (T j).value x y z) ∧
      (∀ a, N₀ ≤ N a → ∀ D : ℝ, descriptorDerivativeScale (N a) σ (L a) ≤ D →
        ∀ j ∈ Finset.range (J+1), ∀ k : (T j).index,
          ChartSymbolControl K
            (normalizedEndpoint (A j k*D^(p j k)) (fun x w => (T j).left k (a,x) w)) 1 D ∧
          ChartSymbolControl K
            (normalizedEndpoint (E j k*D^(q j k)) (fun x w => (T j).right k (a,x) w)) 1 D) ∧
      (∀ a (D : ℝ) j (k : (T j).index) (w : Sphere (n+3)),
        (∀ x, normalizedEndpoint (A j k*D^(p j k)) (fun x w => (T j).left k (a,x) w) x w ≠ 0 →
          ∀ b ∈ B a, (x,w) ∈ descriptorEndpointGood (Q a) (ρ a) (f a) (N a)
            σ (J₀ a) (i a+1) b) ∧
        (∀ x, normalizedEndpoint (E j k*D^(q j k)) (fun x w => (T j).right k (a,x) w) x w ≠ 0 →
          ∀ b ∈ B a, (x,w) ∈ descriptorEndpointGood (Q a) (ρ a) (f a) (N a)
            σ (J₀ a) (i a+1) b)) := by
  classical
  have hfamily (j : ℕ) := normalized_descriptor_inverse_family n j K P hσ Q hQ ρ f
    N L J₀ i t B hB S hcard hlength hsep
  choose Ns T p q A E hm ho hv hn _hp _hr hs using hfamily
  refine ⟨(Finset.range (J+1)).sup Ns,T,p,q,A,E,hm,ho,hv,?_,fun a D j k w => hs j a D k w⟩
  intro a ha D hD j hj k
  exact hn j a ((Finset.le_sup hj).trans ha) D hD k

end Falconer

end OAI

import OAI.MeasureTheory.Falconer.Graphs.ProfileGraph
import OAI.MeasureTheory.Falconer.Graphs.GraphEnergyEstimate

namespace OAI

/-! # The graph estimate with the two actual regularized profiles

This applies the proved oscillatory localization and graph bound, then
inserts the actual occupied-cell counts and integer parallel-test degrees.
The analytic error remains explicit for the separate arbitrary-power budget.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem dyadic_profile_graph_energy_step
    (hpublished : PublishedGnomonicSurface) (n k : ℕ) (hn : 1 ≤ n)
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W)
    (hsupp : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A C : ℝ, 0 ≤ A ∧ 0 < C ∧
      ∀ (Q₁ Q₂ : DyadicCube (n+2)), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (ρ₁ ρ₂ : Measure (Space (n+2))) (N : ℕ) (s₁ s₂ lam : ℝ)
        (m₁ m₂ : ℝ → ℝ),
      Regularization.RegularizedProfileData Q₁ ρ₁ N s₁ lam m₁ →
      Regularization.RegularizedProfileData Q₂ ρ₂ N s₂ lam m₂ → 0 < N →
      ∀ (a p g₁ g₂ : ℕ) (σ : ℝ), a ≤ p → p ≤ N → 0 ≤ σ →
      a ≤ g₁ → g₁ ≤ p → (g₁:ℝ)-a ≤ 2*σ*N →
      a ≤ g₂ → g₂ ≤ p → (g₂:ℝ)-a ≤ 2*σ*N →
      ∀ (X Y : List (Fin (n+2) → Bool)), X.length = a → Y.length = a →
      ∀ (v τ δ H B D : ℝ), 0 < τ → 0 < δ → δ ≤ 1/2 →
      0 ≤ H → 0 ≤ B → 1 ≤ D → δ⁻¹ ≤ D →
      Real.sqrt (n+2 : ℕ)*(Q₁.descendant X).side ≤ (τ/4)*D →
      2*Real.sqrt (n+2 : ℕ)*((Q₁.descendant X).side/(2:ℝ)^(p-a))+
        8*δ*(Real.sqrt (n+2 : ℕ)*(Q₁.descendant X).side) ≤ τ/4 →
      4*Real.pi*((2:ℝ)^N)^α ≤ (2:ℝ)^v*τ →
      4*τ*((2:ℝ)^(p-a)/(Q₁.descendant X).side) ≤
        (⌈4*((2:ℝ)^N)^(30*σ)⌉₊:ℝ) →
      ∀ {ι : Type*} (K : Finset ι) (w : ι → Sphere (n+2))
        (η : ι → Sphere (n+2) → ℝ),
      (∀ j ∈ K, ChartCapControl k (η j) (w j : Space (n+2)) δ H) →
      (∀ j ∈ K, ∀ z, 0 ≤ η j z) → (∀ z, ∑ j ∈ K, η j z = 1) →
      ∀ (b c : Space (n+2) → Sphere (n+2) → ℂ),
      ChartSymbolControl k b B D → ChartSymbolControl k c B D →
      ∀ (W₁ W₂ : ℝ),
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q₁.descendant X).side/(2:ℝ)^(g₁-a))) ≤ W₁ →
      2*τ+2*δ*(Real.sqrt (n+2 : ℕ)*((Q₂.descendant Y).side/(2:ℝ)^(g₂-a))) ≤ W₂ →
      (∀ q ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a),
        ∀ᵐ x ∂ρ₁.restrict ((Q₁.descendant X).descendant q).carrier,
        ∀ z : Sphere (n+2), b x z ≠ 0 →
          DyadicParallelTest (Q₁.descendant X) ((Q₁.descendant X).occupiedPaths ρ₁ (p-a))
            (g₁-a) q z W₁
            ⌈((2:ℝ)^N)^(PlanarFalconer.height
              (fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) g₁ p+
                1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊) →
      (∀ q ∈ (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
        ∀ᵐ x ∂ρ₂.restrict ((Q₂.descendant Y).descendant q).carrier,
        ∀ z : Sphere (n+2), c x z ≠ 0 →
          DyadicParallelTest (Q₂.descendant Y) ((Q₂.descendant Y).occupiedPaths ρ₂ (p-a))
            (g₂-a) q z W₂
            ⌈((2:ℝ)^N)^(PlanarFalconer.height
              (fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) g₂ p+
                1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊) →
      ∀ [IsFiniteMeasure (PlanarFalconer.sourceAngularShellMeasure v Ψ)],
      ∀ E : ℝ, 0 ≤ E →
      (∀ row ∈ (Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
          (Q₂.descendant Y).occupiedPaths ρ₂ (p-a),
        independentAngularEnergy p v Ψ
          (fun z => endpointTransform
            (ρ₁.restrict ((Q₁.descendant X).descendant row.1).carrier)
            (profileModelMass m₁ N p) b z.1 z.2)
          (fun z => endpointTransform
            (ρ₂.restrict ((Q₂.descendant Y).descendant row.2).carrier)
            (profileModelMass m₂ N p) c z.1 z.2) ≤ E) →
      independentAngularEnergy a v Ψ
        (fun z => endpointTransform (ρ₁.restrict (Q₁.descendant X).carrier)
          (profileModelMass m₁ N a) b z.1 z.2)
        (fun z => endpointTransform (ρ₂.restrict (Q₂.descendant Y).carrier)
          (profileModelMass m₂ N a) c z.1 z.2) ≤
      2*11^(n+2)*((2:ℝ)^N)^(
        -((m₁ ((p:ℝ)/N)-((n+2:ℕ):ℝ)/2*p/N)-
          (m₁ ((a:ℝ)/N)-((n+2:ℕ):ℝ)/2*a/N))-
        ((m₂ ((p:ℝ)/N)-((n+2:ℕ):ℝ)/2*p/N)-
          (m₂ ((a:ℝ)/N)-((n+2:ℕ):ℝ)/2*a/N))+
        (min (PlanarFalconer.height (fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) a p)
          (PlanarFalconer.height (fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N) a p)+
        (1000*(((n+2:ℕ):ℝ)+1)+32*(n+2:ℕ))*σ)+4*(((n+2:ℕ):ℝ)+1)*lam)*E +
      (2:ℝ)^(((n+2:ℕ):ℝ)*(v-a)) *
        ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
          (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
        capGraphError (n+2) k A C W ((2:ℝ)^N) T
          (profileModelMass m₁ N p) (profileModelMass m₂ N p) H B D v τ K.card
          ((Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
            (Q₂.descendant Y).occupiedPaths ρ₂ (p-a)).card := by
  obtain ⟨A,C,hA,hC,hloc⟩ := dyadic_graph_energy_step hpublished n k hn φ Ψ
    hφ hΨ hpos hzero hW hΨW hsupp hα T
  refine ⟨A,C,hA,hC,?_⟩
  intro Q₁ Q₂ hQ₁ hQ₂ ρ₁ ρ₂ N s₁ s₂ lam m₁ m₂ hreg₁ hreg₂ hN
    a p g₁ g₂ σ hap hp hσ hag₁ hgp₁ hgap₁ hag₂ hgp₂ hgap₂ X Y hX hY
    v τ δ H B D hτ hδ hδsmall hH hB hD hδD hnorm herr hfreq hL
    ι K w η hcap hη hpart b c hb hc W₁ W₂ hw₁ hw₂ hs₁ hs₂ _ E hE hchild
  let := hreg₁.probability
  let := hreg₂.probability
  have hside : (Q₂.descendant Y).side = (Q₁.descendant X).side := by
    rw [Q₁.descendant_side,Q₂.descendant_side,hX,hY,hQ₁,hQ₂]
  have hQ : 0 < (Q₁.descendant X).side :=
    Q₁.descendant_side_pos (by rw [hQ₁]; norm_num) X
  have hmass (m : ℝ → ℝ) (j : ℕ) : 0 < profileModelMass m N j := by
    unfold profileModelMass
    positivity
  let F₁ : ℕ → ℝ := fun j => m₁ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N
  let F₂ : ℕ → ℝ := fun j => m₂ ((j:ℝ)/N)-((n+2:ℕ):ℝ)/2*j/N
  let C₁ := ⌈((2:ℝ)^N)^(PlanarFalconer.height F₁ g₁ p+1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊
  let C₂ := ⌈((2:ℝ)^N)^(PlanarFalconer.height F₂ g₂ p+1000*(((n+2:ℕ):ℝ)+1)*σ)⌉₊
  let L := ⌈4*((2:ℝ)^N)^(30*σ)⌉₊
  let degree := (2*L+1)^(n+2) * min (C₁*2^((n+2)*(g₁-a))) (C₂*2^((n+2)*(g₂-a)))
  have hd := profile_graph_degree_two (n+2) F₁ F₂ hN hσ
    hag₁ hgp₁ hgap₁ hag₂ hgp₂ hgap₂
  have hbound := two_profile_graph_contribution_bound Q₁ Q₂ ρ₁ ρ₂ hreg₁ hreg₂ hN
    hap hp X Y hX hY v Ψ b c degree (by positivity) hE hd hchild
  have hraw := hloc (Q₁.descendant X) (Q₂.descendant Y) hQ hside ρ₁ ρ₂
    (p-a) ((2:ℝ)^N) (one_le_pow₀ (by norm_num)) v τ δ H B D
    hτ hδ hδsmall hH hB hD hδD hnorm herr hfreq
    (profileModelMass m₁ N a) (profileModelMass m₂ N a)
    (profileModelMass m₁ N p) (profileModelMass m₂ N p) a p
    (hmass m₁ a) (hmass m₂ a) (hmass m₁ p) (hmass m₂ p)
    K w η hcap hη hpart b c hb hc (g₁-a) (g₂-a) L C₁ C₂
    (Nat.sub_le_sub_right hgp₁ a) (Nat.sub_le_sub_right hgp₂ a)
    hL W₁ W₂ hw₁ hw₂ hs₁ hs₂
  have hadd := add_le_add hbound (le_refl
    ((2:ℝ)^(((n+2:ℕ):ℝ)*(v-a)) *
      ((profileModelMass m₁ N p/profileModelMass m₁ N a)*
        (profileModelMass m₂ N p/profileModelMass m₂ N a))^2 *
      capGraphError (n+2) k A C W ((2:ℝ)^N) T
        (profileModelMass m₁ N p) (profileModelMass m₂ N p) H B D v τ K.card
        ((Q₁.descendant X).occupiedPaths ρ₁ (p-a) ×ˢ
          (Q₂.descendant Y).occupiedPaths ρ₂ (p-a)).card))
  exact hraw.trans (by simpa only [twoProfileGraphContribution,mul_assoc] using hadd)

end Falconer

end OAI

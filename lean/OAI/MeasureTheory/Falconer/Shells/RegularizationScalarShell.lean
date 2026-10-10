import OAI.MeasureTheory.Falconer.Shells.ClassPairShell
import OAI.MeasureTheory.Falconer.Shells.RegularClassShell

namespace OAI

/-! # Scalar shell decay after summing the actual regularized class pairs -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal SchwartzMap ContDiff

theorem exists_regularization_scalar_shell
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m : ℕ) {χ : ℝ} (hχ : 0 < χ)
    (φ : 𝓢(ℝ,ℂ)) (Ψ : ℝ → ℝ) (hφ : ∀ r, φ r = (Ψ r : ℂ))
    (hΨ : Measurable Ψ) (hsmooth : ContDiff ℝ ∞ Ψ)
    (hpos : ∀ r, 0 ≤ Ψ r) (hzero : ∀ r ≤ 0, Ψ r = 0)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    {V : ℝ} (hV : 0 ≤ V) (hΨV : ∀ r, Ψ r ≤ V)
    (hsupp : ∀ r, Ψ r ≠ 0 → r ∈ Ioo (1/4:ℝ) 4)
    (δ W : ℝ) (hδ : 0 < δ) (hW : 0 < W) :
    ∃ lam σ κ β : ℝ, 0 < lam ∧ 0 < σ ∧ lam ≤ σ ∧ 0 < κ ∧ 0 < β ∧
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ (Q₁ Q₂ : DyadicCube (m+3)), Q₁.side = 1 → Q₂.side = 1 →
      ∀ (μ ν : Measure (Space (m+3))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ (B₁ B₂ : ℕ) (t₁ t₂ : ℝ≥0∞), 0 < t₁ → 0 < t₂ →
      ∀ p₁ p₂ : List ℕ → CellPath (m+3),
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁, regularizationLabel Q₁ μ N B₁ (p₁ T) = T) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂, regularizationLabel Q₂ ν N B₂ (p₂ T) = T) →
      (∀ T ∈ regularizationIndex Q₁ μ N B₁ t₁,
        RegularizedProfileData Q₁ (sourceClass Q₁ μ N B₁ (p₁ T)) N ((m+3:ℕ)/2+χ) lam
          (sourceUnitProfile Q₁ μ N B₁ (p₁ T))) →
      (∀ T ∈ regularizationIndex Q₂ ν N B₂ t₂,
        RegularizedProfileData Q₂ (sourceClass Q₂ ν N B₂ (p₂ T)) N ((m+3:ℕ)/2+χ) lam
          (sourceUnitProfile Q₂ ν N B₂ (p₂ T))) →
      (∀ᵐ z ∂μ.prod ν, δ ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ W) →
      (∀ᵐ z : Space (m+3) × Space (m+3) ∂μ.prod ν,
        ‖NormedSpace.normalize (z.1-z.2)-(gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/8) →
      ∃ c : List ℕ × List ℕ → ℕ,
        (∀ i ∈ (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂), c i ≤ N) ∧
        ∀ (k : ℕ) (A D : Fin k → Set (Space (m+3))),
          (∀ j, MeasurableSet (A j) ∧ MeasurableSet (D j)) →
          (Pairwise fun j l => Disjoint (A j ×ˢ D j) (A l ×ˢ D l)) →
          PlanarFalconer.shellEnergy
            (regularizationPairDistance Q₁ Q₂ μ ν N B₁ B₂ t₁ t₂ σ κ p₁ p₂ c (⋃ j, A j ×ˢ D j)) N ≤
              2*(k:ℝ)^2*((2:ℝ)^N)^(-β/16) := by
  classical
  obtain ⟨lam,σ,κ,β,hlam,hσ,hlamσ,hκ,hβ,N₀,hN₀,hmain⟩ :=
    exists_regular_class_shell hgnomonic hquadratic m hχ φ Ψ hφ hΨ hsmooth
      hpos hzero hone hV hΨV hsupp δ W hδ hW
  refine ⟨lam,σ,κ,β,hlam,hσ,hlamσ,hκ,hβ,N₀,hN₀,?_⟩
  intro N hN Q₁ Q₂ hQ₁ hQ₂ μ ν _ _ B₁ B₂ t₁ t₂ ht₁ ht₂ p₁ p₂ he₁ he₂ hreg₁ hreg₂ hsep hnear
  let I := (regularizationIndex Q₁ μ N B₁ t₁).product (regularizationIndex Q₂ ν N B₂ t₂)
  have hside₁ : 0 < Q₁.side := by rw [hQ₁]; norm_num
  have hside₂ : 0 < Q₂.side := by rw [hQ₂]; norm_num
  have hex (i : List ℕ × List ℕ) (hi : i ∈ I) :
      ∃ c : ℕ, c ≤ N ∧ ∀ A D : Set (Space (m+3)), MeasurableSet A → MeasurableSet D →
      (∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)),
        ‖charFun (endpointWeightedDistance ((sourceClass Q₁ μ N B₁ (p₁ i.1)).restrict A)
          ((sourceClass Q₂ ν N B₂ (p₂ i.2)).restrict D) 1 1 1
          (sourceOuterMask Q₁ μ N B₁ σ κ (p₁ i.1) c)
          (sourceOuterMask Q₂ ν N B₂ σ κ (p₂ i.2) c)) r‖^2) ≤ ((2:ℝ)^N)^(-β/16) := by
    have hi₁ := (Finset.mem_product.mp hi).1
    have hi₂ := (Finset.mem_product.mp hi).2
    let : IsProbabilityMeasure (sourceClass Q₁ μ N B₁ (p₁ i.1)) := (hreg₁ i.1 hi₁).probability
    let : IsProbabilityMeasure (sourceClass Q₂ ν N B₂ (p₂ i.2)) := (hreg₂ i.2 hi₂).probability
    have hac := (sourceClass_absolutelyContinuous Q₁ μ N B₁ (p₁ i.1)).prod
      (sourceClass_absolutelyContinuous Q₂ ν N B₂ (p₂ i.2))
    obtain ⟨c,hc,_hw,_hclo,hb⟩ := hmain N hN Q₁ Q₂ hQ₁ hQ₂ _ _ _ _
      (hreg₁ i.1 hi₁) (hreg₂ i.2 hi₂)
      (sourceClass_parent Q₁ hside₁ μ N B₁ (p₁ i.1))
      (sourceClass_parent Q₂ hside₂ ν N B₂ (p₂ i.2)) (hac.ae_le hsep) (hac.ae_le hnear)
    exact ⟨c,by omega,hb⟩
  let c : List ℕ × List ℕ → ℕ := fun i => if hi : i ∈ I then (hex i hi).choose else 0
  have hc (i : List ℕ × List ℕ) (hi : i ∈ I) : c i ≤ N := by
    simpa only [c,dite_eq_left hi] using (hex i hi).choose_spec.1
  refine ⟨c,hc,?_⟩
  intro k A D hm hd
  apply regularizationPairDistance_shell_le (by omega) Q₁ Q₂ hside₁ hside₂ μ ν N B₁ B₂
    t₁ t₂ ht₁ ht₂ σ κ p₁ p₂ he₁ he₂ c A D hm hd hδ (hsep.mono fun _ h => h.1) (by positivity)
  intro i hi j
  have hb := (hex i hi).choose_spec.2 (A j) (D j) (hm j).1 (hm j).2
  simpa only [c,I,dite_eq_left hi] using hb

end Falconer.Regularization

end OAI

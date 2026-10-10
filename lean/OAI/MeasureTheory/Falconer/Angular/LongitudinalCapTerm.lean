import OAI.MeasureTheory.Falconer.Radial.RadialPairSwap
import OAI.MeasureTheory.Falconer.Geometry.NonstationaryGeometry

namespace OAI

/-!
# The longitudinal discarded cap term

The failed test is imposed on the two fixed cap centers and cell-center
displacements. Cap support and point-replacement errors transfer it to the
actual phase. Radial Fubini then applies Schwartz decay before any absolute
values are taken in the cell expansion.
-/

namespace Falconer
open Set MeasureTheory
open scoped SchwartzMap

theorem longitudinal_discarded_cap_term_bound {d : ℕ} {X : Type*} [MeasurableSpace X]
    (φ : 𝓢(ℝ, ℂ)) (Ψ : ℝ → ℝ)
    (hφ : ∀ u, φ u = (Ψ u : ℂ)) (hΨ : Measurable Ψ)
    (hpos : ∀ u, 0 ≤ Ψ u) (hzero : ∀ u ≤ 0, Ψ u = 0)
    {W : ℝ} (hW : 0 ≤ W) (hΨW : ∀ t, Ψ t ≤ W) (hz : ∀ t, 4 < t → Ψ t = 0)
    {α : ℝ} (hα : 0 < α) (T : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (μ : Measure X) [IsFiniteMeasure μ], ∀ R : ℝ, 1 ≤ R → ∀ v τ δ : ℝ,
      0 ≤ δ → 4*Real.pi*R^α ≤ (2 : ℝ)^v*τ →
      ∀ (w₁ w₂ d₁ d₂ : Space d),
      τ < |inner ℝ w₁ d₁+inner ℝ w₂ d₂| →
      ∀ (v₁ v₂ : X → Space d), Measurable v₁ → Measurable v₂ →
      ∀ (b₁ b₂ : X → Sphere d → ℂ),
      Measurable (Function.uncurry b₁) → Measurable (Function.uncurry b₂) →
      (∀ x z, b₁ x z ≠ 0 → ‖(z : Space d)-w₁‖ ≤ δ) →
      (∀ x z, b₂ x z ≠ 0 → ‖(z : Space d)-w₂‖ ≤ δ) →
      (∀ x, (∃ z, b₁ x z ≠ 0) → (∃ z, b₂ x z ≠ 0) →
        (‖v₁ x-d₁‖+δ*‖d₁‖)+(‖v₂ x-d₂‖+δ*‖d₂‖) ≤ τ/2) →
      ∀ B₁ B₂ : ℝ, 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ x z, ‖b₁ x z‖ ≤ B₁) → (∀ x z, ‖b₂ x z‖ ≤ B₂) →
      ‖expandedCapTerm μ v Ψ v₁ v₂ b₁ b₂‖ ≤
        B₁*B₂*A*((sphereMeasure d).real univ)^2*μ.real univ*R^(-T) := by
  obtain ⟨A,hA,hdecay⟩ := radial_discarded_term_bound_uniform
    (X := (Sphere d × Sphere d) × X) φ Ψ hφ hΨ hpos hzero hα T
  refine ⟨A,hA,?_⟩
  intro μ hμ R hR v τ δ _hδ hfreq w₁ w₂ d₁ d₂ hbad v₁ v₂ hv₁ hv₂
    b₁ b₂ hb₁ hb₂ hcap₁ hcap₂ herr B₁ B₂ hB₁ hB₂ hbound₁ hbound₂
  rw [expandedCapTerm_radial_swap μ v Ψ hW hΨW hz v₁ v₂ hv₁ hv₂ b₁ b₂ hb₁ hb₂
    hB₁ hbound₁ hbound₂]
  let σ := ((sphereMeasure d).prod (sphereMeasure d)).prod μ
  have hh := hdecay σ R hR v
    (fun p : (Sphere d × Sphere d) × X => b₁ p.2 p.1.1*b₂ p.2 p.1.2)
    (fun p => inner ℝ (p.1.1 : Space d) (v₁ p.2)+inner ℝ (p.1.2 : Space d) (v₂ p.2))
    (B₁*B₂) (mul_nonneg hB₁ hB₂) (fun p => by
      rw [norm_mul]
      exact mul_le_mul (hbound₁ _ _) (hbound₂ _ _) (norm_nonneg _) hB₁) (by
      intro p hp
      obtain ⟨hp₁,hp₂⟩ := mul_ne_zero_iff.mp hp
      have he₁ := hcap₁ p.2 p.1.1 hp₁
      have he₂ := hcap₂ p.2 p.1.2 hp₂
      have he : (‖v₁ p.2-d₁‖+‖(p.1.1 : Space d)-w₁‖*‖d₁‖)+
          (‖v₂ p.2-d₂‖+‖(p.1.2 : Space d)-w₂‖*‖d₂‖) ≤ τ/2 := by
        apply le_trans _ (herr p.2 ⟨p.1.1,hp₁⟩ ⟨p.1.2,hp₂⟩)
        gcongr
      have hl := longitudinal_failure_nonstationary
        (sphere_norm p.1.1) (sphere_norm p.1.2) (v₁ p.2) (v₂ p.2) d₁ d₂ hbad he
      have ht : (2 : ℝ)^v*τ/2 ≤ (2 : ℝ)^v*
          |inner ℝ (p.1.1 : Space d) (v₁ p.2)+inner ℝ (p.1.2 : Space d) (v₂ p.2)| := by
        nlinarith [mul_le_mul_of_nonneg_left hl
          (le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<2) v))]
      linarith)
  apply hh.trans_eq
  dsimp only [σ]
  rw [show (univ : Set ((Sphere d × Sphere d) × X)) = univ ×ˢ univ by simp,
    measureReal_prod_prod]
  rw [show (univ : Set (Sphere d × Sphere d)) = univ ×ˢ univ by simp,
    measureReal_prod_prod]
  ring

end Falconer

end OAI

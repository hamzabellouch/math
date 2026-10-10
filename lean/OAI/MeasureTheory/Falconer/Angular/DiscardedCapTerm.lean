import OAI.MeasureTheory.Falconer.Angular.CapLocalization
import OAI.MeasureTheory.Falconer.Angular.AngularPairSwap
import OAI.MeasureTheory.Falconer.Shells.ShellNonstationary

namespace OAI

/-!
# The complete angular–radial error for one discarded cap term

Spatial labels remain in their original finite measure. The adapted frame
is fixed before these labels are integrated. The phase is the four-point
phase after the two displacements have been formed.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

theorem discarded_cap_term_bound {X : Type*} [MeasurableSpace X]
    (hpublished : PublishedGnomonicSurface) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (w d : Space (n+2)) (τ δ : ℝ),
      ‖w‖ = 1 → 0 < τ → 0 ≤ δ → δ ≤ 1/2 → τ < ‖perpendicularPart w d‖ →
      ∃ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), e (chartPole n) = w ∧
        ∀ (μ : Measure X) [IsFiniteMeasure μ] (v₁ v₂ : X → Space (n+2)),
          Measurable v₁ → Measurable v₂ →
          ∀ (b₁ b₂ : X → Sphere (n+2) → ℂ),
          Measurable (Function.uncurry b₁) → Measurable (Function.uncurry b₂) →
          (∀ x z, b₁ x z ≠ 0 → ‖(z : Space (n+2))-w‖ ≤ δ) →
          (∀ x y, ‖y‖ ≤ 1 → ContDiff ℝ ∞ (rotatedChartAmplitude e (b₁ x) y)) →
          ∀ (B₁ B₂ C D v : ℝ) (Ψ : ℝ → ℝ),
          0 ≤ B₁ → 0 ≤ B₂ → 0 ≤ C → 1 ≤ D →
          (∀ x z, ‖b₁ x z‖ ≤ B₁) → (∀ x z, ‖b₂ x z‖ ≤ B₂) →
          (∀ x, (∃ z, b₁ x z ≠ 0) → ‖v₁ x‖ ≤ (τ/4)*D) →
          (∀ x, (∃ z, b₁ x z ≠ 0) → ‖v₁ x-d‖+8*δ*‖d‖ ≤ τ/2) →
          (∀ k ≤ m, ∀ x y, ‖y‖ ≤ 1 → ∀ u ∈ tsupport (rotatedChartAmplitude e (b₁ x) y),
            ‖iteratedDeriv k (rotatedChartAmplitude e (b₁ x) y) u‖ ≤ C*D^k) →
          Measurable Ψ → (∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4 : ℝ) 4) →
          ∀ W : ℝ, 0 ≤ W → (∀ t, Ψ t ≤ W) →
          ‖∫ r, ∫ z : Sphere (n+2) × Sphere (n+2), ∫ x,
            Complex.exp (Complex.I*(r : ℂ)*
              ((inner ℝ (z.1 : Space (n+2)) (v₁ x) : ℂ)+
               (inner ℝ (z.2 : Space (n+2)) (v₂ x) : ℂ))) * b₁ x z.1 * b₂ x z.2
            ∂μ ∂(sphereMeasure (n+2)).prod (sphereMeasure (n+2))
            ∂PlanarFalconer.sourceAngularShellMeasure v Ψ‖ ≤
          (A*C*B₂*(sphereMeasure (n+2)).real univ*μ.real univ) *
            (16*D/((2 : ℝ)^v*τ))^m*(4*W) := by
  obtain ⟨A,hA,he⟩ := failed_cap_sphere_nonstationary hpublished n m hn
  refine ⟨A,hA,?_⟩
  intro w d τ δ hw hτ hδ hsmall hbad
  obtain ⟨e,hew,hest⟩ := he w d τ δ hw hτ hδ hsmall hbad
  refine ⟨e,hew,?_⟩
  intro μ hμ v₁ v₂ hv₁ hv₂ b₁ b₂ hb₁ hb₂ hcap hsmooth B₁ B₂ C D v Ψ
    hB₁ hB₂ hC hD hbound₁ hbound₂ hv herr hder hΨ hs W hW hΨW
  let F : ℝ → ℂ := fun r => ∫ z : Sphere (n+2) × Sphere (n+2), ∫ x,
    Complex.exp (Complex.I*(r : ℂ)*
      ((inner ℝ (z.1 : Space (n+2)) (v₁ x) : ℂ)+
       (inner ℝ (z.2 : Space (n+2)) (v₂ x) : ℂ))) * b₁ x z.1 * b₂ x z.2
    ∂μ ∂(sphereMeasure (n+2)).prod (sphereMeasure (n+2))
  have hfirst (r : ℝ) (hr : 0 < r) (x : X) :
      ‖∫ z, sphereOscillator r (v₁ x) z*b₁ x z ∂sphereMeasure (n+2)‖ ≤
        A*C*(D/(r*(τ/4)))^m := by
    by_cases hactive : ∃ z, b₁ x z ≠ 0
    · exact hest (v₁ x) (b₁ x) (hb₁.comp (measurable_const.prodMk measurable_id))
        (hcap x) (hsmooth x) B₁ C D r hC hD hr (hbound₁ x) (hv x hactive) (herr x hactive)
        (fun k hk y hy u hu => hder k hk x y hy u hu)
    · have hz : ∀ z, b₁ x z = 0 := by simpa only [not_exists,not_not] using hactive
      simp only [hz,mul_zero,integral_zero,norm_zero]
      positivity
  have hF (r : ℝ) (hr : (2 : ℝ)^v/4 < r) : ‖F r‖ ≤
      (A*C*B₂*(sphereMeasure (n+2)).real univ*μ.real univ)*(D/(r*(τ/4)))^m := by
    have hr0 : 0 < r := lt_trans (by positivity) hr
    have hswap := angular_pair_spatial_swap μ r v₁ v₂ hv₁ hv₂ b₁ b₂ hb₁ hb₂
      hB₁ hB₂ hbound₁ hbound₂
    have heq : F r = ∫ x, ∫ z : Sphere (n+2) × Sphere (n+2),
        Complex.exp (Complex.I*(r : ℂ)*
          ((inner ℝ (z.1 : Space (n+2)) (v₁ x) : ℂ)+
           (inner ℝ (z.2 : Space (n+2)) (v₂ x) : ℂ))) * b₁ x z.1 * b₂ x z.2
        ∂(sphereMeasure (n+2)).prod (sphereMeasure (n+2)) ∂μ := by
      rw [show F r = _ from hswap]
      apply integral_congr_ae
      filter_upwards with x
      exact (angular_pair_factorization r (v₁ x) (v₂ x) (b₁ x) (b₂ x)).symm
    rw [heq]
    apply (angular_pair_outer_bound μ r v₁ v₂ b₁ b₂ (by positivity)
      (hfirst r hr0) hbound₂).trans_eq
    ring
  have hh := shell_nonstationary_integral_bound v Ψ hΨ hs hW hΨW F m
    (show 0 ≤ A*C*B₂*(sphereMeasure (n+2)).real univ*μ.real univ by positivity)
    (zero_le_one.trans hD) (show 0 < τ/4 by positivity) hF
  convert hh using 1
  congr 2
  congr 1
  field_simp
  ring

end Falconer

end OAI

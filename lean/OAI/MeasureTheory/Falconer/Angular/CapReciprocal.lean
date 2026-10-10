import OAI.MeasureTheory.Falconer.Angular.CapDenominator

namespace OAI

/-! # Derivatives of the cap normalization factor -/

namespace Falconer
open Set
open scoped ContDiff Topology

noncomputable def capReciprocal {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (S : Finset (Sphere d)) (x : Space d) : ℝ :=
  smoothReciprocal 1 zero_lt_one (capDenominator δ hδ S x)

theorem capReciprocal_contDiff {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) : ContDiff ℝ ∞ (capReciprocal δ hδ S) :=
  (smoothReciprocal_contDiff 1 zero_lt_one).comp (capDenominator_contDiff hδ S)

theorem capDenominator_mul_reciprocal {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    capDenominator δ hδ S w * capReciprocal δ hδ S w = 1 := by
  exact smoothReciprocal_eq zero_lt_one
    ((capDenominator_ge_one hδ S hcover w).trans (le_abs_self _))

theorem capReciprocal_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  choose B hB hBb using (fun k => capDenominator_chart_derivatives n k)
  obtain ⟨C,hC,hCb⟩ := reciprocal_germ_derivatives B hB m
  refine ⟨C,hC,?_⟩
  intro δ hδ hδ1 S hsep hcover e y hy u hu
  let g : ℝ → ℝ := fun t => capDenominator δ hδ S (rotatedChartCurve e y t)
  let q : ℝ → ℝ := fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)
  have hg : ContDiff ℝ ∞ g := (capDenominator_contDiff hδ S).comp (rotatedChartCurve_contDiff e y)
  have hq : ContDiff ℝ ∞ q := (capReciprocal_contDiff hδ S).comp (rotatedChartCurve_contDiff e y)
  have hw (t : ℝ) : rotatedChartCurve e y t ∈ Metric.sphere (0 : Space (n+2)) 1 := by
    simp only [Metric.mem_sphere,dist_zero_right,rotatedChartCurve_norm]
  have hg1 (t : ℝ) : 1 ≤ g t := capDenominator_ge_one hδ S hcover ⟨_,hw t⟩
  have he : (fun t => q t*g t) =ᶠ[𝓝 u] (fun _ => 1) := Filter.Eventually.of_forall (by
    intro t
    simpa only [g,q,mul_comm] using capDenominator_mul_reciprocal hδ S hcover ⟨_,hw t⟩)
  have hh := hCb g q hg hq 1 δ⁻¹ u zero_lt_one (inv_nonneg.mpr hδ.le)
    ((hg1 u).trans (le_abs_self _)) he (by
      intro k _hk _hkm
      simpa only [mul_one] using hBb k δ hδ hδ1 S hsep e y hy u hu)
  simpa only [inv_one,mul_one] using hh

end Falconer

end OAI

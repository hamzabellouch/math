import OAI.MeasureTheory.Falconer.Fourier.CellSymbols
import OAI.MeasureTheory.Falconer.Angular.QuantitativeCaps

namespace OAI

/-!
# Finite derivative data for the graph localization

These records express cap and endpoint regularity bounds. They contain no oscillatory estimate or incidence conclusion.
Spatial cell indicators preserve all the required angular derivative bounds.
-/

namespace Falconer
open Set MeasureTheory
open scoped ContDiff

structure ChartSymbolControl {n : ℕ} (m : ℕ)
    (b : Space (n+2) → Sphere (n+2) → ℂ) (B D : ℝ) : Prop where
  measurable : Measurable (Function.uncurry b)
  bound : ∀ x w, ‖b x w‖ ≤ B
  smooth : ∀ x (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n),
    ContDiff ℝ ∞ (rotatedChartAmplitude e (b x) y)
  derivative : ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)), ∀ k ≤ m,
    ∀ x (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
    ‖iteratedDeriv k (rotatedChartAmplitude e (b x) y) u‖ ≤ B*D^k

structure ChartCapControl {n : ℕ} (m : ℕ) (η : Sphere (n+2) → ℝ)
    (w : Space (n+2)) (δ H : ℝ) : Prop where
  measurable : Measurable η
  bound : ∀ z, |η z| ≤ 1
  support : ∀ z, η z ≠ 0 → ‖(z : Space (n+2))-w‖ ≤ δ
  smooth : ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n),
    ContDiff ℝ ∞ (rotatedChartAmplitude e (fun z => (η z : ℂ)) y)
  derivative : ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)), ∀ k ≤ m,
    ∀ (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
    ‖iteratedDeriv k (rotatedChartAmplitude e (fun z => (η z : ℂ)) y) u‖ ≤ H*(δ⁻¹)^k

theorem ChartSymbolControl.cell {n m : ℕ}
    {b : Space (n+2) → Sphere (n+2) → ℂ} {B D : ℝ}
    (h : ChartSymbolControl m b B D) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (Q : DyadicCube (n+2)) : ChartSymbolControl m (cellSymbol Q b) B D := by
  classical
  refine ⟨cellSymbol_measurable Q b h.measurable,
    cellSymbol_bound Q b hB h.bound,?_,?_⟩
  · intro x e y
    exact cellSymbol_chart_smooth Q e b x y (fun _ => h.smooth x e y)
  · intro e k hk x y hy u hu
    by_cases hx : x ∈ Q.carrier
    · have he : cellSymbol Q b x = b x := by funext w; simp [cellSymbol,hx]
      rw [he]
      exact h.derivative e k hk x y hy u hu
    · have he : cellSymbol Q b x = fun _ => 0 := by funext w; simp [cellSymbol,hx]
      rw [he]
      have hzero : rotatedChartAmplitude e (fun _ => (0 : ℂ)) y = fun _ => 0 := rfl
      rw [hzero]
      simp only [iteratedDeriv_const,ite_self,norm_zero]
      exact mul_nonneg hB (pow_nonneg hD k)

/-- The finite cap partition supplies the cap regularity bounds. -/
theorem exists_controlled_cap_partition (n m : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ (S : Finset (Sphere (n+2))) (η : Sphere (n+2) → Sphere (n+2) → ℝ),
        (S.card : ℝ) ≤ (4/δ+1)^(n+2) ∧
        (∀ w, ∑ c ∈ S, η c w = 1) ∧
        (∀ c ∈ S, ∀ w, 0 ≤ η c w) ∧
        ∀ c ∈ S, ChartCapControl m (η c) (c : Space (n+2)) δ H := by
  obtain ⟨H,hH,hmain⟩ := quantitative_smooth_cap_partition n m
  refine ⟨H,hH,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,η,hcard,_hoverlap,hmeas,hpart,hbound,hsupp,hsmooth,hder⟩ := hmain δ hδ hδ1
  refine ⟨S,η,hcard,hpart,(fun c hc w => (hbound c hc w).1),?_⟩
  intro c hc
  refine ⟨hmeas c,?_,hsupp c hc,hsmooth c,?_⟩
  · intro w
    rw [abs_of_nonneg (hbound c hc w).1]
    exact (hbound c hc w).2
  · intro e k hk y hy u hu
    exact hder c e y hy u hu k hk

end Falconer

end OAI

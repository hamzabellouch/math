import OAI.MeasureTheory.Falconer.Angular.NormalizedCaps

namespace OAI

/-!
# Quantitative smooth cap partition on the sphere

This supplies the actual partition used in angular localization, with
uniform derivatives, a polynomial global count, and bounded local overlap.
It contains no Fourier or incidence estimate as an assumption.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem normalizedCap_complex_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv m (rotatedChartAmplitude e
        (fun w => (normalizedCap δ hδ S c w : ℂ)) y) u‖ ≤ B*(δ⁻¹)^m := by
  obtain ⟨B,hB,hBb⟩ := normalizedCap_chart_derivatives n m
  refine ⟨B,hB,?_⟩
  intro δ hδ hδ1 S hsep hcover c e y hy u hu
  let f : ℝ → ℝ := fun t => normalizedCap δ hδ S c (rotatedChartCurve e y t)
  have hf : ContDiff ℝ ∞ f :=
    (normalizedCap_contDiff hδ S c).comp (rotatedChartCurve_contDiff e y)
  have hn := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (hf.contDiffAt (x := u))
    (show (m : ℕ∞ω) ≤ ∞ by simp)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    Real.norm_eq_abs] at hn
  change ‖iteratedDeriv m (Complex.ofRealLI ∘ f) u‖ ≤ _
  rw [hn]
  exact hBb δ hδ hδ1 S hsep hcover c e y hy u hu

theorem quantitative_smooth_cap_partition (n m : ℕ) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      ∃ (S : Finset (Sphere (n+2))) (η : Sphere (n+2) → Sphere (n+2) → ℝ),
        (S.card : ℝ) ≤ (4/δ+1)^(n+2) ∧
        (∀ w, ((S.filter (fun c => dist w c ≤ δ)).card : ℝ) ≤ (5 : ℝ)^(n+2)) ∧
        (∀ c, Measurable (η c)) ∧
        (∀ w, ∑ c ∈ S, η c w = 1) ∧
        (∀ c ∈ S, ∀ w, 0 ≤ η c w ∧ η c w ≤ 1) ∧
        (∀ c ∈ S, ∀ w, η c w ≠ 0 → ‖(w : Space (n+2))-(c : Space (n+2))‖ ≤ δ) ∧
        (∀ c, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n,
          ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η c w : ℂ)) y)) ∧
        (∀ c, ∀ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), ∀ y : Space n, ‖y‖ ≤ 1 →
          ∀ u ∈ Icc (-1 : ℝ) 1, ∀ k ≤ m,
          ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => (η c w : ℂ)) y) u‖ ≤ H*(δ⁻¹)^k) := by
  classical
  choose B hB hBb using (fun k => normalizedCap_complex_chart_derivatives n k)
  let H := ∑ k ∈ Finset.range (m+1), B k
  have hH : 0 ≤ H := Finset.sum_nonneg (fun k _ => hB k)
  refine ⟨H,hH,?_⟩
  intro δ hδ hδ1
  obtain ⟨S,hsep,hcover,hcard,hoverlap⟩ := finite_separated_cap_net (n+2) hδ
  obtain ⟨hpart,hbounds,hsupport⟩ := normalizedCap_properties hδ S hcover
  refine ⟨S,fun c w => normalizedCap δ hδ S c w,hcard,hoverlap,?_,hpart,hbounds,
    (fun c hc w => hsupport c hc w),?_,?_⟩
  · intro c
    exact (normalizedCap_contDiff hδ S c).continuous.measurable.comp continuous_subtype_val.measurable
  · intro c e y
    exact ambient_symbol_chart_smooth e (fun x => (normalizedCap δ hδ S c x : ℂ))
      (Complex.ofRealCLM.contDiff.comp (normalizedCap_contDiff hδ S c)) y
  · intro c e y hy u hu k hkm
    apply (hBb k δ hδ hδ1 S (fun x hx y hy hxy => (hsep x hx y hy hxy).le)
      hcover c e y hy u hu).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (by omega))

end Falconer

end OAI

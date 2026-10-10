import OAI.MeasureTheory.Falconer.Fourier.SmoothMask

namespace OAI

/-!
# Uniform derivative bounds for buffered angular masks

Selecting any subcollection of the partition preserves the same derivative
scale. The bound uses local overlap; it does not grow with the number of
selected caps or depend on the geometry of the good set.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem normalizedCap_rotated_derivative_zero {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere (n+2))) (c : Sphere (n+2))
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n) (u : ℝ)
    (hfar : δ < ‖rotatedChartCurve e y u-(c : Space (n+2))‖) (m : ℕ) :
    iteratedDeriv m (fun t => normalizedCap δ hδ S c (rotatedChartCurve e y t)) u = 0 := by
  have hb : ContDiff ℝ ∞ (fun t => capBump δ hδ c (rotatedChartCurve e y t)) :=
    (capBump δ hδ c).contDiff.comp (rotatedChartCurve_contDiff e y)
  have hq : ContDiff ℝ ∞ (fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)) :=
    (capReciprocal_contDiff hδ S).comp (rotatedChartCurve_contDiff e y)
  change iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)*
    capReciprocal δ hδ S (rotatedChartCurve e y t)) u = 0
  rw [iteratedDeriv_fun_mul ((hb.of_le (by simp)).contDiffAt) ((hq.of_le (by simp)).contDiffAt)]
  apply Finset.sum_eq_zero
  intro k _
  rw [capBump_rotated_derivative_zero hδ c e y u hfar k,mul_zero,zero_mul]

theorem capCutoffAmbient_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (U : Set (Sphere (n+2)))
      (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => capCutoffAmbient δ hδ S U (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  classical
  obtain ⟨C,hC,hCb⟩ := normalizedCap_chart_derivatives n m
  refine ⟨5^(n+2)*C,by positivity,?_⟩
  intro δ hδ hδ1 S hsep hcover U e y hy u hu
  let S₀ := cutoffCapCenters δ S U
  let w : Sphere (n+2) := sphereMap e (gnomonicChart (coordinateJoin y u))
  let T := S₀.filter (fun c => dist w c ≤ δ)
  let f : Sphere (n+2) → ℝ := fun c =>
    iteratedDeriv m (fun t => normalizedCap δ hδ S c (rotatedChartCurve e y t)) u
  have hsub : S₀ ⊆ S := Finset.filter_subset _ _
  have hdiff (c : Sphere (n+2)) :
      ContDiff ℝ ∞ (fun t => normalizedCap δ hδ S c (rotatedChartCurve e y t)) :=
    (normalizedCap_contDiff hδ S c).comp (rotatedChartCurve_contDiff e y)
  have hzero (c : Sphere (n+2)) (hc : c ∈ S₀) (hct : c ∉ T) : f c = 0 := by
    have hdist : δ < dist w c := lt_of_not_ge (fun h => hct (Finset.mem_filter.mpr ⟨hc,h⟩))
    exact normalizedCap_rotated_derivative_zero hδ S c e y u hdist m
  have hsum : (∑ c ∈ S₀, f c) = ∑ c ∈ T, f c := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  change |iteratedDeriv m (fun t => ∑ c ∈ S₀, normalizedCap δ hδ S c (rotatedChartCurve e y t)) u| ≤ _
  rw [iteratedDeriv_fun_sum (fun c _ => ((hdiff c).of_le (by simp)).contDiffAt)]
  change |∑ c ∈ S₀, f c| ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ T, |f c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ T, C*(δ⁻¹)^m := Finset.sum_le_sum
      (fun c _ => hCb δ hδ hδ1 S hsep hcover c e y hy u hu)
    _ = (T.card : ℝ)*(C*(δ⁻¹)^m) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 5^(n+2)*(C*(δ⁻¹)^m) := mul_le_mul_of_nonneg_right
      (separated_sphere_overlap S₀ hδ
        (fun x hx z hz hne => hsep x (hsub hx) z (hsub hz) hne) w) (by positivity)
    _ = _ := by ring

end Falconer

end OAI

import OAI.MeasureTheory.Falconer.Fourier.ChartBumps

namespace OAI

/-!
# Uniform bounds for the cap partition denominator

Only centers whose closed cap contains the point contribute to a derivative.
The proved local packing bound therefore controls the sum independently of
the total number of caps.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def capDenominator {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (S : Finset (Sphere d)) (x : Space d) : ℝ :=
  ∑ c ∈ S, capBump δ hδ c x

theorem capDenominator_contDiff {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) : ContDiff ℝ ∞ (capDenominator δ hδ S) :=
  ContDiff.sum (fun c _ => (capBump δ hδ c).contDiff)

theorem capDenominator_ge_one {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) (w : Sphere d) :
    1 ≤ capDenominator δ hδ S w := by
  obtain ⟨c,hc,hwc⟩ := hcover w
  have hval : capBump δ hδ c w = 1 :=
    (capBump δ hδ c).one_of_mem_closedBall (Metric.mem_closedBall.mpr hwc)
  calc
    1 = capBump δ hδ c w := hval.symm
    _ ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc

theorem capDenominator_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (y : Space n), ‖y‖ ≤ 1 →
      ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => capDenominator δ hδ S (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  classical
  obtain ⟨C,hC,hCb⟩ := capBump_rotated_derivatives n m
  refine ⟨5^(n+2)*C,by positivity,?_⟩
  intro δ hδ hδ1 S hsep e y hy u hu
  let w : Sphere (n+2) := sphereMap e (gnomonicChart (coordinateJoin y u))
  let T := S.filter (fun c => dist w c ≤ δ)
  let f : Sphere (n+2) → ℝ := fun c =>
    iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u
  have hdiff (c : Sphere (n+2)) :
      ContDiff ℝ ∞ (fun t => capBump δ hδ c (rotatedChartCurve e y t)) :=
    (capBump δ hδ c).contDiff.comp (rotatedChartCurve_contDiff e y)
  have hzero (c : Sphere (n+2)) (hc : c ∈ S) (hct : c ∉ T) : f c = 0 := by
    have hdist : δ < dist w c := lt_of_not_ge (fun h => hct (Finset.mem_filter.mpr ⟨hc,h⟩))
    exact capBump_rotated_derivative_zero hδ c e y u hdist m
  have hsum : (∑ c ∈ S, f c) = ∑ c ∈ T, f c := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  change |iteratedDeriv m (fun t => ∑ c ∈ S, capBump δ hδ c (rotatedChartCurve e y t)) u| ≤ _
  rw [iteratedDeriv_fun_sum (fun c _ => ((hdiff c).of_le (by simp)).contDiffAt)]
  change |∑ c ∈ S, f c| ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ T, |f c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ T, C*(δ⁻¹)^m := Finset.sum_le_sum (fun c _ => hCb δ hδ hδ1 c e y hy u hu)
    _ = (T.card : ℝ)*(C*(δ⁻¹)^m) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 5^(n+2)*(C*(δ⁻¹)^m) := mul_le_mul_of_nonneg_right
      (separated_sphere_overlap S hδ hsep w) (by positivity)
    _ = _ := by ring

end Falconer

end OAI

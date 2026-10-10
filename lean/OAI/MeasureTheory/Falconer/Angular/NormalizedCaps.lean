import OAI.MeasureTheory.Falconer.Angular.CapReciprocal

namespace OAI

/-!
# The normalized cap partition and its uniform derivative bounds

The normalization uses the same fixed smooth reciprocal for all radii.
On the sphere the covering bound makes it the exact reciprocal of the
positive bump sum.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def normalizedCap {d : ℕ} (δ : ℝ) (hδ : 0 < δ)
    (S : Finset (Sphere d)) (c : Sphere d) (x : Space d) : ℝ :=
  capBump δ hδ c x * capReciprocal δ hδ S x

theorem normalizedCap_contDiff {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (c : Sphere d) : ContDiff ℝ ∞ (normalizedCap δ hδ S c) :=
  (capBump δ hδ c).contDiff.mul (capReciprocal_contDiff hδ S)

theorem normalizedCap_properties {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d))
    (hcover : ∀ w : Sphere d, ∃ c ∈ S, dist w c ≤ δ/2) :
    (∀ w : Sphere d, ∑ c ∈ S, normalizedCap δ hδ S c w = 1) ∧
    (∀ c ∈ S, ∀ w : Sphere d, 0 ≤ normalizedCap δ hδ S c w ∧
      normalizedCap δ hδ S c w ≤ 1) ∧
    (∀ c ∈ S, ∀ x : Space d, normalizedCap δ hδ S c x ≠ 0 → ‖x-(c : Space d)‖ ≤ δ) := by
  have hrec (w : Sphere d) : capReciprocal δ hδ S w = (capDenominator δ hδ S w)⁻¹ := by
    have hg : capDenominator δ hδ S w ≠ 0 :=
      ne_of_gt (zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w))
    apply mul_left_cancel₀ hg
    rw [capDenominator_mul_reciprocal hδ S hcover w,mul_inv_cancel₀ hg]
  refine ⟨?_,?_,?_⟩
  · intro w
    simpa only [normalizedCap,← Finset.sum_mul,capDenominator] using
      capDenominator_mul_reciprocal hδ S hcover w
  · intro c hc w
    have hb : capBump δ hδ c w ≤ capDenominator δ hδ S w :=
      Finset.single_le_sum (fun c _ => (capBump δ hδ c).nonneg) hc
    have hg : 0 < capDenominator δ hδ S w :=
      zero_lt_one.trans_le (capDenominator_ge_one hδ S hcover w)
    simp only [normalizedCap,hrec]
    exact ⟨mul_nonneg (capBump δ hδ c).nonneg (inv_nonneg.mpr hg.le),
      (mul_inv_le_iff₀ hg).mpr (by simpa only [one_mul] using hb)⟩
  · intro c _ x hx
    have hb : capBump δ hδ c x ≠ 0 := (mul_ne_zero_iff.mp hx).1
    have hm : x ∈ Metric.ball (c : Space d) δ := by
      change x ∈ Metric.ball (c : Space d) (capBump δ hδ c).rOut
      rw [← (capBump δ hδ c).support_eq]
      exact hb
    exact (mem_ball_iff_norm.mp hm).le

theorem normalizedCap_chart_derivatives (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 →
      ∀ (S : Finset (Sphere (n+2))),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      (∀ w : Sphere (n+2), ∃ c ∈ S, dist w c ≤ δ/2) →
      ∀ (c : Sphere (n+2)) (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2))
      (y : Space n), ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv m (fun t => normalizedCap δ hδ S c (rotatedChartCurve e y t)) u| ≤
        B*(δ⁻¹)^m := by
  choose B hB hBb using (fun k => capBump_rotated_derivatives n k)
  choose Q hQ hQb using (fun k => capReciprocal_chart_derivatives n k)
  let A := ∑ k ∈ Finset.range (m+1), (m.choose k : ℝ)*B k*Q (m-k)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB k)) (hQ (m-k)))
  refine ⟨A,hA,?_⟩
  intro δ hδ hδ1 S hsep hcover c e y hy u hu
  have hb : ContDiff ℝ ∞ (fun t => capBump δ hδ c (rotatedChartCurve e y t)) :=
    (capBump δ hδ c).contDiff.comp (rotatedChartCurve_contDiff e y)
  have hq : ContDiff ℝ ∞ (fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)) :=
    (capReciprocal_contDiff hδ S).comp (rotatedChartCurve_contDiff e y)
  change |iteratedDeriv m (fun t => capBump δ hδ c (rotatedChartCurve e y t)*
    capReciprocal δ hδ S (rotatedChartCurve e y t)) u| ≤ _
  rw [iteratedDeriv_fun_mul ((hb.of_le (by simp)).contDiffAt) ((hq.of_le (by simp)).contDiffAt)]
  calc
    _ ≤ ∑ k ∈ Finset.range (m+1), |(m.choose k : ℝ)*
        iteratedDeriv k (fun t => capBump δ hδ c (rotatedChartCurve e y t)) u*
        iteratedDeriv (m-k) (fun t => capReciprocal δ hδ S (rotatedChartCurve e y t)) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m+1), ((m.choose k : ℝ)*B k*Q (m-k))*(δ⁻¹)^m := by
      apply Finset.sum_le_sum
      intro k hk
      have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
      rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        _ ≤ (m.choose k : ℝ)*(B k*(δ⁻¹)^k)*(Q (m-k)*(δ⁻¹)^(m-k)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hBb k δ hδ hδ1 c e y hy u hu)
            (Nat.cast_nonneg _)) (hQb (m-k) δ hδ hδ1 S hsep hcover e y hy u hu)
            (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
              (mul_nonneg (hB k) (pow_nonneg (inv_nonneg.mpr hδ.le) k)))
        _ = _ := by
          have hp : (δ⁻¹)^k*(δ⁻¹)^(m-k) = (δ⁻¹)^m := by
            rw [← pow_add,Nat.add_sub_of_le hkm]
          calc
            _ = ((m.choose k : ℝ)*B k*Q (m-k))*((δ⁻¹)^k*(δ⁻¹)^(m-k)) := by ring
            _ = _ := by rw [hp]
    _ = A*(δ⁻¹)^m := (Finset.sum_mul _ _ _).symm

end Falconer

end OAI

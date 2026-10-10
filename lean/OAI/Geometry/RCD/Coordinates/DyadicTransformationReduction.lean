import OAI.Geometry.RCD.Coordinates.FiniteDepthNormalization
import OAI.Geometry.RCD.Coordinates.NormalizationComposition
import OAI.Geometry.RCD.Sobolev.BoundedDyadicScale

namespace OAI

/-! # Reduction of a failing radius to a first failing dyadic scale -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem exists_dyadic_comparison_scale {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (htR : t ≤ R) :
    ∃ j : ℕ, t ≤ R/(2 : ℝ)^j ∧ R/(2 : ℝ)^j < 2*t := by
  obtain ⟨j,hn,hc⟩ := exists_nat_pow_near_of_lt_one (div_pos ht hR)
    ((div_le_one hR).mpr htR) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ) < 1)
  have hp (i : ℕ) : (1/2 : ℝ)^i = ((2 : ℝ)^i)⁻¹ := by rw [one_div,inv_pow]
  have hu : t ≤ R/(2 : ℝ)^j := by
    have h := (div_le_iff₀ hR).mp hc
    rw [hp j] at h
    simpa only [div_eq_mul_inv,mul_comm] using h
  refine ⟨j,hu,?_⟩
  have h := (lt_div_iff₀ hR).mp hn
  rw [pow_succ,hp j] at h
  have he : ((2 : ℝ)^j)⁻¹*(1/2)*R = (R/(2 : ℝ)^j)/2 := by ring
  rw [he] at h
  linarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.dyadic_splitting_implies_all_scales {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ ∀ (p : X) (R : ℝ),
      0 < R → -1 ≤ K*(2*R)^2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n),
      FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (2*R) γ u v →
      (∀ j : ℕ, ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p (R/(2 : ℝ)^j) γ
          (transformedColumn (hausdorff n X) hX.quadratic u A)
          (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x))) →
      ∀ t : ℝ, 0 < t → t ≤ R → ∃ A : Euclidean n ≃L[ℝ] Euclidean n,
        FirstOrderSplittingOn (hausdorff n X) hX.quadratic p t β
          (transformedColumn (hausdorff n X) hX.quadratic u A)
          (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x)) ∧
        IsExactMeanNormalization (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic u) (ball p t) measurableSet_ball A := by
  obtain ⟨δ,hδ,hstep⟩ := hX.comparable_radius_splitting hn β hβ
  let γ := min δ 1
  have hγ : 0 < γ := lt_min hδ zero_lt_one
  refine ⟨γ,hγ,min_le_right _ _,?_⟩
  intro p R hR hK u v hfirst hframes t ht htR
  have hγδ : γ ≤ δ := min_le_left _ _
  by_cases hlarge : R/2 ≤ t
  · exact hstep p R hR hK u v
      (hfirst.mono_error _ _ hγ.le hγδ) t hlarge htR
  obtain ⟨j,hlo,hhi⟩ := exists_dyadic_comparison_scale (show 0 < R/2 by positivity) ht
    (le_of_not_ge hlarge)
  let s := (R/2)/(2 : ℝ)^j
  have hs : 0 < s := by dsimp only [s]; positivity
  have hsR : s ≤ R := by
    have hh : s ≤ R/2 := div_le_self (by positivity) (one_le_pow₀ (by norm_num))
    linarith
  have hsK : -1 ≤ K*(2*s)^2 := by
    have hsq : (2*s)^2 ≤ (2*R)^2 := (sq_le_sq₀ (by positivity) (by positivity)).mpr (by linarith)
    by_cases hK0 : 0 ≤ K
    · exact (by norm_num : (-1 : ℝ) ≤ 0).trans (mul_nonneg hK0 (sq_nonneg _))
    · exact hK.trans (mul_le_mul_of_nonpos_left hsq (le_of_not_ge hK0))
  obtain ⟨A,hA⟩ := hframes j
  have he : 2*s = R/(2 : ℝ)^j := by dsimp only [s]; ring
  rw [← he] at hA
  obtain ⟨B,hB,hBn⟩ := hstep p s hs hsK
    (transformedColumn (hausdorff n X) hX.quadratic u A)
    (fun x => (A : Euclidean n →L[ℝ] Euclidean n).adjoint (v x))
    (hA.mono_error _ _ hγ.le hγδ) t (by dsimp only [s]; linarith) hlo
  exact ⟨B.trans A,firstOrderSplitting_comp _ _ u A B v p t β hB,
    exact_mean_normalization_comp _ _ u A B (ball p t) measurableSet_ball hBn⟩

end RegularPointCoordinates

end

end OAI

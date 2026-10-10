import OAI.Geometry.CylinderCovering.Convexity.NormalFrameDefinitions

namespace OAI

noncomputable section
open Finset
open scoped BigOperators InnerProductSpace
namespace CylinderNormalFrame

theorem positive_mass_eq_negative_mass {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∑ i, x i = 0) :
    ∑ i, max (x i) 0 = ∑ i, max (-x i) 0 := by
  have hpoint (i : ι) : max (x i) 0 - max (-x i) 0 = x i := by
    by_cases hi : 0 ≤ x i
    · rw [max_eq_left hi, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (le_of_not_ge hi), max_eq_left (by linarith)]
      ring
  have hsum := congrArg (fun f : ι → ℝ => ∑ i, f i) (funext hpoint)
  simp only [sum_sub_distrib, hx] at hsum
  linarith

theorem sum_abs_eq_twice_positive_mass {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∑ i, x i = 0) :
    ∑ i, |x i| = 2 * ∑ i, max (x i) 0 := by
  have hpoint (i : ι) : |x i| = max (x i) 0 + max (-x i) 0 := by
    by_cases hi : 0 ≤ x i
    · rw [abs_of_nonneg hi, max_eq_left hi, max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonpos (le_of_not_ge hi), max_eq_right (le_of_not_ge hi),
        max_eq_left (by linarith)]
      ring
  simp_rw [hpoint, sum_add_distrib]
  rw [positive_mass_eq_negative_mass x hx]
  ring

theorem sum_sq_le_half_sq_sum_abs {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∑ i, x i = 0) :
    ∑ i, x i ^ 2 ≤ (∑ i, |x i|) ^ 2 / 2 := by
  have hpoint (i : ι) : x i ^ 2 = (max (x i) 0) ^ 2 + (max (-x i) 0) ^ 2 := by
    by_cases hi : 0 ≤ x i
    · rw [max_eq_left hi, max_eq_right (by linarith)]
      ring
    · rw [max_eq_right (le_of_not_ge hi), max_eq_left (by linarith)]
      ring
  have hp : ∑ i, (max (x i) 0) ^ 2 ≤ (∑ i, max (x i) 0) ^ 2 :=
    sum_sq_le_sq_sum_of_nonneg (fun i _ => le_max_right _ _)
  have hn : ∑ i, (max (-x i) 0) ^ 2 ≤ (∑ i, max (-x i) 0) ^ 2 :=
    sum_sq_le_sq_sum_of_nonneg (fun i _ => le_max_right _ _)
  rw [← positive_mass_eq_negative_mass x hx] at hn
  rw [sum_abs_eq_twice_positive_mass x hx]
  simp_rw [hpoint, sum_add_distrib]
  nlinarith

theorem sum_normal : ∑ i : Fin 4, normal i = 0 := by
  ext j
  fin_cases j <;> simp [normal, Fin.sum_univ_succ]

theorem inner_normal_zero (u : Space) :
    inner ℝ u (normal 0) = (Real.sqrt 2 * u 1 - u 2) / Real.sqrt 3 := by
  simp [normal, PiLp.inner_apply, Fin.sum_univ_succ, div_eq_mul_inv]
  ring

theorem inner_normal_one (u : Space) :
    inner ℝ u (normal 1) = (-Real.sqrt 2 * u 1 - u 2) / Real.sqrt 3 := by
  simp [normal, PiLp.inner_apply, Fin.sum_univ_succ, div_eq_mul_inv]
  ring

theorem inner_normal_two (u : Space) :
    inner ℝ u (normal 2) = (Real.sqrt 2 * u 0 + u 2) / Real.sqrt 3 := by
  simp [normal, PiLp.inner_apply, Fin.sum_univ_succ, div_eq_mul_inv]
  ring

theorem inner_normal_three (u : Space) :
    inner ℝ u (normal 3) = (-Real.sqrt 2 * u 0 + u 2) / Real.sqrt 3 := by
  simp [normal, PiLp.inner_apply, Fin.sum_univ_succ, div_eq_mul_inv]
  ring

theorem sum_sq_inner_normal (u : Space) :
    ∑ i : Fin 4, (inner ℝ u (normal i)) ^ 2 = (4 / 3 : ℝ) * ‖u‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_four, inner_normal_zero, inner_normal_one,
    inner_normal_two, inner_normal_three]
  simp only [Fin.sum_univ_three]
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [div_pow, h3]
  nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2)]

theorem normal_unit (i : Fin 4) : ‖normal i‖ = 1 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : ‖normal i‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;> norm_num [normal, Fin.sum_univ_succ, mul_pow, h3, h2]
  nlinarith [norm_nonneg (normal i)]

theorem frameCost_lower_bound (u : Space) (hu : ‖u‖ = 1) :
    Real.sqrt 2 ≤ frameCost u := by
  have hsum : ∑ i : Fin 4, inner ℝ u (normal i) = 0 := by
    rw [← inner_sum, sum_normal, inner_zero_right]
  have hsq := sum_sq_le_half_sq_sum_abs (fun i : Fin 4 => inner ℝ u (normal i)) hsum
  rw [sum_sq_inner_normal, hu] at hsq
  have hnonneg : 0 ≤ ∑ i : Fin 4, |inner ℝ u (normal i)| :=
    sum_nonneg (fun i _ => abs_nonneg _)
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Real.sqrt_le_iff.mpr
  constructor
  · unfold frameCost
    positivity
  · unfold frameCost
    nlinarith [sq_nonneg (∑ i : Fin 4, |inner ℝ u (normal i)|)]

theorem edgeDirection_unit : ‖edgeDirection‖ = 1 := by
  simp [edgeDirection, EuclideanSpace.norm_eq, Fin.sum_univ_succ]

theorem frameCost_edgeDirection : frameCost edgeDirection = Real.sqrt 2 := by
  have h3 : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have h2 : 0 ≤ Real.sqrt 2 / Real.sqrt 3 := by positivity
  simp only [frameCost, Fin.sum_univ_four, inner_normal_zero, inner_normal_one,
    inner_normal_two, inner_normal_three]
  simp [edgeDirection, abs_of_nonneg h2, neg_div]
  field_simp
  norm_num

theorem barycentricCost_lower_bound (u : BarycentricSpace)
    (hu : ‖u‖ = 1) (hsum : ∑ i : Fin 4, u i = 0) :
    1 / Real.sqrt 2 ≤ barycentricCost u := by
  have hsq := sum_sq_le_half_sq_sum_abs (fun i : Fin 4 => u i) hsum
  rw [← EuclideanSpace.real_norm_sq_eq, hu] at hsq
  have hnonneg : 0 ≤ ∑ i : Fin 4, |u i| := sum_nonneg (fun i _ => abs_nonneg _)
  have hbound : Real.sqrt 2 ≤ ∑ i : Fin 4, |u i| := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hnonneg, by nlinarith⟩
  have h2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have h2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hid : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff h2pos.ne').2
    nlinarith
  rw [hid]
  unfold barycentricCost
  linarith

theorem sum_normal_mul (j k : Fin 3) :
    ∑ i : Fin 4, normal i j * normal i k = if j = k then (4 / 3 : ℝ) else 0 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  fin_cases j <;> fin_cases k <;>
    simp [normal, Fin.sum_univ_succ] <;> field_simp <;> nlinarith

theorem isLeast_frameCost :
    IsLeast {a : ℝ | ∃ u : Space, ‖u‖ = 1 ∧ a = frameCost u} (Real.sqrt 2) := by
  constructor
  · exact ⟨edgeDirection, edgeDirection_unit, frameCost_edgeDirection.symm⟩
  · rintro a ⟨u, hu, rfl⟩
    exact frameCost_lower_bound u hu

theorem barycentricEdge_sum : ∑ i : Fin 4, barycentricEdge i = 0 := by
  simp [barycentricEdge, Fin.sum_univ_succ]

theorem barycentricEdge_unit : ‖barycentricEdge‖ = 1 := by
  have hs : ‖barycentricEdge‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [barycentricEdge, Fin.sum_univ_succ, div_pow, Real.sq_sqrt]
  nlinarith [norm_nonneg barycentricEdge]

theorem barycentricCost_edge : barycentricCost barycentricEdge = 1 / Real.sqrt 2 := by
  simp [barycentricCost, barycentricEdge, Fin.sum_univ_succ,
    abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ))]
  ring

theorem isLeast_barycentricCost :
    IsLeast {a : ℝ | ∃ u : BarycentricSpace,
      ‖u‖ = 1 ∧ ∑ i : Fin 4, u i = 0 ∧ a = barycentricCost u} (1 / Real.sqrt 2) := by
  constructor
  · exact ⟨barycentricEdge, barycentricEdge_unit, barycentricEdge_sum,
      barycentricCost_edge.symm⟩
  · rintro a ⟨u, hu, hsum, rfl⟩
    exact barycentricCost_lower_bound u hu hsum

end CylinderNormalFrame

end

end OAI

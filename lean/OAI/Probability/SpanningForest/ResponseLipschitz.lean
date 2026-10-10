import OAI.Probability.SpanningForest.FiniteResponse

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.FiniteResponse

variable {E : Type*} [Fintype E]

lemma abs_sum_mul_le_sup (c v : E → ℝ) :
    |∑ i, c i * v i| ≤ (∑ i, |c i|) * ‖v‖ := by
  calc
    |∑ i, c i * v i| ≤ ∑ i, |c i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i| * |v i| := by simp only [abs_mul]
    _ ≤ ∑ i, |c i| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)
    _ = (∑ i, |c i|) * ‖v‖ := (Finset.sum_mul _ _ _).symm

lemma opNorm_le_abs_row_sum (d : (E → ℝ) →L[ℝ] ℝ) (c : E → ℝ)
    (hrow : ∀ v, d v = ∑ i, c i * v i) :
    ‖d‖ ≤ ∑ i, |c i| := by
  apply d.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  intro v
  rw [Real.norm_eq_abs, hrow]
  exact abs_sum_mul_le_sup c v

theorem abs_sub_le_of_derivative_row_bound
    (f : (E → ℝ) → ℝ) (d : (E → ℝ) → (E → ℝ) →L[ℝ] ℝ)
    (c : (E → ℝ) → E → ℝ) (L : ℝ)
    (hd : ∀ h, HasFDerivAt f (d h) h)
    (hrow : ∀ h v, d h v = ∑ i, c h i * v i)
    (hbound : ∀ h, ∑ i, |c h i| ≤ L) (x y : E → ℝ) :
    |f y - f x| ≤ L * ‖y - x‖ := by
  have hop : ∀ h, ‖d h‖ ≤ L := fun h =>
    (opNorm_le_abs_row_sum (d h) (c h) (hrow h)).trans (hbound h)
  simpa only [Real.norm_eq_abs] using
    (convex_univ : Convex ℝ (Set.univ : Set (E → ℝ))).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun h _ => (hd h).hasFDerivWithinAt) (fun h _ => hop h)
      (Set.mem_univ x) (Set.mem_univ y)

theorem abs_sub_le_of_derivative_row_bound_of_coordinate_bound
    (f : (E → ℝ) → ℝ) (d : (E → ℝ) → (E → ℝ) →L[ℝ] ℝ)
    (c : (E → ℝ) → E → ℝ) (L D : ℝ)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hd : ∀ h, HasFDerivAt f (d h) h)
    (hrow : ∀ h v, d h v = ∑ i, c h i * v i)
    (hbound : ∀ h, ∑ i, |c h i| ≤ L)
    (x y : E → ℝ) (hxy : ∀ i, |y i - x i| ≤ D) :
    |f y - f x| ≤ L * D := by
  apply (abs_sub_le_of_derivative_row_bound f d c L hd hrow hbound x y).trans
  apply mul_le_mul_of_nonneg_left _ hL
  exact (pi_norm_le_iff_of_nonneg hD).mpr hxy

theorem abs_sub_le_of_line_derivative_row_bound
    (f : (E → ℝ) → ℝ) (c : (E → ℝ) → E → ℝ) (L : ℝ)
    (hd : ∀ a b t, HasDerivAt
      (fun s : ℝ => f (a + s • (b - a)))
      (∑ i, c (a + t • (b - a)) i * (b i - a i)) t)
    (hbound : ∀ h, ∑ i, |c h i| ≤ L) (a b : E → ℝ) :
    |f b - f a| ≤ L * ‖b - a‖ := by
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt
      (fun s : ℝ => f (a + s • (b - a)))
      (∑ i, c (a + t • (b - a)) i * (b i - a i))
      (Set.Icc (0 : ℝ) 1) t := fun t _ => (hd a b t).hasDerivWithinAt
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖∑ i, c (a + t • (b - a)) i * (b i - a i)‖ ≤ L * ‖b - a‖ := by
    intro t _
    rw [Real.norm_eq_abs]
    exact (abs_sum_mul_le_sup (c (a + t • (b - a))) (b - a)).trans
      (mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _))
  simpa only [zero_smul, add_zero, one_smul, add_sub_cancel,
    Real.norm_eq_abs] using
    norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hb

theorem mean_abs_sub_le_half {Ω : Type*} [Fintype Ω]
    (p : (E → ℝ) → Ω → ℝ) (x : Ω → E → ℝ) (e : E)
    (d : (E → ℝ) → (E → ℝ) →L[ℝ] ℝ)
    (hp : ∀ h ω, 0 ≤ p h ω) (hnorm : ∀ h, ∑ ω, p h ω = 1)
    (hx : ∀ ω f, x ω f = 0 ∨ x ω f = 1)
    (r : ℝ) (hfixed : ∀ ω, ∑ f, x ω f = r)
    (hneg : ∀ h e f, e ≠ f → covariance (p h) x e f ≤ 0)
    (hd : ∀ h, HasFDerivAt (fun h => mean (p h) x e) (d h) h)
    (hrow : ∀ h v, d h v = ∑ f, covariance (p h) x e f * v f)
    (a b : E → ℝ) :
    |mean (p b) x e - mean (p a) x e| ≤ (1 / 2 : ℝ) * ‖b - a‖ := by
  exact abs_sub_le_of_derivative_row_bound (fun h => mean (p h) x e) d
    (fun h f => covariance (p h) x e f) (1 / 2) hd hrow
    (fun h => covariance_abs_row_le_half (p h) x (hp h) (hnorm h) hx r hfixed
      (hneg h) e) a b

end Problem336.FiniteResponse

end

end OAI

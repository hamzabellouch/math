import OAI.Geometry.EinsteinFour.CurvatureFirstBianchi

namespace OAI

/-! Transport of coordinate curvature skew-adjointness through the actual
orthonormal frame. No change-of-frame assumption is used. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

private theorem sum_four_first_last (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ c, ∑ d, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]

private theorem sum_five_first_last (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact sum_four_first_last (fun a c d e => f a b c d e)

private theorem skew_matrix_contraction (L E : Mat4)
    (hL : ∀ r b, L r b = -L b r) (k l : Fin 4) :
    (∑ r, ∑ b, L r b * E r k * E b l) =
      -(∑ r, ∑ b, L r b * E r l * E b k) := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ r, ∑ b, -(L r b * E r l * E b k) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro b _
      rw [hL b r]
      ring
    _ = _ := by simp only [Finset.sum_neg_distrib]

private theorem tensor_last_skew_transport (G E : Mat4)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ p q r b, (∑ a, G a b * R a p q r) = -(∑ a, G a r * R a p q b))
    (i j k l : Fin 4) :
    (∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
      G a b * R a p q r * E p i * E q j * E r k * E b l) =
      -(∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
      G a b * R a p q r * E p i * E q j * E r l * E b k) := by
  have heq (k l : Fin 4) :
      (∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
        G a b * R a p q r * E p i * E q j * E r k * E b l) =
      ∑ p, ∑ q, (E p i * E q j) *
        ∑ r, ∑ b, (∑ a, G a b * R a p q r) * E r k * E b l := by
    rw [sum_five_first_last, sum_four_first_last]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq, heq]
  have hs (p q : Fin 4) := skew_matrix_contraction
    (fun r b => ∑ a, G a b * R a p q r) E (hR p q) k l
  simp_rw [hs, mul_neg]
  simp only [Finset.sum_neg_distrib]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem frameCurvature_last_skew_of_lowered (e : OrthonormalFrame g c)
    (h : ∀ p q r b, (∑ a, chartMetric g c a b *
      curvatureComponent g c (chartAt FourSpace c c) a p q r) =
      -(∑ a, chartMetric g c a r *
      curvatureComponent g c (chartAt FourSpace c c) a p q b)) (i j k l : Fin 4) :
    frameCurvature g c e i j k l = -frameCurvature g c e i j l k :=
  tensor_last_skew_transport (chartMetric g c) e.matrix
    (curvatureComponent g c (chartAt FourSpace c c)) h i j k l

end
end PositiveEinsteinFour.Geometry

end OAI

import OAI.Geometry.EinsteinFour.ActualRicciContraction

namespace OAI

/-! The first Bianchi identity follows directly from the symmetric
Levi-Civita Christoffel symbols and is preserved by frame contraction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricInChart_comm (g : SmoothMetric M) (c : M) (z : FourSpace)
    (i j : Fin 4) : metricInChart g c z i j = metricInChart g c z j i := by
  exact g.symm _ _ _

theorem christoffel_comm (g : SmoothMetric M) (c : M) (z : FourSpace)
    (l i j : Fin 4) : christoffel g c z l i j = christoffel g c z l j i := by
  have hm : (fun w => metricInChart g c w i j) =
      (fun w => metricInChart g c w j i) := funext fun w => metricInChart_comm g c w i j
  unfold christoffel
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem curvatureComponent_first_bianchi (g : SmoothMetric M) (c : M) (z : FourSpace)
    (l i j k : Fin 4) :
    curvatureComponent g c z l i j k + curvatureComponent g c z l j k i +
      curvatureComponent g c z l k i j = 0 := by
  have hji : (fun w => christoffel g c w l j i) =
      (fun w => christoffel g c w l i j) := funext fun w => christoffel_comm g c w l j i
  have hkj : (fun w => christoffel g c w l k j) =
      (fun w => christoffel g c w l j k) := funext fun w => christoffel_comm g c w l k j
  have hki : (fun w => christoffel g c w l k i) =
      (fun w => christoffel g c w l i k) := funext fun w => christoffel_comm g c w l k i
  have hc : (∑ p, (christoffel g c z l i p * christoffel g c z p j k -
      christoffel g c z l j p * christoffel g c z p i k)) +
      (∑ p, (christoffel g c z l j p * christoffel g c z p k i -
      christoffel g c z l k p * christoffel g c z p j i)) +
      (∑ p, (christoffel g c z l k p * christoffel g c z p i j -
      christoffel g c z l i p * christoffel g c z p k j)) = 0 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro p _
    rw [christoffel_comm g c z p k i, christoffel_comm g c z p j i,
      christoffel_comm g c z p k j]
    ring
  unfold curvatureComponent
  rw [hji, hkj, hki]
  linarith

private theorem sum_three_cycle (f : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ p, ∑ q, ∑ r, f p q r) = ∑ p, ∑ q, ∑ r, f q r p := by
  calc
    _ = ∑ p, ∑ r, ∑ q, f p q r := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

private theorem contracted_bianchi (R : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hR : ∀ p q r, R p q r + R q r p + R r p q = 0)
    (E : Matrix (Fin 4) (Fin 4) ℝ) (i j k : Fin 4) :
    (∑ p, ∑ q, ∑ r, R p q r * E p i * E q j * E r k) +
      (∑ p, ∑ q, ∑ r, R p q r * E p j * E q k * E r i) +
      (∑ p, ∑ q, ∑ r, R p q r * E p k * E q i * E r j) = 0 := by
  have h2 : (∑ p, ∑ q, ∑ r, R p q r * E p j * E q k * E r i) =
      ∑ p, ∑ q, ∑ r, R q r p * E p i * E q j * E r k := by
    rw [sum_three_cycle]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    ring
  have h3 : (∑ p, ∑ q, ∑ r, R p q r * E p k * E q i * E r j) =
      ∑ p, ∑ q, ∑ r, R r p q * E p i * E q j * E r k := by
    rw [sum_three_cycle, sum_three_cycle]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [h2, h3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro p _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro q _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro r _
  linear_combination (E p i * E q j * E r k) * hR p q r

theorem frameCurvature_first_bianchi {g : SmoothMetric M} {c : M}
    (e : OrthonormalFrame g c) (i j k l : Fin 4) :
    frameCurvature g c e i j k l + frameCurvature g c e j k i l +
      frameCurvature g c e k i j l = 0 := by
  unfold frameCurvature
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro a _
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro b _
  have h := contracted_bianchi
    (fun p q r => curvatureComponent g c (chartAt FourSpace c c) a p q r)
    (curvatureComponent_first_bianchi g c (chartAt FourSpace c c) a) e.matrix i j k
  have heq (i j k : Fin 4) :
      (∑ p, ∑ q, ∑ r, chartMetric g c a b *
        curvatureComponent g c (chartAt FourSpace c c) a p q r *
        e.matrix p i * e.matrix q j * e.matrix r k * e.matrix b l) =
      (chartMetric g c a b * e.matrix b l) *
        ∑ p, ∑ q, ∑ r, curvatureComponent g c (chartAt FourSpace c c) a p q r *
          e.matrix p i * e.matrix q j * e.matrix r k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [heq, heq, heq]
  linear_combination (chartMetric g c a b * e.matrix b l) * h

end
end PositiveEinsteinFour.Geometry

end OAI

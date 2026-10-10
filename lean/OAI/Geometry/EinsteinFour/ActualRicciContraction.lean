import OAI.Geometry.EinsteinFour.OrthonormalFrame

namespace OAI

/-! Contraction of the actual chart curvature in an orthonormal frame.
This is a finite change-of-basis calculation, used to discharge the Ricci
positivity needed by constant Einstein normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

private theorem sum_six_rotate {α : Type*} [Fintype α]
    (f : α → α → α → α → α → α → ℝ) :
    (∑ i, ∑ a, ∑ b, ∑ p, ∑ q, ∑ r, f i a b p q r) =
      ∑ a, ∑ p, ∑ q, ∑ r, ∑ i, ∑ b, f i a b p q r := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ i, ∑ p, ∑ b, ∑ q, ∑ r, f i a b p q r := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ b, ∑ q, ∑ r, f i a b p q r := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      calc
        _ = ∑ i, ∑ q, ∑ b, ∑ r, f i a b p q r := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = ∑ q, ∑ i, ∑ b, ∑ r, f i a b p q r := Finset.sum_comm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro q _
          calc
            _ = ∑ i, ∑ r, ∑ b, f i a b p q r := by
              apply Finset.sum_congr rfl
              intro i _
              exact Finset.sum_comm
            _ = _ := Finset.sum_comm

theorem tensor_trace_basis_change (G E : Mat4)
    (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ)
    (h : ∀ a p, (∑ i, ∑ b, G a b * E p i * E b i) = if a = p then 1 else 0)
    (j k : Fin 4) :
    (∑ i, ∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
      G a b * C a p q r * E p i * E q j * E r k * E b i) =
      ∑ q, ∑ r, E q j * (∑ a, C a a q r) * E r k := by
  rw [sum_six_rotate]
  have hh (a p q r : Fin 4) :
      (∑ i, ∑ b, G a b * C a p q r * E p i * E q j * E r k * E b i) =
        C a p q r * E q j * E r k * (∑ i, ∑ b, G a b * E p i * E b i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [hh, h]
  simp only [mul_ite, mul_one, mul_zero]
  have hs (a q r : Fin 4) :
      (∑ p, if a = p then C a p q r * E q j * E r k else 0) =
        C a a q r * E q j * E r k := by simp
  have ht (a : Fin 4) :
      (∑ p, ∑ q, ∑ r, if a = p then C a p q r * E q j * E r k else 0) =
        ∑ q, ∑ r, C a a q r * E q j * E r k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_comm]
    simp only [hs]
  simp only [ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem OrthonormalFrame.inverse_contraction (e : OrthonormalFrame g c) (a p : Fin 4) :
    (∑ i, ∑ b, chartMetric g c a b * e.matrix p i * e.matrix b i) =
      if a = p then 1 else 0 := by
  have hi : e.matrix * (e.matrixᵀ * chartMetric g c) = 1 :=
    mul_eq_one_comm.mp e.orthonormal
  have hij := congrFun (congrFun hi p) a
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at hij
  calc
    _ = ∑ i, ∑ b, e.matrix p i * (e.matrix b i * chartMetric g c b a) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro b _
      have hsym : chartMetric g c a b = chartMetric g c b a := by
        simpa only [Matrix.conjTranspose_apply, star_trivial] using
          congrFun (congrFun (chartMetric_posDef g c).isHermitian.eq b) a
      rw [hsym]
      ring
    _ = if p = a then 1 else 0 := by simpa only [Finset.mul_sum] using hij
    _ = _ := by simp only [eq_comm]

theorem frameCurvature_ricci (e : OrthonormalFrame g c) (j k : Fin 4) :
    (∑ i, frameCurvature g c e i j k i) = e.ricci j k := by
  change (∑ i, ∑ a, ∑ b, ∑ p, ∑ q, ∑ r,
    chartMetric g c a b * curvatureComponent g c (chartAt FourSpace c c) a p q r *
      e.matrix p i * e.matrix q j * e.matrix r k * e.matrix b i) = _
  rw [tensor_trace_basis_change _ _ _ e.inverse_contraction]
  change (∑ q, ∑ r, e.matrix q j *
    (∑ a, curvatureComponent g c (chartAt FourSpace c c) a a q r) * e.matrix r k) =
    ∑ r, (∑ q, e.matrix q j *
      (∑ a, curvatureComponent g c (chartAt FourSpace c c) a a q r)) * e.matrix r k
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

variable {g : SmoothMetric M} {c : M}

theorem curvatureComponent_first_skew (g : SmoothMetric M) (c : M) (z : FourSpace)
    (l i j k : Fin 4) :
    curvatureComponent g c z l i j k = -curvatureComponent g c z l j i k := by
  simp only [curvatureComponent, Finset.sum_sub_distrib]
  ring

theorem frameCurvature_first_skew (e : OrthonormalFrame g c) (i j k l : Fin 4) :
    frameCurvature g c e i j k l = -frameCurvature g c e j i k l := by
  unfold frameCurvature
  have hh (a b : Fin 4) :
      (∑ p, ∑ q, ∑ r, chartMetric g c a b *
        curvatureComponent g c (chartAt FourSpace c c) a p q r *
        e.matrix p i * e.matrix q j * e.matrix r k * e.matrix b l) =
      -(∑ p, ∑ q, ∑ r, chartMetric g c a b *
        curvatureComponent g c (chartAt FourSpace c c) a p q r *
        e.matrix p j * e.matrix q i * e.matrix r k * e.matrix b l) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ p, ∑ q, ∑ r, -(chartMetric g c a b *
          curvatureComponent g c (chartAt FourSpace c c) a p q r *
          e.matrix p j * e.matrix q i * e.matrix r k * e.matrix b l) := by
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro r _
        rw [curvatureComponent_first_skew]
        ring
      _ = _ := by simp only [Finset.sum_neg_distrib]
  calc
    _ = ∑ a, ∑ b, -(∑ p, ∑ q, ∑ r, chartMetric g c a b *
        curvatureComponent g c (chartAt FourSpace c c) a p q r *
        e.matrix p j * e.matrix q i * e.matrix r k * e.matrix b l) := by
      exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hh a b))
    _ = _ := by simp only [Finset.sum_neg_distrib]

theorem frameCurvature_first_self (e : OrthonormalFrame g c) (i k l : Fin 4) :
    frameCurvature g c e i i k l = 0 := by
  have h := frameCurvature_first_skew e i i k l
  linarith


end
end PositiveEinsteinFour.Geometry

end OAI

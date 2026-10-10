import OAI.Geometry.IsometricImmersion.Curvature.AffineConnection

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace AffineCalculus

theorem coordPartial_sum_const_mul (f : Fin 2 → Coord → ℝ) (c : Fin 2 → ℝ)
    {p : Coord} (hf : ∀ a, DifferentiableAt ℝ (f a) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, c a * f a q) p =
      ∑ a, c a * coordPartial i (f a) p := by
  rw [HessianCalculus.coordPartial_sum_two _ (fun a => (hf a).const_mul (c a)) i]
  apply Finset.sum_congr rfl
  intro a _
  exact coordPartial_const_mul_at (hf a) (c a) i

theorem coordPartial_double_sum_const_mul
    (f : Fin 2 → Fin 2 → Coord → ℝ) (c : Fin 2 → Fin 2 → ℝ)
    {p : Coord} (hf : ∀ a b, DifferentiableAt ℝ (f a b) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, ∑ b, c a b * f a b q) p =
      ∑ a, ∑ b, c a b * coordPartial i (f a b) p := by
  rw [HessianCalculus.coordPartial_sum_two _
    (fun a => DifferentiableAt.fun_sum fun b _ => (hf a b).const_mul (c a b)) i]
  apply Finset.sum_congr rfl
  intro a _
  exact coordPartial_sum_const_mul (f a) (c a) (hf a) i

theorem pushed_connection_product
    (R : Matrix (Fin 2) (Fin 2) ℝ)
    (C D : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (h : ∀ a i j, (∑ l, R a l * C l i j) = ∑ c, ∑ d, R c i * R d j * D a c d)
    (a i j k : Fin 2) :
    (∑ l, R a l * ∑ m, C m j k * C l i m) =
      ∑ c, ∑ d, ∑ e, ∑ f, R c i * R e j * R f k * D d e f * D a c d := by
  calc
    _ = ∑ m, C m j k * (∑ l, R a l * C l i m) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ m, C m j k * (∑ c, ∑ d, R c i * R d m * D a c d) := by
      simp only [h]
    _ = ∑ c, ∑ d, R c i * D a c d * (∑ m, R d m * C m j k) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ c, ∑ d, R c i * D a c d *
        (∑ e, ∑ f, R e j * R f k * D d e f) := by simp only [h]
    _ = _ := by simp only [Fin.sum_univ_two]; ring

end AffineCalculus

theorem coordPartial_christoffel_affinePullback_push
    {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a i j k : Fin 2) :
    (∑ l, R a l * coordPartial i (christoffel (affinePullbackMetric g b R) l j k) q) =
      ∑ c, ∑ d, ∑ e, R c j * R d k * R e i *
        coordPartial e (christoffel g a c d) (affineCoordinates b R q) := by
  have hV := isOpen_affine_preimage hU b R
  have hgR := affinePullbackMetric_smoothPositive hg b R
    (Matrix.mulVec_injective_of_isUnit hR)
  have hL (l : Fin 2) : DifferentiableAt ℝ
      (christoffel (affinePullbackMetric g b R) l j k) q :=
    (((christoffel_contDiffOn hgR hV l j k) q hq).contDiffAt
      (hV.mem_nhds hq)).differentiableAt (by simp)
  have hG (c d : Fin 2) : DifferentiableAt ℝ (christoffel g a c d)
      (affineCoordinates b R q) :=
    (((christoffel_contDiffOn hg hU a c d) _ hq).contDiffAt
      (hU.mem_nhds hq)).differentiableAt (by simp)
  have hGc (c d : Fin 2) : DifferentiableAt ℝ
      (fun p => christoffel g a c d (affineCoordinates b R p)) q :=
    (hG c d).comp q (affineCoordinates_hasFDerivAt b R q).differentiableAt
  have hchain (c d : Fin 2) :
      coordPartial i (fun p => christoffel g a c d (affineCoordinates b R p)) q =
        ∑ e, R e i * coordPartial e (christoffel g a c d) (affineCoordinates b R q) :=
    coordPartial_affine_comp b R q (hG c d) i
  have heq : (fun p => ∑ l, R a l *
      christoffel (affinePullbackMetric g b R) l j k p) =ᶠ[𝓝 q]
      (fun p => ∑ c, ∑ d, R c j * R d k *
        christoffel g a c d (affineCoordinates b R p)) := by
    filter_upwards [hV.mem_nhds hq] with p hp
    exact christoffel_affinePullback_push hg hU b R hR p hp a j k
  calc
    _ = coordPartial i (fun p => ∑ l, R a l *
        christoffel (affinePullbackMetric g b R) l j k p) q :=
      (AffineCalculus.coordPartial_sum_const_mul _ _ hL i).symm
    _ = coordPartial i (fun p => ∑ c, ∑ d, R c j * R d k *
        christoffel g a c d (affineCoordinates b R p)) q := by
      unfold coordPartial
      rw [heq.fderiv_eq]
    _ = ∑ c, ∑ d, (R c j * R d k) * coordPartial i
        (fun p => christoffel g a c d (affineCoordinates b R p)) q :=
      AffineCalculus.coordPartial_double_sum_const_mul _ _ hGc i
    _ = _ := by
      simp_rw [hchain]
      simp only [Fin.sum_univ_two]
      ring

theorem riemann_affinePullback_push {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a k i j : Fin 2) :
    (∑ l, R a l * riemann (affinePullbackMetric g b R) l k i j q) =
      ∑ c, ∑ d, ∑ e, R c k * R d i * R e j *
        riemann g a c d e (affineCoordinates b R q) := by
  let C := fun a i j => christoffel (affinePullbackMetric g b R) a i j q
  let D := fun a i j => christoffel g a i j (affineCoordinates b R q)
  have hp (a i j : Fin 2) : (∑ l, R a l * C l i j) =
      ∑ c, ∑ d, R c i * R d j * D a c d :=
    christoffel_affinePullback_push hg hU b R hR q hq a i j
  calc
    _ = (∑ l, R a l * coordPartial i
          (christoffel (affinePullbackMetric g b R) l j k) q) -
        (∑ l, R a l * coordPartial j
          (christoffel (affinePullbackMetric g b R) l i k) q) +
        (∑ l, R a l * ∑ m, C m j k * C l i m) -
        (∑ l, R a l * ∑ m, C m i k * C l j m) := by
      simp only [riemann, C, Fin.sum_univ_two]
      ring
    _ = (∑ c, ∑ d, ∑ e, R c j * R d k * R e i *
          coordPartial e (christoffel g a c d) (affineCoordinates b R q)) -
        (∑ c, ∑ d, ∑ e, R c i * R d k * R e j *
          coordPartial e (christoffel g a c d) (affineCoordinates b R q)) +
        (∑ c, ∑ d, ∑ e, ∑ f, R c i * R e j * R f k * D d e f * D a c d) -
        (∑ c, ∑ d, ∑ e, ∑ f, R c j * R e i * R f k * D d e f * D a c d) := by
      rw [coordPartial_christoffel_affinePullback_push hg hU b R hR q hq a i j k,
        coordPartial_christoffel_affinePullback_push hg hU b R hR q hq a j i k,
        AffineCalculus.pushed_connection_product R C D hp a i j k,
        AffineCalculus.pushed_connection_product R C D hp a j i k]
    _ = _ := by
      simp only [riemann, D, Fin.sum_univ_two]
      ring

theorem loweredRiemann_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (l k i j : Fin 2) :
    loweredRiemann (affinePullbackMetric g b R) l k i j q =
      ∑ a, ∑ c, ∑ d, ∑ e, R a l * R c k * R d i * R e j *
        loweredRiemann g a c d e (affineCoordinates b R q) := by
  calc
    _ = ∑ a, ∑ c, R a l * g (affineCoordinates b R q) a c *
        (∑ r, R c r * riemann (affinePullbackMetric g b R) r k i j q) := by
      simp only [loweredRiemann, affinePullbackMetric, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_two]
      ring
    _ = ∑ a, ∑ c, R a l * g (affineCoordinates b R q) a c *
        (∑ d, ∑ e, ∑ f, R d k * R e i * R f j *
          riemann g c d e f (affineCoordinates b R q)) := by
      simp_rw [riemann_affinePullback_push hg hU b R hR q hq]
    _ = _ := by simp only [loweredRiemann, Fin.sum_univ_two]; ring

theorem gaussianCurvature_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) :
    gaussianCurvature (affinePullbackMetric g b R) q =
      gaussianCurvature g (affineCoordinates b R q) := by
  have hgR := affinePullbackMetric_smoothPositive hg b R
    (Matrix.mulVec_injective_of_isUnit hR)
  have hsym : g (affineCoordinates b R q) 1 0 = g (affineCoordinates b R q) 0 1 :=
    metric_coeff_symm hg hq 1 0
  have hlow : loweredRiemann (affinePullbackMetric g b R) 0 1 0 1 q =
      gaussianCurvature g (affineCoordinates b R q) * (affinePullbackMetric g b R q).det := by
    rw [loweredRiemann_affinePullback hg hU b R hR q hq]
    simp only [loweredRiemann_factorization hg hU hq,
      affinePullbackMetric, Matrix.det_fin_two, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two, hsym]
    ring
  change loweredRiemann (affinePullbackMetric g b R) 0 1 0 1 q /
    (affinePullbackMetric g b R q).det = _
  rw [hlow, mul_div_cancel_right₀ _ (metricDet_ne_zero hgR hq)]

theorem det_affinePullbackMetric (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord) :
    (affinePullbackMetric g b R q).det =
      R.det ^ 2 * (g (affineCoordinates b R q)).det := by
  simp only [affinePullbackMetric, Matrix.det_mul, Matrix.det_transpose]
  ring

end SmoothLocal.Geometry

end

end OAI

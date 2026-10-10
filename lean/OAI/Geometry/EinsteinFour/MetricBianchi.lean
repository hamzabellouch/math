import OAI.Geometry.EinsteinFour.WeylDerivative
import OAI.Geometry.EinsteinFour.AngularGradient

namespace OAI

/-! The actual Weyl gradient, with its derivative index treated as a tangent
vector. These changes of coordinate retain every component: neither the
Bianchi equation nor a differential estimate is built into the definition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Angular Bianchi TraceHessian
open scoped Manifold ContDiff

noncomputable section

/-- Reorder the derivative slot of a symmetric matrix gradient. -/
def gradientTensor (Z : Gradient) : Tensor where
  diagonal a := WithLp.toLp 2 (fun i => Z i a a)
  off a := WithLp.toLp 2 (fun i => Z i (next a) (previous a))

theorem gradientTensor_matrix (Z : Gradient) (hs : ∀ i, symmetric (Z i))
    (a b : Fin 3) :
    (gradientTensor Z).matrix a b = WithLp.toLp 2 (fun i => Z i a b) := by
  ext i
  fin_cases a <;> fin_cases b <;> simp [gradientTensor, Tensor.matrix, next, previous]
  all_goals exact hs i _ _

theorem gradientTensor_traceFree (Z : Gradient) (ht : ∀ i, traceFree (Z i)) :
    (gradientTensor Z).traceFree := by
  ext i
  simpa [Tensor.traceFree, gradientTensor, traceFree, Fin.sum_univ_three] using ht i

/-- This is the coordinate divergence of the matrix gradient. -/
def gradientDivergence (Z : Gradient) (r : Fin 3) (i : Fin 4) : ℝ :=
  ∑ s, ∑ j, quaternionMatrix s i j * Z j s r

theorem gradientTensor_divergence (Z : Gradient) (hs : ∀ i, symmetric (Z i))
    (r : Fin 3) (i : Fin 4) :
    (gradientTensor Z).divergence r i = gradientDivergence Z r i := by
  rw [Tensor.divergence_eq_sum]
  simp_rw [gradientTensor_matrix Z hs]
  change (∑ s, quaternion s (WithLp.toLp 2 (fun j => Z j s r))) i = _
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  unfold gradientDivergence
  apply Finset.sum_congr rfl
  intro s _
  exact (quaternionMatrix_apply s (WithLp.toLp 2 (fun j => Z j s r)) i).symm

theorem gradientTensor_bianchi (Z : Gradient) (hs : ∀ i, symmetric (Z i))
    (hb : ∀ r i, gradientDivergence Z r i = 0) : (gradientTensor Z).bianchi := by
  intro r
  ext i
  exact gradientTensor_divergence Z hs r i |>.trans (hb r i)

/-- The tensor norm is precisely the ordinary covariant-gradient norm. -/
theorem gradientTensor_squaredNorm (Z : Gradient) (hs : ∀ i, symmetric (Z i)) :
    (gradientTensor Z).squaredNorm = gradientSquareNorm Z := by
  unfold Tensor.squaredNorm
  simp_rw [gradientTensor_matrix Z hs, EuclideanSpace.real_norm_sq_eq]
  change (∑ a, ∑ b, ∑ i, Z i a b ^ 2) = ∑ i, ∑ a, ∑ b, Z i a b ^ 2
  calc
    _ = ∑ a, ∑ i, ∑ b, Z i a b ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The concrete tensor to which the finite Bianchi estimates apply. -/
def plusGradientTensor (g : SmoothMetric M) (c : M) (e : OrthonormalFrame g c) :
    Tensor := gradientTensor (plusWeylGradient g c e)

theorem plusGradientTensor_squaredNorm (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (hs : ∀ i, symmetric (plusWeylGradient g c e i)) :
    (plusGradientTensor g c e).squaredNorm =
      gradientSquareNorm (plusWeylGradient g c e) :=
  gradientTensor_squaredNorm _ hs

/-- Refined Kato for the actual gradient after its classical differential
Bianchi equation has been supplied. The eigenframe's normalized spectral
shape is explicit; no scalar gradient estimate is a hypothesis. -/
theorem plusGradientTensor_refined_kato (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (S : Shape)
    (hs : ∀ i, symmetric (plusWeylGradient g c e i))
    (ht : ∀ i, traceFree (plusWeylGradient g c e i))
    (hb : ∀ r i, gradientDivergence (plusWeylGradient g c e) r i = 0) :
    (5 / 3) * ‖radialCoordinate S (plusGradientTensor g c e)‖ ^ 2 ≤
      gradientSquareNorm (plusWeylGradient g c e) / 6 := by
  rw [← plusGradientTensor_squaredNorm g c e hs]
  exact refined_kato S _ (gradientTensor_traceFree _ ht) (gradientTensor_bianchi _ hs hb)

end

end PositiveEinsteinFour.Geometry

end OAI

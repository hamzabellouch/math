import Mathlib
import OAI.Analysis.AffineBernstein.EntireAndDoubling

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LogDetGradientEnergy

/-- Half the squared Euclidean gradient, expressed in the frozen orthonormal coordinates. -/
def gradientEnergy {n : ℕ} (u : Space n → ℝ) (x : Space n) : ℝ :=
  (1/2 : ℝ) * ∑ k, (dirDeriv (coordinateVector n k) u x)^2

lemma contDiffOn_gradientEnergy {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω) :
    ContDiffOn ℝ ∞ (gradientEnergy u) Ω := by
  exact contDiffOn_const.mul (ContDiffOn.sum fun k _ => (contDiffOn_dirDeriv hΩ hu _).pow 2)

lemma dirDeriv_gradientEnergy {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (i : Fin n) :
    dirDeriv (coordinateVector n i) (gradientEnergy u) x =
      ∑ k, dirDeriv (coordinateVector n k) u x * hessian u x i k := by
  change dirDeriv _ (fun y => (1/2:ℝ) * ∑ k, (dirDeriv (coordinateVector n k) u y)^2) x = _
  have hs : ContDiffAt ℝ ∞ (fun y => ∑ k, (dirDeriv (coordinateVector n k) u y)^2) x :=
    ContDiffAt.sum fun k _ => (contDiffAt_dirDeriv hu _).pow 2
  rw [dirDeriv_const_mul (hs.differentiableAt (by simp)),
    dirDeriv_sum (fun (k : Fin n) (y : Space n) => (dirDeriv (coordinateVector n k) u y)^2)
      (fun k => ((contDiffAt_dirDeriv hu _).differentiableAt (by simp)).pow 2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [pow_two]
  rw [dirDeriv_mul ((contDiffAt_dirDeriv hu _).differentiableAt (by simp))
    ((contDiffAt_dirDeriv hu _).differentiableAt (by simp))]
  change (1/2:ℝ) * (hessian u x i k * dirDeriv (coordinateVector n k) u x +
    dirDeriv (coordinateVector n k) u x * hessian u x i k) = _
  ring

lemma inverseHessian_pair_gradient {n : ℕ} {u : Space n → ℝ} {x : Space n}
    (hu : ContDiffAt ℝ ∞ u x) (hp : (hessian u x).PosDef) (f : Space n → ℝ) :
    inverseHessianPair u (gradientEnergy u) f x =
      ∑ k, dirDeriv (coordinateVector n k) u x * dirDeriv (coordinateVector n k) f x := by
  unfold inverseHessianPair
  simp_rw [dirDeriv_gradientEnergy hu]
  have hs := Matrix.isHermitian_iff_isSymm.mp hp.isHermitian
  have he (i : Fin n) : (∑ k, dirDeriv (coordinateVector n k) u x * hessian u x i k) =
      ∑ k, dirDeriv (coordinateVector n k) u x * hessian u x k i := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hs.apply k i]
  simp only [he]
  exact inverse_radial_contraction hp _ _

lemma inverseHessianTrace_gradientEnergy {n : ℕ} {Ω : Set (Space n)} (hΩ : IsOpen Ω)
    {u : Space n → ℝ} (hu : ContDiffOn ℝ ∞ u Ω)
    {x : Space n} (hx : x ∈ Ω) (hp : (hessian u x).PosDef) :
    inverseHessianTrace u (gradientEnergy u) x =
      (hessian u x).trace + ∑ k,
        dirDeriv (coordinateVector n k) u x * dirDeriv (coordinateVector n k) (logHessianDet u) x := by
  have hk (k : Fin n) := contDiffOn_dirDeriv hΩ hu (coordinateVector n k)
  have he (i j : Fin n) : hessian (gradientEnergy u) x i j =
      (1/2 : ℝ) * ∑ k, hessian (fun y => dirDeriv (coordinateVector n k) u y *
        dirDeriv (coordinateVector n k) u y) x i j := by
    change dirDeriv _ (dirDeriv _ (fun y => (1/2:ℝ) * ∑ k,
      (dirDeriv (coordinateVector n k) u y)^2)) x = _
    rw [second_dirDeriv_const_mul hΩ (ContDiffOn.sum fun k _ => (hk k).pow 2) hx]
    congr 1
    change hessian (fun y => ∑ k, (dirDeriv (coordinateVector n k) u y)^2) x i j = _
    simp only [pow_two]
    exact hessian_sum_on hΩ (fun k => (hk k).mul (hk k)) hx i j
  have hsum : inverseHessianTrace u (gradientEnergy u) x =
      (1/2:ℝ) * ∑ k, ∑ i, ∑ j, (hessian u x)⁻¹ i j *
        hessian (fun y => dirDeriv (coordinateVector n k) u y *
          dirDeriv (coordinateVector n k) u y) x i j := by
    unfold inverseHessianTrace
    simp only [he, Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    try simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  have hterm (k : Fin n) : (∑ i, ∑ j, (hessian u x)⁻¹ i j *
      hessian (fun y => dirDeriv (coordinateVector n k) u y *
        dirDeriv (coordinateVector n k) u y) x i j) =
      2 * dirDeriv (coordinateVector n k) u x *
        dirDeriv (coordinateVector n k) (logHessianDet u) x + 2 * hessian u x k k := by
    rw [hessian_product_trace hΩ (hk k) (hk k) hx (inverseHessian_isSymm hp)]
    change dirDeriv (coordinateVector n k) u x *
        inverseHessianTrace u (dirDeriv (coordinateVector n k) u) x +
      dirDeriv (coordinateVector n k) u x *
        inverseHessianTrace u (dirDeriv (coordinateVector n k) u) x +
      2 * (∑ i, ∑ j, (hessian u x)⁻¹ i j * hessian u x i k * hessian u x j k) = _
    rw [inverseHessianTrace_dirDeriv hΩ hu hx hp, inverse_column_contraction hp]
    ring
  simp_rw [hterm]
  rw [Finset.mul_sum]
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end LogDetGradientEnergy

end
end AffineBernstein
end

end OAI

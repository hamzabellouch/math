import OAI.Geometry.RCD.Sobolev.LipschitzGreenPairing
import OAI.Geometry.RCD.Sobolev.SmoothTestDirectional
import OAI.Geometry.RCD.Metric.EuclideanGreenIdentity

namespace OAI

/-! # The compact-test Laplacian pairing for a Lipschitz Euclidean function -/

open Set Filter MeasureTheory InnerProductSpace Laplacian
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem euclidean_gradient_pairing_sum {n : ℕ} (f ψ : Euclidean n → ℝ) (x : Euclidean n) :
    inner ℝ (gradient f x) (gradient ψ x)=
      ∑ i : Fin n, fderiv ℝ f x (EuclideanSpace.single i 1)*
        fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
  rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.basisFun_apply,inner_gradient_left]
  conv_lhs => rhs; rw [real_inner_comm,inner_gradient_left]

theorem lipschitz_green_trace {n : ℕ} {f ψ : Euclidean n → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) {S : ℝ} (hS : 0<S)
    (hψ : InteriorSmoothTest n S ψ) :
    (∫ x, inner ℝ (gradient f x) (gradient ψ x))= -(∫ x, f x*(Δ ψ) x) := by
  let e := fun i : Fin n => EuclideanSpace.single i (1:ℝ)
  let dψ := fun i : Fin n => fun x => fderiv ℝ ψ x (e i)
  have hdψ (i : Fin n) : InteriorSmoothTest n S (dψ i) := hψ.fderiv_apply (e i)
  have hi (i : Fin n) : Integrable (fun x => fderiv ℝ f x (e i)*dψ i x) volume :=
    lipschitz_directional_integrable hf
      ((hdψ i).1.continuous.integrable_of_hasCompactSupport (hdψ i).2.1) (e i)
  have hj (i : Fin n) : Integrable (fun x => f x*fderiv ℝ (dψ i) x (e i)) volume :=
    (hf.continuous.mul (((hdψ i).1.continuous_fderiv (by simp)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
      ((hdψ i).2.1.fderiv_apply ℝ (e i)).mul_left
  have he (i : Fin n) : (∫ x, fderiv ℝ f x (e i)*dψ i x)=
      -(∫ x, f x*fderiv ℝ (dψ i) x (e i)) :=
    lipschitz_green_directional hf hS (hdψ i) (e i)
  simp_rw [euclidean_gradient_pairing_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib,← integral_finsetSum _ (fun i _ => hj i)]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  rw [laplacian_eq_sum_second_directional (hψ.1.of_le (by simp))]
  dsimp only [dψ,e]
  exact (Finset.mul_sum _ _ _).symm

end RegularPointCoordinates

end

end OAI

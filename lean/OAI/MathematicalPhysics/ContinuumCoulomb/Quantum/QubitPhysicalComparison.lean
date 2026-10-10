import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QubitMediatorTargetGround

namespace OAI

/-! Turning an exact compressed-matrix identity into a physical target-energy
comparison, for the subdivision and third-order constructions. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators InnerProductSpace Classical
variable {σ κ : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]

theorem qmaPhysical_target_error (g : ℝ) (L T : Matrix σ σ ℂ) (D V : κ → Matrix σ σ ℂ)
    (hg : 0 < g) (hL : L.conjTranspose = L) (hD : ∀ e, (D e).conjTranspose = D e)
    (hV : ∀ e, (V e).conjTranspose = V e) {d m η δ : ℝ}
    (hd : 0 ≤ d) (hm : 0 ≤ m) (hsmall : 2*d+4*m ≤ g)
    (hPert : ‖qmaPerturbationOperator L D V‖ ≤ d)
    (hCouple : ∑ e, ‖spinMatrixOperator (V e)‖ ≤ g*η)
    (hM : ‖spinMatrixOperator (qmaThirdMatrix L D V (g:ℂ))‖ ≤ m)
    (hError : ‖spinMatrixOperator (qmaThirdMatrix L D V (g:ℂ)-T)‖ ≤ δ)
    (u : EuclideanSpace ℂ σ) (hu : ‖u‖ = 1) :
    |MediatorGraph.normalizedBottom (qmaPhysicalMediatorMatrix g L D V)-
      MediatorGraph.normalizedBottom T| ≤ (2*d^2/g+2*m)*η^2+δ := by
  have hbound (p : EuclideanSpace ℂ σ) (hp : ‖p‖ = 1) :
      |qmaQuadratic (qmaThirdMatrix L D V (g:ℂ)) (fun i => p i)| ≤ m := by
    have h := (qmaQuadratic_norm_bound _ p).trans
      (mul_le_mul_of_nonneg_right hM (sq_nonneg ‖p‖))
    simpa only [hp,one_pow,mul_one] using h
  have hground := qmaPhysical_thirdOrder_ground g L D V hg hL hD hV hd hm hsmall
    hPert hCouple hbound u hu
  rw [qmaThirdOrderBottom_eq] at hground
  have htarget := qmaNormalizedBottom_norm_error (qmaThirdMatrix L D V (g:ℂ)) T u hu hError
  exact (abs_sub_le _ _ _).trans (add_le_add hground htarget)

end ContinuumCoulomb

end

end OAI

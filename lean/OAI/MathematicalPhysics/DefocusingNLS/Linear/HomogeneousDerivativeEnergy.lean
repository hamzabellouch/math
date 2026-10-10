import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalDerivative

namespace OAI

/-! # The completed-space energy of the ordered derivative tensor -/

open MeasureTheory
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousPhysicalDerivative_energy (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (u : HomogeneousY a N) :
    (∑ j : Fin N → Fin 12, ‖homogeneousPhysicalDerivative a N ha ha1 hk j u‖ ^ 2) =
      ‖homogeneousHighEnergy a N ha1 hk u‖ ^ 2 := by
  have he : (fun v : HomogeneousY a N =>
      ∑ j : Fin N → Fin 12, ‖homogeneousPhysicalDerivative a N ha ha1 hk j v‖ ^ 2) =
      (fun v => ‖homogeneousHighEnergy a N ha1 hk v‖ ^ 2) :=
    (homogeneousSchwartzEmbedding_dense a N ha ha1 hk).equalizer
      (by fun_prop) (by fun_prop) (by
        funext f
        simp only [Function.comp_apply, homogeneousPhysicalDerivative_Schwartz,
          homogeneousOrderedDerivativeL2_norm_sq]
        rw [homogeneousOrderedDerivative_energy]
        exact (homogeneousHighEnergy_Schwartz_norm_sq a N ha ha1 hk
          (radianFourierKernel f)).symm)
  exact congrFun he u

theorem homogeneousPhysicalDerivative_inner (a : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < (N : ℝ)) (u v : HomogeneousY a N) :
    (∑ j : Fin N → Fin 12, inner ℝ
      (homogeneousPhysicalDerivative a N ha ha1 hk j u)
      (homogeneousPhysicalDerivative a N ha ha1 hk j v)) =
      inner ℝ (homogeneousHighEnergy a N ha1 hk u)
        (homogeneousHighEnergy a N ha1 hk v) := by
  have h := homogeneousPhysicalDerivative_energy a N ha ha1 hk (u + v)
  simp only [map_add, norm_add_sq_real, Finset.sum_add_distrib,
    ← Finset.mul_sum, homogeneousPhysicalDerivative_energy] at h
  nlinarith

end DefocusingNLS

end OAI

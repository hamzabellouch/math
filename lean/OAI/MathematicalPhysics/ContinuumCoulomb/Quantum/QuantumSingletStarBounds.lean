import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumSingletStar
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.SpinMatrixNorm

namespace OAI

/-! Full-space norm and low-sector facts for the routing singlet stars. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {κ : Type*} [Fintype κ]

theorem mediatorAxisSpoke_star (n r : ℕ) (e : Fin r) (i : Fin n) (member : Fin 2) :
    (mediatorAxisSpoke n r e i member).conjTranspose = mediatorAxisSpoke n r e i member := by
  simp only [mediatorAxisSpoke,Matrix.conjTranspose_sum,elementaryMediatorSpoke_star]

theorem mediatorAxisSpoke_norm (n r : ℕ) (e : Fin r) (i : Fin n) (member : Fin 2) :
    ‖spinMatrixOperator (mediatorAxisSpoke n r e i member)‖ ≤ 3 := by
  rw [mediatorAxisSpoke,spinMatrixOperator_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _μ : Fin 3, (1:ℝ) := Finset.sum_le_sum (fun μ _ =>
      elementaryMediatorSpoke_operator_norm n r e member μ i)
    _ = 3 := by norm_num

theorem qmaSingletStar_star (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    (qmaSingletStar n r e site member amplitude).conjTranspose =
      qmaSingletStar n r e site member amplitude := by
  simp only [qmaSingletStar,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
    Complex.star_def,Complex.conj_ofReal,mediatorAxisSpoke_star]

theorem qmaSingletStar_norm (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    ‖spinMatrixOperator (qmaSingletStar n r e site member amplitude)‖ ≤
      3*∑ a, |amplitude a| := by
  rw [qmaSingletStar,spinMatrixOperator_sum,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [spinMatrixOperator_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_comm]
  exact mul_le_mul_of_nonneg_right (mediatorAxisSpoke_norm n r e _ _) (abs_nonneg _)

theorem qmaSingletStar_low (n r : ℕ) (e : Fin r) (site : κ → Fin n)
    (member : κ → Fin 2) (amplitude : κ → ℝ) :
    mediatorCompression n r (qmaSingletStar n r e site member amplitude) = 0 := by
  simp only [qmaSingletStar,mediatorAxisSpoke,map_sum,map_smul,
    elementaryMediatorSpoke_low_compression,Finset.sum_const_zero,smul_zero]

theorem qmaRoutingStars_star (n r : ℕ) (site : Fin r → κ → Fin n)
    (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    (qmaRoutingStars n r site member amplitude).conjTranspose =
      qmaRoutingStars n r site member amplitude := by
  simp only [qmaRoutingStars,Matrix.conjTranspose_sum,qmaSingletStar_star]

theorem qmaRoutingStars_low (n r : ℕ) (site : Fin r → κ → Fin n)
    (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    mediatorCompression n r (qmaRoutingStars n r site member amplitude) = 0 := by
  simp only [qmaRoutingStars,map_sum,qmaSingletStar_low,Finset.sum_const_zero]

theorem qmaRoutingStars_norm (n r : ℕ) (site : Fin r → κ → Fin n)
    (member : Fin r → κ → Fin 2) (amplitude : Fin r → κ → ℝ) :
    ‖spinMatrixOperator (qmaRoutingStars n r site member amplitude)‖ ≤
      3*∑ e, ∑ a, |amplitude e a| := by
  rw [qmaRoutingStars,spinMatrixOperator_sum,Finset.mul_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun e _ =>
    qmaSingletStar_norm n r e (site e) (member e) (amplitude e)))

end ContinuumCoulomb

end

end OAI

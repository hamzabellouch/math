import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourLogical

namespace OAI

/-! Logical X and Z fields are realized by internal physical exchanges. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourField (x z : ℝ) : Matrix (Fin 16) (Fin 16) ℂ :=
  ((x/(2*Real.sqrt 3):ℝ):ℂ) • (qmaFourExchange 0 3-qmaFourExchange 0 2)-
    ((z/2:ℝ):ℂ) • qmaFourExchange 0 1

theorem qmaFourField_compression (x z : ℝ) :
    qmaFourEncoding.conjTranspose*qmaFourField x z*qmaFourEncoding =
      (x:ℂ) • pauliX+(z:ℂ) • pauliZ+((z/2:ℝ):ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsc : (Real.sqrt 3:ℂ) ≠ 0 := by exact_mod_cast hs
  simp only [qmaFourField,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul]
  rw [qmaFourEncoding_compression 0 3 (by decide),
    qmaFourEncoding_compression 0 2 (by decide),qmaFourEncoding_compression 0 1 (by decide),
    qmaFourLogical_X,qmaFourLogical_Z]
  push_cast
  simp only [smul_smul,smul_sub,smul_neg]
  have hx : ((x:ℂ)/(2*(Real.sqrt 3:ℂ)))*(2*(Real.sqrt 3:ℂ)) = x := by field_simp
  have hz : ((z:ℂ)/2)*2 = z := by ring
  rw [hx,hz]
  module

end ContinuumCoulomb

end

end OAI

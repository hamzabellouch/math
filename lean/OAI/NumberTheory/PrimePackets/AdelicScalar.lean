import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicReduction

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise
open Matrix Module Filter Set
namespace PrimeDegreePackets.Adelic

open Matrix
 
def IntegralFiniteScalar (u : RationalFiniteAdelesˣ) : Prop :=
  ∀ p : Nat.Primes, u.val p ∈ rationalLocalIntegers p ∧ (u⁻¹).val p ∈ rationalLocalIntegers p

 
theorem finite_scalar_rational_integral (a : RationalFiniteAdelesˣ) :
    ∃ q : ℚˣ, ∃ z : RationalFiniteAdelesˣ, IntegralFiniteScalar z ∧
      a = Units.map rationalFiniteEmbedding.toMonoidHom q * z := by
  let b : Basis (Fin 1) ℚ ℚ := Module.finBasisOfFinrankEq ℚ ℚ (by simp)
  obtain ⟨c,hc⟩ := finite_matrix_rational_reduction (by simp : finrank ℚ ℚ = 1) b
    (GeneralLinearGroup.scalar (Fin 1) a)
  let k := GeneralLinearGroup.map rationalFiniteEmbedding c * GeneralLinearGroup.scalar (Fin 1) a
  refine ⟨(GeneralLinearGroup.det c)⁻¹,GeneralLinearGroup.det k,?_,?_⟩
  · intro p
    constructor
    · change k.val.det p ∈ rationalLocalIntegers p
      simpa only [Matrix.det_fin_one] using hc.1 0 0 p
    · change (k⁻¹).val.det p ∈ rationalLocalIntegers p
      simpa only [Matrix.det_fin_one] using hc.2 0 0 p
  · dsimp only [k]
    rw [map_mul,GeneralLinearGroup.map_det,GeneralLinearGroup.det_scalar]
    simp

end PrimeDegreePackets.Adelic

end

end OAI

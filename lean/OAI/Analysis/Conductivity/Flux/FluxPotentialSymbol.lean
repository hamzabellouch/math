import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Matrix

def fluxPotentialSymbol {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R]
    (D : Matrix m n R) (N : Matrix n m R) : Matrix n n R :=
  (D * N).det • 1 - N * (D * N).adjugate * D

theorem fluxPotentialSymbol_div {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R]
    (D : Matrix m n R) (N : Matrix n m R) :
    D * fluxPotentialSymbol D N = 0 := by
  unfold fluxPotentialSymbol
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_adjugate,
    Matrix.smul_mul, Matrix.one_mul, sub_self]

theorem fluxPotentialSymbol_on_ker {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [CommRing R]
    (D : Matrix m n R) (N : Matrix n m R) (v : n → R)
    (hv : D *ᵥ v = 0) :
    fluxPotentialSymbol D N *ᵥ v = (D * N).det • v := by
  simp only [fluxPotentialSymbol, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, sub_zero]

theorem fluxPotentialSymbol_range {m n K : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Field K]
    (D : Matrix m n K) (N : Matrix n m K) (hdet : (D * N).det ≠ 0) :
    Set.range (fluxPotentialSymbol D N).mulVec =
      {v | D *ᵥ v = 0} := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    simp only [Set.mem_ofPred_eq, Matrix.mulVec_mulVec,
      fluxPotentialSymbol_div, Matrix.zero_mulVec]
  · intro hv
    refine ⟨((D * N).det)⁻¹ • v, ?_⟩
    rw [Matrix.mulVec_smul, fluxPotentialSymbol_on_ker D N v hv,
      smul_smul, inv_mul_cancel₀ hdet, one_smul]

end ScalarConductivity

end

end OAI

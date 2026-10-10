import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliMonomial
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourGround

namespace OAI

/-! Physical single-spin actions on the four-spin encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourSpinIndex (i : Fin 4) (μ : Fin 3) (s : Fin 16) : Fin 16 :=
  qmaFourIndex (Function.update (qmaFourBits s) i (qmaPauliBit μ (qmaFourBits s i)))

def qmaFourSpinRational (i : Fin 4) (μ : Fin 3) : Matrix (Fin 16) (Fin 16) ℚ :=
  fun s t => qmaPhysicalPauliSign μ (qmaFourBits s i)*
    (if qmaFourSpinIndex i μ s = t then 1 else 0)

def qmaFourSpin (i : Fin 4) (μ : Fin 3) : Matrix (Fin 16) (Fin 16) ℂ :=
  qmaPauliPhase μ • (qmaFourSpinRational i μ).map (Rat.castHom ℂ)

theorem qmaFourSpin_source (i : Fin 4) (μ : Fin 3) : qmaFourSpin i μ =
    (sourceLocalPauli 4 i μ).submatrix qmaFourBits qmaFourBits := by
  ext s t
  have he : qmaFourSpinIndex i μ s = t ↔
      Function.update (qmaFourBits s) i (qmaPauliBit μ (qmaFourBits s i)) = qmaFourBits t :=
    qmaFourBasisEquiv.eq_symm_apply.symm
  simp only [qmaFourSpin,Matrix.smul_apply,smul_eq_mul,Matrix.map_apply,
    qmaFourSpinRational,map_mul,Matrix.submatrix_apply,qmaLocalPauli_monomial]
  by_cases h : qmaFourSpinIndex i μ s = t
  · simp [h,he.mp h]
  · have ht := mt he.mpr h
    simp [h,ht]

theorem qmaFourSpinRational_mulVec (i : Fin 4) (μ : Fin 3) (v : Fin 16 → ℚ) (s : Fin 16) :
    (qmaFourSpinRational i μ *ᵥ v) s =
      qmaPhysicalPauliSign μ (qmaFourBits s i)*v (qmaFourSpinIndex i μ s) := by
  simp only [qmaFourSpinRational,Matrix.mulVec,dotProduct,mul_assoc,← Finset.mul_sum,
    ite_mul,one_mul,zero_mul]
  simp

def qmaFourSpinRawAction (i : Fin 4) (μ : Fin 3) : Matrix (Fin 16) (Fin 2) ℚ :=
  fun s b => qmaPhysicalPauliSign μ (qmaFourBits s i)*qmaFourRawEncoding (qmaFourSpinIndex i μ s) b

theorem qmaFourSpinRawAction_eq (i : Fin 4) (μ : Fin 3) :
    qmaFourSpinRational i μ*qmaFourRawEncoding = qmaFourSpinRawAction i μ := by
  ext s b
  exact qmaFourSpinRational_mulVec i μ (fun t => qmaFourRawEncoding t b) s

theorem qmaFourSpin_encoding (i : Fin 4) (μ : Fin 3) :
    qmaFourSpin i μ*qmaFourEncoding = qmaPauliPhase μ •
      ((qmaFourSpinRawAction i μ).map (Rat.castHom ℂ)*qmaFourNormalization) := by
  rw [qmaFourSpin,qmaFourEncoding,Matrix.smul_mul,← Matrix.mul_assoc,qmaFourRawComplex,
    ← Matrix.map_mul,qmaFourSpinRawAction_eq]

end ContinuumCoulomb

end

end OAI

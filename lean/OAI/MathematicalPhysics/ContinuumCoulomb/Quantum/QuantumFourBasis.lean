import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePauli
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRectangularOperator

namespace OAI

/-! Fixed four-spin coordinates for the exchange-only encoding. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaFourBits (n : Fin 16) : Fin 4 → Fin 2 :=
  ![⟨n.val/8,by have hn := n.isLt; omega⟩,
    ⟨n.val/4%2,by omega⟩,⟨n.val/2%2,by omega⟩,⟨n.val%2,by omega⟩]

def qmaFourIndex (s : Fin 4 → Fin 2) : Fin 16 :=
  ⟨8*(s 0).val+4*(s 1).val+2*(s 2).val+(s 3).val,by
    have h0 := (s 0).isLt
    have h1 := (s 1).isLt
    have h2 := (s 2).isLt
    have h3 := (s 3).isLt
    omega⟩

def qmaFourBasisEquiv : (Fin 4 → Fin 2) ≃ Fin 16 where
  toFun := qmaFourIndex
  invFun := qmaFourBits
  left_inv s := by
    funext i
    have h0 := (s 0).isLt
    have h1 := (s 1).isLt
    have h2 := (s 2).isLt
    have h3 := (s 3).isLt
    fin_cases i <;> apply Fin.ext <;> simp [qmaFourBits,qmaFourIndex] <;> omega
  right_inv n := by
    apply Fin.ext
    have hn := n.isLt
    simp [qmaFourBits,qmaFourIndex]
    omega

def qmaFourExchangeRational (i j : Fin 4) : Matrix (Fin 16) (Fin 16) ℚ :=
  fun s t => 2*(if qmaFourIndex (sourceSpinSwap i j (qmaFourBits s)) = t then 1 else 0)-
    (if s = t then 1 else 0)

def qmaFourExchange (i j : Fin 4) : Matrix (Fin 16) (Fin 16) ℂ :=
  fun s t => qmaFourExchangeRational i j s t

theorem qmaFourExchange_source (i j : Fin 4) : qmaFourExchange i j =
    (sourceHeisenbergMatrix 4 i j).submatrix qmaFourBits qmaFourBits := by
  have hs (s t : Fin 16) : qmaFourIndex (sourceSpinSwap i j (qmaFourBits s)) = t ↔
      sourceSpinSwap i j (qmaFourBits s) = qmaFourBits t := by
    exact (qmaFourBasisEquiv.eq_symm_apply).symm
  have he (s t : Fin 16) : s = t ↔ qmaFourBits s = qmaFourBits t :=
    qmaFourBasisEquiv.symm.injective.eq_iff.symm
  ext s t
  simp only [qmaFourExchange,qmaFourExchangeRational,sourceHeisenbergMatrix,Matrix.submatrix_apply]
  simp only [hs,he]
  split_ifs <;> norm_num

end ContinuumCoulomb

end

end OAI

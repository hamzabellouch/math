import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliExpansion

namespace OAI

/-! Hermitian local matrices have real Pauli coefficients. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauliCoefficient_star (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : A.IsHermitian) (w : ι → Fin 4) :
    star (qmaPauliCoefficient A w) = qmaPauliCoefficient A w := by
  have hs : star (∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A s t*qmaPauliWord w t s) =
      ∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A s t*qmaPauliWord w t s := by
    calc
      _ = ∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A t s*qmaPauliWord w s t := by
        simp only [star_sum,star_mul,hA.apply,(qmaPauliWord_hermitian w).apply]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = _ := Finset.sum_comm
  simp [qmaPauliCoefficient,hs]

theorem qmaPauliCoefficient_real (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hA : A.IsHermitian) (w : ι → Fin 4) : (qmaPauliCoefficient A w).im = 0 := by
  have h := congrArg Complex.im (qmaPauliCoefficient_star A hA w)
  simp only [Complex.star_def,Complex.conj_im] at h
  linarith

theorem qmaPauli_real_expansion (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (hA : A.IsHermitian) :
    (∑ w : ι → Fin 4, ((qmaPauliCoefficient A w).re : ℂ) • qmaPauliWord w) = A := by
  have he (w : ι → Fin 4) : ((qmaPauliCoefficient A w).re : ℂ) = qmaPauliCoefficient A w := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using (qmaPauliCoefficient_real A hA w).symm
  simp only [he,qmaPauli_expansion]

end ContinuumCoulomb

end

end OAI

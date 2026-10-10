import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliReal

namespace OAI

/-! A real Hermitian matrix contains only Pauli words with an even number
of imaginary Y factors. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

def qmaPauliSign (i : Fin 4) : ℂ := if i = 2 then -1 else 1

theorem qmaPauli_conjugate (i : Fin 4) (a b : Fin 2) :
    star (qmaPauli i a b) = qmaPauliSign i*qmaPauli i a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [qmaPauli,qmaPauliSign,pauliX,pauliY,pauliZ]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def qmaPauliYCount (w : ι → Fin 4) : ℕ := (Finset.univ.filter (fun i => w i = 2)).card

omit [DecidableEq ι] in
theorem qmaPauliWord_conjugate (w : ι → Fin 4) (s t : ι → Fin 2) :
    star (qmaPauliWord w s t) = (-1:ℂ)^qmaPauliYCount w*qmaPauliWord w s t := by
  simp only [qmaPauliWord,star_prod,qmaPauli_conjugate,Finset.prod_mul_distrib]
  congr 1
  simp [qmaPauliSign,qmaPauliYCount,Finset.prod_ite]

theorem qmaPauliCoefficient_conjugate_of_real
    (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (hA : ∀ s t, (A s t).im = 0)
    (w : ι → Fin 4) :
    star (qmaPauliCoefficient A w) = (-1:ℂ)^qmaPauliYCount w*qmaPauliCoefficient A w := by
  have ha (s t : ι → Fin 2) : star (A s t) = A s t := by
    apply Complex.ext
    · rfl
    · simp [hA]
  have hs : star (∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A s t*qmaPauliWord w t s) =
      (-1:ℂ)^qmaPauliYCount w*(∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A s t*qmaPauliWord w t s) := by
    simp only [star_sum,star_mul,ha,qmaPauliWord_conjugate,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hi : star (((2:ℂ)^Fintype.card ι)⁻¹) = ((2:ℂ)^Fintype.card ι)⁻¹ := by
    change (starRingEnd ℂ) (((2:ℂ)^Fintype.card ι)⁻¹) = _
    rw [map_inv₀,map_pow]
    have h2 : (starRingEnd ℂ) (2:ℂ) = 2 := by simp only [starRingEnd_apply]; norm_num
    rw [h2]
  unfold qmaPauliCoefficient
  calc
    _ = star (∑ s : ι → Fin 2, ∑ t : ι → Fin 2, A s t*qmaPauliWord w t s)*
        star (((2:ℂ)^Fintype.card ι)⁻¹) := star_mul _ _
    _ = ((-1:ℂ)^qmaPauliYCount w*(∑ s : ι → Fin 2, ∑ t : ι → Fin 2,
        A s t*qmaPauliWord w t s))*((2:ℂ)^Fintype.card ι)⁻¹ := congrArg₂ (· * ·) hs hi
    _ = _ := by ring

theorem qmaPauliCoefficient_odd_zero (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hH : A.IsHermitian) (hR : ∀ s t, (A s t).im = 0)
    (w : ι → Fin 4) (hw : Odd (qmaPauliYCount w)) : qmaPauliCoefficient A w = 0 := by
  have hs := qmaPauliCoefficient_conjugate_of_real A hR w
  rw [qmaPauliCoefficient_star A hH w,hw.neg_one_pow] at hs
  have he : (2:ℂ)*qmaPauliCoefficient A w = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

end ContinuumCoulomb

end

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliParity

namespace OAI

/-! Fixed-width Pauli tables.  Padding a local word duplicates its coefficient
by a known factor; replacing odd-Y zero terms by the identity keeps every
emitted word real without a dependent filtered index type. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPaddedPauli
open scoped BigOperators Classical

def splitWords (n m : ℕ) : (Fin (n+m) → Fin 4) ≃
    ((Fin n → Fin 4) × (Fin m → Fin 4)) :=
  ((finSumFinEquiv.symm).arrowCongr (Equiv.refl (Fin 4))).trans
    (Equiv.sumArrowEquivProdArrow (Fin n) (Fin m) (Fin 4))

def restrictWord (n m : ℕ) (w : Fin (n+m) → Fin 4) : Fin n → Fin 4 :=
  fun i => w (Fin.castAdd m i)

theorem splitWords_first (n m : ℕ) (w : Fin (n+m) → Fin 4) :
    (splitWords n m w).1 = restrictWord n m w := rfl

theorem sum_restrict {A : Type} [AddCommMonoid A] (n m : ℕ)
    (f : (Fin n → Fin 4) → A) :
    (∑ w : Fin (n+m) → Fin 4, f (restrictWord n m w)) =
      4^m • ∑ v : Fin n → Fin 4, f v := by
  calc
    _ = ∑ p : (Fin n → Fin 4) × (Fin m → Fin 4), f p.1 :=
      (splitWords n m).sum_comp (fun p => f p.1)
    _ = _ := by simp [Fintype.sum_prod_type,Finset.sum_nsmul]

theorem normalized_sum_restrict {A : Type} [AddCommMonoid A] [Module ℂ A]
    (n m : ℕ) (f : (Fin n → Fin 4) → A) :
    (∑ w : Fin (n+m) → Fin 4, ((4:ℂ)^m)⁻¹ • f (restrictWord n m w)) =
      ∑ v : Fin n → Fin 4, f v := by
  rw [← Finset.smul_sum, sum_restrict, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def evenWord (w : ι → Fin 4) : ι → Fin 4 :=
  if Even (qmaPauliYCount w) then w else fun _ => 0

def evenCoefficient (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ) (w : ι → Fin 4) : ℝ :=
  if Even (qmaPauliYCount w) then (qmaPauliCoefficient A w).re else 0

omit [DecidableEq ι] in
theorem evenWord_even (w : ι → Fin 4) : Even (qmaPauliYCount (evenWord w)) := by
  unfold evenWord
  split_ifs with h
  · exact h
  · simp [qmaPauliYCount]

theorem even_expansion (A : Matrix (ι → Fin 2) (ι → Fin 2) ℂ)
    (hH : A.IsHermitian) (hR : ∀ s t, (A s t).im = 0) :
    (∑ w : ι → Fin 4, (evenCoefficient A w:ℂ) • qmaPauliWord (evenWord w)) = A := by
  calc
    _ = ∑ w : ι → Fin 4, ((qmaPauliCoefficient A w).re:ℂ) • qmaPauliWord w := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases he : Even (qmaPauliYCount w)
      · simp only [evenCoefficient,evenWord,he,ite_true]
      · have ho := (Nat.even_or_odd (qmaPauliYCount w)).resolve_left he
        have hz := qmaPauliCoefficient_odd_zero A hH hR w ho
        simp only [evenCoefficient,evenWord,he,ite_false,hz,Complex.zero_re,
          Complex.ofReal_zero,zero_smul]
    _ = A := qmaPauli_real_expansion A hH

def paddedWord (n m : ℕ) (w : Fin (n+m) → Fin 4) : Fin n → Fin 4 :=
  evenWord (restrictWord n m w)

def paddedCoefficient (n m : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (w : Fin (n+m) → Fin 4) : ℝ :=
  evenCoefficient A (restrictWord n m w)/(4:ℝ)^m

theorem paddedWord_even (n m : ℕ) (w : Fin (n+m) → Fin 4) :
    Even (qmaPauliYCount (paddedWord n m w)) := evenWord_even _

theorem padded_expansion (n m : ℕ)
    (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hH : A.IsHermitian) (hR : ∀ s t, (A s t).im = 0) :
    (∑ w : Fin (n+m) → Fin 4,
      (paddedCoefficient n m A w:ℂ) • qmaPauliWord (paddedWord n m w)) = A := by
  let f : (Fin n → Fin 4) → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
    fun v => (evenCoefficient A v:ℂ) • qmaPauliWord (evenWord v)
  have hf : (∑ w : Fin (n+m) → Fin 4, ((4:ℂ)^m)⁻¹ • f (restrictWord n m w)) =
      ∑ v : Fin n → Fin 4, f v := normalized_sum_restrict n m f
  calc
    _ = ∑ w : Fin (n+m) → Fin 4,
        ((4:ℂ)^m)⁻¹ • f (restrictWord n m w) := by
      apply Finset.sum_congr rfl
      intro w _
      dsimp only [paddedCoefficient,paddedWord,f]
      rw [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_ofNat,smul_smul]
      congr 1
      rw [div_eq_mul_inv,mul_comm]
    _ = ∑ v : Fin n → Fin 4, f v := hf
    _ = A := even_expansion A hH hR

theorem six_word_count : Fintype.card (Fin 6 → Fin 4) = 4096 := by
  simp

end ContinuumCoulomb.QuantumPaddedPauli

end

end OAI

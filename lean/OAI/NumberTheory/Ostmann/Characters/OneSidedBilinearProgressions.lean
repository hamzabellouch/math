import OAI.NumberTheory.Ostmann.Characters.OneSidedBilinearCauchy

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters

def progressionVariation (w : ℕ → ℂ) (N : ℕ) : ℝ :=
  ‖w (N-1)‖ + ∑ n ∈ Finset.range (N-1), ‖w (n+1)-w n‖

theorem crtProduct_natCast {q q' : ℕ} (h : q.Coprime q')
    (χ : MulChar (ZMod q) ℂ) (ξ : MulChar (ZMod q') ℂ) (n : ℕ) :
    crtProduct h χ ξ (n : ZMod (q*q')) = χ (n : ZMod q) * conj (ξ (n : ZMod q')) := by
  unfold crtProduct
  rw [map_natCast]
  rfl

theorem norm_character_cross_progression_le {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime]
    (h : q.Coprime q') (χ : MulChar (ZMod q) ℂ) (ξ : MulChar (ZMod q') ℂ)
    (hχ : χ ≠ 1) (Q a : ℕ) (hQ : Q.Coprime (q*q')) (w : ℕ → ℂ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N,
      w n * χ ((Q*n+a : ℕ) : ZMod q) * conj (ξ ((Q*n+a : ℕ) : ZMod q'))‖ ≤
      (q*q' : ℕ) * progressionVariation w N := by
  have hbound := norm_crtProduct_weighted_sum_le h χ ξ hχ
    (ZMod.unitOfCoprime Q hQ) (a : ZMod (q*q')) w N
  have heq (n : ℕ) :
      (↑(ZMod.unitOfCoprime Q hQ) * (n : ZMod (q*q')) + a) =
        ((Q*n+a : ℕ) : ZMod (q*q')) := by simp
  simp_rw [heq, crtProduct_natCast] at hbound
  simpa only [progressionVariation, mul_assoc] using hbound

variable {κ : Type*}

def primeCharacterKernel (q : κ → ℕ) (χ : ∀ j, MulChar (ZMod (q j)) ℂ)
    (Q a : ℕ) (W : ℕ → κ → ℂ) (n : ℕ) (j : κ) : ℂ :=
  χ j ((Q*n+a : ℕ) : ZMod (q j)) * W n j

def crossProgressionWeight (b : ℕ → ℝ) (W : ℕ → κ → ℂ) (j k : κ) (n : ℕ) : ℂ :=
  (b n : ℂ) * W n j * conj (W n k)

theorem characterGram_eq_progression (q : κ → ℕ) (χ : ∀ j, MulChar (ZMod (q j)) ℂ)
    (Q a N : ℕ) (b : ℕ → ℝ) (W : ℕ → κ → ℂ) (j k : κ) :
    oneSidedGram (fun n : Fin N => b n)
      (fun n : Fin N => primeCharacterKernel q χ Q a W n) j k =
      ∑ n ∈ Finset.range N, crossProgressionWeight b W j k n *
        χ j ((Q*n+a : ℕ) : ZMod (q j)) * conj (χ k ((Q*n+a : ℕ) : ZMod (q k))) := by
  unfold oneSidedGram
  dsimp only
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
    (b n : ℂ) * primeCharacterKernel q χ Q a W n j *
      conj (primeCharacterKernel q χ Q a W n k)) N]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [primeCharacterKernel, crossProgressionWeight, map_mul]
  ring

theorem characterGram_bound (q : κ → ℕ) (hq : ∀ j, (q j).Prime)
    (χ : ∀ j, MulChar (ZMod (q j)) ℂ) (hχ : ∀ j, χ j ≠ 1)
    (Q a N : ℕ) (hQ : ∀ j, Q.Coprime (q j))
    (b : ℕ → ℝ) (W : ℕ → κ → ℂ) (j k : κ) (hjk : q j ≠ q k) :
    ‖oneSidedGram (fun n : Fin N => b n)
      (fun n : Fin N => primeCharacterKernel q χ Q a W n) j k‖ ≤
      (q j * q k : ℕ) * progressionVariation (crossProgressionWeight b W j k) N := by
  let : Fact (q j).Prime := ⟨hq j⟩
  let : Fact (q k).Prime := ⟨hq k⟩
  rw [characterGram_eq_progression]
  exact norm_character_cross_progression_le ((Nat.coprime_primes (hq j) (hq k)).mpr hjk)
    (χ j) (χ k) (hχ j) Q a ((hQ j).mul_right (hQ k)) _ N

end Ostmann.Characters

end

end OAI

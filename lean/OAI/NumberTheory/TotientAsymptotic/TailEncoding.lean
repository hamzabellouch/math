import OAI.NumberTheory.TotientAsymptotic.TailArray
import OAI.NumberTheory.TotientAsymptotic.CofactorMass
import OAI.NumberTheory.TotientAsymptotic.PrimeBoxGeometry

namespace OAI

/-! A fixed cofactor and the ordered tail-prime vector determine a witness. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def tailPrimeVector {H : ℕ} (η : TailDatum H) : Fin (H-P H) → ℕ :=
  fun i => tailPrime η (H-1-i.val)

lemma tailVector_eq_primeCoord {H : ℕ} (η : TailDatum H) :
    tailVector η = primePrefixCoord (tailPrimeVector η) := rfl

lemma tailPrimeVector_prime {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) (i : Fin (H-P H)) : (tailPrimeVector η i).Prime := by
  apply (hη.2.2.1 _ _).1
  have := i.isLt
  exact Finset.mem_Ico.mpr (by omega)

lemma tailDatum_eq_of_primeVector {H : ℕ} {s t : ℝ} {η ξ : TailDatum H}
    (hη : IsWitness H s η) (hξ : IsWitness H t ξ)
    (hcof : η.cofactor=ξ.cofactor) (hvec : tailPrimeVector η=tailPrimeVector ξ) : η=ξ := by
  have hQ : η.Q=ξ.Q := by
    funext i
    by_cases hi : i.val < P H
    · rw [hη.1 i hi, hξ.1 i hi]
    · have hib := i.isLt
      let j : Fin (H-P H) := ⟨H-1-i.val, by omega⟩
      have hh := congrFun hvec j
      have he : H-1-j.val=i.val := by dsimp [j]; omega
      simpa only [tailPrimeVector, he, tailPrime, dite_eq_left i.isLt] using hh
  cases η
  cases ξ
  cases hQ
  cases hcof
  rfl

lemma prod_tail_indices {M : Type*} [CommMonoid M] {H : ℕ} (hPH : P H ≤ H) (f : ℕ → M) :
    (∏ l ∈ Finset.Ico (P H) H, f l) = ∏ i : Fin (H-P H), f (H-1-i.val) := by
  apply Finset.prod_bij (fun l hl => (⟨H-1-l, by
    have := Finset.mem_Ico.mp hl
    omega⟩ : Fin (H-P H)))
  · intro l hl
    exact Finset.mem_univ _
  · intro l hl k hk he
    have := Finset.mem_Ico.mp hl
    have := Finset.mem_Ico.mp hk
    have hv := congrArg Fin.val he
    simp only at hv
    omega
  · intro i _
    have hi := i.isLt
    refine ⟨H-1-i.val, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Fin.ext
    simp only
    omega
  · intro l hl
    have := Finset.mem_Ico.mp hl
    have he : H-1-(H-1-l)=l := by omega
    rw [he]

lemma tail_value_eq_vector {H : ℕ} (η : TailDatum H) (hPH : P H ≤ H) :
    w η = η.cofactor*∏ i, tailPrimeVector η i := by
  rw [w, prod_tail_indices hPH]
  rfl

lemma tail_reciprocal_vector {H : ℕ} {s : ℝ} {η : TailDatum H}
    (hη : IsWitness H s η) (hPH : P H ≤ H) :
    ((w η).totient : ℝ)⁻¹ ≤
      (η.cofactor.totient : ℝ)⁻¹*reciprocalShiftWeight (tailPrimeVector η) := by
  have hh := tail_reciprocal_majorant hη
  rw [prod_tail_indices hPH] at hh
  have he : (∏ i : Fin (H-P H), (tailPrime η (H-1-i.val)-1 : ℝ)⁻¹) =
      reciprocalShiftWeight (tailPrimeVector η) := by
    unfold reciprocalShiftWeight
    rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (tailPrimeVector_prime hη i).one_lt.le, Nat.cast_one]
    rfl
  rwa [he] at hh

end TotientAsymptotic

end

end OAI

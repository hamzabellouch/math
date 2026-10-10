import OAI.NumberTheory.Jacobsthal.Estimates.CoefficientHeightChoice
import OAI.NumberTheory.Jacobsthal.Primes.PrimeProductLifting
import OAI.NumberTheory.Jacobsthal.Sieve.LineCongruenceConstruction

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

def constraintVolume (P : Finset ℕ) (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) : ℕ :=
  ∏ p : P, p.val^((D+1)*(T p).card)

noncomputable def logarithmicCost (P : Finset ℕ) (T : ∀ p : P, Finset (ZMod p.val)) : ℝ :=
  ∑ p : P, ((T p).card : ℝ)*Real.log (p.val : ℝ)

theorem constraintVolume_pos (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) : 0 < constraintVolume P T D := by
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (hP p p.property) _

theorem constraintVolume_log (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (D : ℕ) :
    Real.log (constraintVolume P T D : ℝ) = ((D : ℝ)+1)*logarithmicCost P T := by
  classical
  unfold constraintVolume logarithmicCost
  simp only [Nat.cast_prod,Nat.cast_pow]
  rw [Real.log_prod (by
    intro p hp
    exact pow_ne_zero _ (by exact_mod_cast (Nat.ne_of_gt (hP p p.property))))]
  simp only [Real.log_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem dimension_pos (D : ℕ) : 0 < (D+2).choose 2 := Nat.choose_pos (by omega)

theorem dimension_ratio (D : ℕ) :
    ((D : ℝ)+1)/((D+2).choose 2 : ℝ) = 2/((D : ℝ)+2) := by
  have hNat : (D+2)*(D+1) = (D+2).choose 2*2 := by
    simpa only [Nat.choose_one_right,Nat.add_assoc] using Nat.add_one_mul_choose_eq (D+1) 1
  have hReal : ((D : ℝ)+2)*((D : ℝ)+1) = ((D+2).choose 2 : ℝ)*2 := by exact_mod_cast hNat
  apply (div_eq_div_iff (by exact_mod_cast (dimension_pos D).ne') (by positivity)).mpr
  nlinarith only [hReal]

theorem exists_small_line_polynomial (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (a : ∀ p : P, ZMod p.val) (D : ℕ) :
    ∃ (Q : MvPolynomial (Fin 2) ℤ) (H : ℕ), Q ≠ 0 ∧ Q.totalDegree ≤ D ∧ 0 < H ∧
      (∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) ∧
      (∀ p : P, ∀ s : T p, lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val Q = 0) ∧
      Real.log (2*(H : ℝ)) ≤ Real.log 4 + 2/((D : ℝ)+2)*logarithmicCost P T := by
  let M := constraintVolume P T D
  let N := (D+2).choose 2
  let H := boxHeight M N
  have hM : 0 < M := constraintVolume_pos P hP T D
  have hN : 0 < N := dimension_pos D
  obtain ⟨Q,hQ,hdegree,hcoeff,hline⟩ := exists_line_congruence_polynomial P hP T a D H
    (boxHeight_card_strict hN)
  refine ⟨Q,H,hQ,hdegree,boxHeight_pos hM,hcoeff,hline,?_⟩
  have hlog := boxHeight_log_bound hM hN
  change Real.log (2*(H : ℝ)) ≤ Real.log 4 + Real.log (constraintVolume P T D : ℝ)/((D+2).choose 2 : ℝ) at hlog
  rw [constraintVolume_log P hP T D] at hlog
  have he : (((D : ℝ)+1)*logarithmicCost P T)/((D+2).choose 2 : ℝ) =
      2/((D : ℝ)+2)*logarithmicCost P T := by
    calc
      _ = (((D : ℝ)+1)/((D+2).choose 2 : ℝ))*logarithmicCost P T := by ring
      _ = _ := by rw [dimension_ratio]
  rwa [he] at hlog

end ErdosAuxiliaryPolynomial

end

section

namespace ErdosAuxiliaryPolynomial

noncomputable def valueBudget (D H : ℕ) (S : ℝ) : ℝ :=
  ((D+2).choose 2 : ℝ)*(H : ℝ)*(max 1 S)^D

noncomputable def logarithmicValueBudget (D H : ℕ) (S : ℝ) : ℝ :=
  Real.log ((D+2).choose 2 : ℝ)+Real.log (H : ℝ)+(D : ℝ)*Real.log (max 1 S)

theorem valueBudget_pos (D H : ℕ) (hH : 0 < H) (S : ℝ) : 0 < valueBudget D H S := by
  have hN : (0 : ℝ) < ((D+2).choose 2 : ℝ) := by exact_mod_cast dimension_pos D
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hM : (0 : ℝ) < max 1 S := zero_lt_one.trans_le (le_max_left _ _)
  exact mul_pos (mul_pos hN hH0) (pow_pos hM D)

theorem valueBudget_log (D H : ℕ) (hH : 0 < H) (S : ℝ) :
    Real.log (valueBudget D H S) = logarithmicValueBudget D H S := by
  have hN : (((D+2).choose 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (dimension_pos D).ne'
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hM : (max 1 S : ℝ) ≠ 0 := (zero_lt_one.trans_le (le_max_left _ _)).ne'
  rw [valueBudget,Real.log_mul (mul_ne_zero hN hH0) (pow_ne_zero D hM),
    Real.log_mul hN hH0,Real.log_pow]
  rfl

theorem prime_product_log (I : Finset ℕ) (hprime : ∀ p ∈ I, Nat.Prime p) :
    Real.log ((∏ p ∈ I, p : ℕ) : ℝ) = ∑ p ∈ I, Real.log (p : ℝ) := by
  rw [Nat.cast_prod]
  exact Real.log_prod (fun p hp => by exact_mod_cast (hprime p hp).ne_zero)

theorem polynomial_log_value_bound (Q : MvPolynomial (Fin 2) ℤ) (D H : ℕ)
    (hD : Q.totalDegree ≤ D) (hH : ∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) (hHpos : 0 < H)
    (S : ℝ) (x y : ℤ) (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S)
    (hne : MvPolynomial.eval ![x,y] Q ≠ 0) :
    Real.log |(MvPolynomial.eval ![x,y] Q : ℝ)| ≤ logarithmicValueBudget D H S := by
  rw [← valueBudget_log D H hHpos S]
  apply Real.log_le_log
  · apply abs_pos.mpr
    exact_mod_cast hne
  · exact polynomial_value_bound Q D H hD hH S x y hx hy

theorem value_zero_of_log_prime_budget (Q : MvPolynomial (Fin 2) ℤ) (D H : ℕ)
    (hD : Q.totalDegree ≤ D) (hH : ∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) (hHpos : 0 < H)
    (S : ℝ) (x y : ℤ) (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S)
    (I : Finset ℕ) (hprime : ∀ p ∈ I, Nat.Prime p) (a s : ∀ p : I, ZMod p.val)
    (hline : ∀ p : I, lineSub (Int.castRingHom (ZMod p.val)) (a p) (s p) Q = 0)
    (hinc : ∀ p : I, (y : ZMod p.val) = a p-s p*(x : ZMod p.val))
    (hlarge : logarithmicValueBudget D H S < ∑ p ∈ I, Real.log (p : ℝ)) :
    MvPolynomial.eval ![x,y] Q = 0 := by
  apply value_zero_of_incident_prime_product Q D H hD hH S x y hx hy I hprime a s hline hinc
  have hp : (0 : ℝ) < ((∏ p ∈ I, p : ℕ) : ℝ) := by
    exact_mod_cast (Finset.prod_pos (fun p hp => (hprime p hp).pos))
  apply (Real.log_lt_log_iff (valueBudget_pos D H hHpos S) hp).mp
  rw [valueBudget_log D H hHpos S,prime_product_log I hprime]
  exact hlarge

end ErdosAuxiliaryPolynomial

end

section

namespace ErdosAuxiliaryPolynomial

def LineIncidence (P : Finset ℕ) (T : ∀ p : P, Finset (ZMod p.val))
    (a : ∀ p : P, ZMod p.val) (x y : ℤ) (p : P) : Prop :=
  ∃ s : T p, (y : ZMod p.val) = a p-s.val*(x : ZMod p.val)

theorem exists_auxiliary_polynomial_lifting (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (T : ∀ p : P, Finset (ZMod p.val)) (a : ∀ p : P, ZMod p.val) (D : ℕ) :
    ∃ (Q : MvPolynomial (Fin 2) ℤ) (H : ℕ), Q ≠ 0 ∧ Q.totalDegree ≤ D ∧ 0 < H ∧
      (∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ)) ∧
      (∀ p : P, ∀ s : T p, lineSub (Int.castRingHom (ZMod p.val)) (a p) s.val Q = 0) ∧
      Real.log (2*(H : ℝ)) ≤ Real.log 4+2/((D : ℝ)+2)*logarithmicCost P T ∧
      ∀ (S : ℝ) (x y : ℤ), (0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) →
        (0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S) →
        ∀ (I : Finset ℕ) (hIP : I ⊆ P),
          (∀ p : I, LineIncidence P T a x y ⟨p.val,hIP p.property⟩) →
          logarithmicValueBudget D H S < ∑ p ∈ I, Real.log (p : ℝ) →
          MvPolynomial.eval ![x,y] Q = 0 := by
  classical
  obtain ⟨Q,H,hQ,hD,hH,hcoeff,hline,hlog⟩ :=
    exists_small_line_polynomial P (fun p hp => (hP p hp).pos) T a D
  refine ⟨Q,H,hQ,hD,hH,hcoeff,hline,hlog,?_⟩
  intro S x y hx hy I hIP hinc hlarge
  unfold LineIncidence at hinc
  choose s hs using hinc
  apply value_zero_of_log_prime_budget Q D H hD hcoeff hH S x y hx hy I
    (fun p hp => hP p (hIP hp))
    (fun p : I => a ⟨p.val,hIP p.property⟩) (fun p : I => (s p).val)
  · exact fun p => hline ⟨p.val,hIP p.property⟩ (s p)
  · exact hs
  · exact hlarge

theorem logarithmicCost_le_budget (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (T : ∀ p : P, Finset (ZMod p.val)) (K : P → ℝ)
    (hK : ∀ p : P, ((T p).card : ℝ) ≤ K p) :
    logarithmicCost P T ≤ ∑ p : P, K p*Real.log (p.val : ℝ) := by
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_right (hK p)
  apply Real.log_nonneg
  exact_mod_cast Nat.succ_le_of_lt (hP p p.property)

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI

import OAI.Analysis.Laughlin.Pair.Spectators

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

noncomputable def spinOrbitalPolynomial {N : ℕ} (Q : ℕ) (i : Fin N) (x : Fin (Q+1)) :
    MvPolynomial (SpinorVariables N) ℂ :=
  C (Real.sqrt (Nat.choose Q x.val : ℝ) : ℂ) *
    (X (i,false)^(Q-x.val)*X (i,true)^x.val)

theorem spinPolynomial_expansion {N Q : ℕ} (ψ : State N Q) :
    spinPolynomial ψ = ∑ a, C (ψ a) * ∏ k, spinOrbitalPolynomial Q k (a k) := by
  classical
  unfold spinPolynomial
  apply Finset.sum_congr rfl
  intro a ha
  rw [monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  have he (k : Fin N) : (∏ b : Bool, X (k,b)^monomialExponent a (k,b)) =
      (X (k,false)^(Q-(a k).val)*X (k,true)^(a k).val : MvPolynomial _ ℂ) := by
    simp [monomialExponent, mul_comm]
  simp_rw [he]
  simp only [spinOrbitalPolynomial, Finset.prod_mul_distrib, ← map_prod, map_mul]
  have hw : spinWeight a = ∏ k : Fin N,
      (Real.sqrt (Nat.choose Q (a k).val : ℝ) : ℂ) := by
    simp [spinWeight]
  rw [hw]
  ring

theorem prod_pair_split {N : ℕ} {R : Type*} [CommMonoid R]
    (i j : Fin N) (hij : i ≠ j) (f : Fin N → R) :
    (∏ k, f k) = (∏ k ∈ (Finset.univ.erase i).erase j, f k) * f i * f j := by
  classical
  have hj : j ∈ Finset.univ.erase i := by simp [Ne.symm hij]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ _ hj]
  ac_rfl

noncomputable def spectatorPolynomial {N Q : ℕ} (i j : Fin N) (a : Configuration N Q) :
    MvPolynomial (SpinorVariables N) ℂ :=
  ∏ k ∈ (Finset.univ.erase i).erase j, spinOrbitalPolynomial Q k (a k)

theorem spinOrbital_update_product {N Q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (a : Configuration N Q) (x y : Fin (Q+1)) :
    (∏ k, spinOrbitalPolynomial Q k ((Function.update (Function.update a i x) j y) k)) =
      spectatorPolynomial i j a * spinOrbitalPolynomial Q i x * spinOrbitalPolynomial Q j y := by
  rw [prod_pair_split i j hij]
  simp only [Function.update_self, Function.update_of_ne hij]
  congr 2
  apply Finset.prod_congr rfl
  intro k hk
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  simp [Function.update_of_ne, hki,hkj]

end Laughlin

end OAI

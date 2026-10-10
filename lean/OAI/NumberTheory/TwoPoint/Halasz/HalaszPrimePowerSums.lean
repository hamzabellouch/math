import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePowerRoots
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

namespace OAI

/-! Newton identities over the prime-power ring. The small integers in
the identities are units when the prime exceeds the number of variables. -/
namespace TwoPointCorrelations

open Finset MvPolynomial

lemma halasz_unit_power_sums_esymm {R : Type*} [CommRing R] {s : ℕ}
    (x y : Fin s → R)
    (hu : ∀ j : ℕ, 1≤j → j≤s → IsUnit (j:R))
    (hp : ∀ j : ℕ, 1≤j → j≤s → ∑ i, x i^j=∑ i, y i^j) :
    ∀ k : ℕ, k≤s → eval x (esymm (Fin s) R k)=eval y (esymm (Fin s) R k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hks
    by_cases hk : k=0
    · subst k
      simp
    have he (a : ℕ × ℕ) (ha : a∈(antidiagonal k).filter (fun a => a.1<k)) :
        eval x ((-1: MvPolynomial (Fin s) R)^a.1 * esymm (Fin s) R a.1 * psum (Fin s) R a.2) =
          eval y ((-1: MvPolynomial (Fin s) R)^a.1 * esymm (Fin s) R a.1 * psum (Fin s) R a.2) := by
      obtain ⟨ha,hak⟩ := mem_filter.mp ha
      have hab : a.1+a.2=k := mem_antidiagonal.mp ha
      have hj := hp a.2 (by omega) (by omega)
      have hi := ih a.1 hak (by omega)
      simp only [map_mul,map_pow,map_neg,map_one]
      rw [hi]
      have hs : eval x (psum (Fin s) R a.2)=eval y (psum (Fin s) R a.2) := by
        simpa [psum] using hj
      rw [hs]
    have hsum := sum_congr rfl he
    have hx := congrArg (eval x) (mul_esymm_eq_sum (Fin s) R k)
    have hy := congrArg (eval y) (mul_esymm_eq_sum (Fin s) R k)
    simp only [map_mul,map_natCast,map_pow,map_neg,map_one,map_sum] at hx hy
    apply (hu k (by omega) hks).mul_right_inj.mp
    rw [hx,hy]
    simpa only [map_mul,map_pow,map_neg,map_one] using
      congrArg (fun z : R => (-1:R)^(k+1)*z) hsum

theorem halasz_unit_power_sums_product {R : Type*} [CommRing R] {s : ℕ}
    (x y : Fin s → R)
    (hu : ∀ j : ℕ, 1≤j → j≤s → IsUnit (j:R))
    (hp : ∀ j : ℕ, 1≤j → j≤s → ∑ i, x i^j=∑ i, y i^j) :
    (∏ i, (Polynomial.X-Polynomial.C (x i))) =
      ∏ i, (Polynomial.X-Polynomial.C (y i)) := by
  classical
  let a : Multiset R := univ.val.map x
  let b : Multiset R := univ.val.map y
  have ha : a.card=s := by simp [a]
  have hb : b.card=s := by simp [b]
  have he : ∀ k : ℕ, a.esymm k=b.esymm k := by
    intro k
    by_cases hk : k≤s
    · have hx := aeval_esymm_eq_multiset_esymm (Fin s) R k x
      have hy := aeval_esymm_eq_multiset_esymm (Fin s) R k y
      rw [aeval_eq_eval] at hx hy
      exact hx.symm.trans ((halasz_unit_power_sums_esymm x y hu hp k hk).trans hy)
    · rw [Multiset.esymm_of_card_lt (by omega : a.card<k),
        Multiset.esymm_of_card_lt (by omega : b.card<k)]
  have hprod : (a.map (fun t => Polynomial.X-Polynomial.C t)).prod =
      (b.map (fun t => Polynomial.X-Polynomial.C t)).prod := by
    rw [Multiset.prod_X_sub_X_eq_sum_esymm,Multiset.prod_X_sub_X_eq_sum_esymm,ha,hb]
    apply sum_congr rfl
    intro k _
    rw [he k]
  simpa only [a,b,Multiset.map_map,Function.comp_def,Finset.prod_eq_multiset_prod] using hprod

theorem halasz_prime_power_power_sums_product {p r k : ℕ} [Fact p.Prime]
    (hkp : k<p) (x y : Fin k → ZMod (p^(r+1)))
    (hp : ∀ j : ℕ, 1≤j → j≤k → ∑ i, x i^j=∑ i, y i^j) :
    (∏ i, (Polynomial.X-Polynomial.C (x i))) =
      ∏ i, (Polynomial.X-Polynomial.C (y i)) := by
  apply halasz_unit_power_sums_product x y _ hp
  intro j hj hjk
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) (by omega)).mpr
  exact Nat.not_dvd_of_pos_of_lt hj (hjk.trans_lt hkp)

theorem halasz_prime_power_solution_mem {p r k : ℕ} [Fact p.Prime]
    (hkp : k<p) (x y : Fin k → ZMod (p^(r+1)))
    (hx : Function.Injective (fun i => halaszPrimePowerReduction p r (x i)))
    (hp : ∀ j : ℕ, 1≤j → j≤k → ∑ i, x i^j=∑ i, y i^j) (i : Fin k) :
    ∃ j, y i=x j := by
  have hpoly := halasz_prime_power_power_sums_product hkp x y hp
  have he := congrArg (Polynomial.eval (y i)) hpoly
  simp only [Polynomial.eval_prod,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] at he
  have hy : ∏ j, (y i-y j)=0 := prod_eq_zero (mem_univ i) (sub_self _)
  exact halasz_prime_power_split_roots x hx (y i) (he.trans hy)

/-- A sufficient nonsingular congruence bound for the mean-value iteration.
The factor k^k is deliberately used in place of the sharper k!. -/
theorem halasz_prime_power_solution_count {p r k : ℕ} [Fact p.Prime]
    (hkp : k<p) (x : Fin k → ZMod (p^(r+1)))
    (hx : Function.Injective (fun i => halaszPrimePowerReduction p r (x i)))
    (F : Finset (Fin k → ZMod (p^(r+1))))
    (hF : ∀ y∈F, ∀ j : ℕ, 1≤j → j≤k → ∑ i, x i^j=∑ i, y i^j) :
    F.card ≤ k^k := by
  classical
  let S : Finset (ZMod (p^(r+1))) := univ.image x
  have hs : S.card≤k := (card_image_le).trans_eq (card_fin k)
  have hsub : F ⊆ Fintype.piFinset (fun _ : Fin k => S) := by
    intro y hy
    apply Fintype.mem_piFinset.mpr
    intro i
    obtain ⟨j,hj⟩ := halasz_prime_power_solution_mem hkp x y hx (hF y hy) i
    exact mem_image.mpr ⟨j,mem_univ _,hj.symm⟩
  calc
    F.card ≤ (Fintype.piFinset (fun _ : Fin k => S)).card := card_le_card hsub
    _ = S.card^k := by simp
    _ ≤ k^k := Nat.pow_le_pow_left hs k

end TwoPointCorrelations

end OAI

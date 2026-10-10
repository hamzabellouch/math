import Mathlib

namespace OAI

/-! Monic remainders, sparse coefficient support and weighted polynomial identities. -/

namespace DeterministicThreeSum
namespace Sparse
open scoped BigOperators
open Finset Polynomial
variable (R : Type*) [CommRing R]

noncomputable def gridPolynomial (n : ℕ) : R[X] :=
  ∏ i : Fin n, (X - C (i.val : R))

lemma gridPolynomial_monic (n : ℕ) : (gridPolynomial R n).Monic := by
  apply monic_prod_of_monic
  intro i hi
  exact monic_X_sub_C _

lemma gridPolynomial_eval (n : ℕ) (i : Fin n) :
    (gridPolynomial R n).eval (i.val : R) = 0 := by
  rw [gridPolynomial, eval_prod]
  apply prod_eq_zero (mem_univ i)
  simp

lemma gridPolynomial_natDegree [Nontrivial R] (n : ℕ) :
    (gridPolynomial R n).natDegree = n := by
  rw [gridPolynomial, natDegree_prod_of_monic]
  · simp only [natDegree_X_sub_C, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  · intro i hi
    exact monic_X_sub_C _

noncomputable def remainderPower (n j : ℕ) : R[X] :=
  X ^ j %ₘ gridPolynomial R n

lemma remainderPower_eval (n j : ℕ) (i : Fin n) :
    (remainderPower R n j).eval (i.val : R) = (i.val : R) ^ j := by
  rw [remainderPower]
  have h := eval₂_modByMonic_eq_self_of_root
    (p := (X : R[X]) ^ j) (f := RingHom.id R) (by simpa using gridPolynomial_eval R n i)
  simpa using h

lemma remainderPower_degree_le (n j : ℕ) :
    (remainderPower R n j).natDegree ≤ j := by
  calc
    _ ≤ ((X : R[X]) ^ j).natDegree := natDegree_modByMonic_le_left
    _ ≤ j := natDegree_X_pow_le j

lemma remainderPower_degree_lt [Nontrivial R] {n : ℕ} (hn : 0 < n) (j : ℕ) :
    (remainderPower R n j).natDegree < n := by
  have hne : gridPolynomial R n ≠ 1 := by
    intro h
    have hh := congrArg Polynomial.natDegree h
    rw [gridPolynomial_natDegree, natDegree_one] at hh
    omega
  have h := natDegree_modByMonic_lt ((X : R[X]) ^ j) (gridPolynomial_monic R n) hne
  rwa [gridPolynomial_natDegree] at h

lemma remainderPower_coeff_zero_of_ge [Nontrivial R] {n j k : ℕ} (hn : 0 < n)
    (hk : n ≤ k) : (remainderPower R n j).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt ((remainderPower_degree_lt R hn j).trans_le hk)

lemma remainderPower_coeff_zero_of_gt {n j k : ℕ} (hk : j < k) :
    (remainderPower R n j).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt ((remainderPower_degree_le R n j).trans_lt hk)

lemma remainderPower_sum [Nontrivial R] {n : ℕ} (hn : 0 < n) (j : ℕ) (x : Fin n) :
    ∑ k : Fin n, (remainderPower R n j).coeff k.val * (x.val : R) ^ k.val =
      (x.val : R) ^ j := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (remainderPower R n j).coeff k * (x.val : R) ^ k)]
  rw [← eval_eq_sum_range' (remainderPower_degree_lt R hn j)]
  exact remainderPower_eval R n j x

noncomputable def localCoefficient (m b v i j : ℕ) : R :=
  ∑ r ∈ range (v + 1), (v.choose r : R) *
    (remainderPower R m r).coeff i * (remainderPower R b (v - r)).coeff j

lemma localCoefficient_zero {m b v i j : ℕ} (h : v < i + j) :
    localCoefficient R m b v i j = 0 := by
  apply sum_eq_zero
  intro r hr
  have hrle : r ≤ v := by have := mem_range.mp hr; omega
  by_cases hri : r < i
  · rw [remainderPower_coeff_zero_of_gt R hri]
    ring
  · have hrj : v - r < j := by omega
    rw [remainderPower_coeff_zero_of_gt R hrj]
    ring

lemma localCoefficient_eval [Nontrivial R] {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (v : ℕ) (x : Fin m) (y : Fin b) :
    ∑ i : Fin m, ∑ j : Fin b,
      localCoefficient R m b v i.val j.val * (x.val : R) ^ i.val * (y.val : R) ^ j.val =
        ((x.val : R) + (y.val : R)) ^ v := by
  simp only [localCoefficient, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := univ) (t := range (v + 1))]
  calc
    _ = ∑ r ∈ range (v + 1), (v.choose r : R) *
        (∑ i : Fin m, (remainderPower R m r).coeff i.val * (x.val : R) ^ i.val) *
        (∑ j : Fin b, (remainderPower R b (v - r)).coeff j.val * (y.val : R) ^ j.val) := by
      apply sum_congr rfl
      intro r hr
      simp only [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ring
    _ = ∑ r ∈ range (v + 1), (v.choose r : R) * (x.val : R) ^ r * (y.val : R) ^ (v - r) := by
      simp only [remainderPower_sum R hm, remainderPower_sum R hb]
    _ = _ := by
      rw [add_pow]
      apply sum_congr rfl
      intro r hr
      ring

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

noncomputable def coefficient (m b : ℕ) (P : MvPolynomial σ R)
    (i : σ → Fin m) (j : σ → Fin b) : R :=
  ∑ v ∈ P.support, P.coeff v * ∏ k, localCoefficient R m b (v k) (i k).val (j k).val

lemma monomial_expansion [Nontrivial R] {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (v : σ → ℕ) (x : σ → Fin m) (y : σ → Fin b) :
    ∑ i : σ → Fin m, ∑ j : σ → Fin b,
      (∏ k, localCoefficient R m b (v k) (i k).val (j k).val) *
        (∏ k, ((x k).val : R) ^ (i k).val) *
        (∏ k, ((y k).val : R) ^ (j k).val) =
      ∏ k, (((x k).val : R) + ((y k).val : R)) ^ (v k) := by
  have h := congrArg (fun g : σ → R => ∏ k, g k)
    (funext fun k => localCoefficient_eval R hm hb (v k) (x k) (y k))
  simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib] at h
  exact h

theorem coefficient_evaluation [Nontrivial R] {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    (P : MvPolynomial σ R) (x : σ → Fin m) (y : σ → Fin b) :
    MvPolynomial.eval (fun k => ((x k).val : R) + ((y k).val : R)) P =
      ∑ i : σ → Fin m, ∑ j : σ → Fin b,
        coefficient R m b P i j * (∏ k, ((x k).val : R) ^ (i k).val) *
          (∏ k, ((y k).val : R) ^ (j k).val) := by
  rw [MvPolynomial.eval_eq']
  simp only [coefficient, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := univ) (t := P.support)]
  apply sum_congr rfl
  intro v hv
  rw [← monomial_expansion R hm hb v x y]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  ring

omit [DecidableEq σ] in
lemma coefficient_support {m b Δ : ℕ} (P : MvPolynomial σ R) (hP : P.totalDegree ≤ Δ)
    (i : σ → Fin m) (j : σ → Fin b)
    (hij : Δ < (∑ k, (i k).val) + ∑ k, (j k).val) :
    coefficient R m b P i j = 0 := by
  apply sum_eq_zero
  intro v hv
  have hdeg : ∑ k, v k ≤ Δ := by
    have h := (MvPolynomial.le_totalDegree hv).trans hP
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h
    exact h
  have hex : ∃ k, v k < (i k).val + (j k).val := by
    by_contra! h
    have hs := sum_le_sum (fun k (_ : k ∈ (univ : Finset σ)) => h k)
    rw [sum_add_distrib] at hs
    omega
  obtain ⟨k, hk⟩ := hex
  rw [prod_eq_zero (mem_univ k) (localCoefficient_zero R hk)]
  exact mul_zero _

end Sparse
end DeterministicThreeSum
namespace DeterministicThreeSum.Weighted
open Finset
open scoped BigOperators
noncomputable section
variable {R : Type} [CommRing R]

lemma split_support {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (small : Finset I) (low : Finset J) (A : I → J → R)
    (hA : ∀ i ∉ small, ∀ j ∉ low, A i j = 0) (X : I → R) (Y : J → R) :
    (∑ i, ∑ j, A i j * X i * Y j) =
      (∑ j ∈ low, (∑ i, A i j * X i) * Y j) +
      ∑ i ∈ small, X i * ∑ j ∈ lowᶜ, A i j * Y j := by
  have hs : (∑ i, ∑ j ∈ lowᶜ, A i j * X i * Y j) =
      ∑ i ∈ small, X i * ∑ j ∈ lowᶜ, A i j * Y j := by
    calc
      _ = ∑ i, X i * ∑ j ∈ lowᶜ, A i j * Y j := by
        apply sum_congr rfl
        intro i hi
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        ring
      _ = _ := (sum_subset (subset_univ small) (by
        intro i hi hni
        have hz : (∑ j ∈ lowᶜ, A i j * Y j) = 0 := by
          apply sum_eq_zero
          intro j hj
          rw [hA i hni j (mem_compl.mp hj), zero_mul]
        rw [hz,mul_zero])).symm
  calc
    _ = ∑ i, ((∑ j ∈ low, A i j * X i * Y j) +
        ∑ j ∈ lowᶜ, A i j * X i * Y j) := by
      apply sum_congr rfl
      intro i hi
      exact (sum_add_sum_compl low _).symm
    _ = (∑ i, ∑ j ∈ low, A i j * X i * Y j) +
        ∑ i, ∑ j ∈ lowᶜ, A i j * X i * Y j := sum_add_distrib
    _ = _ := by rw [hs, sum_comm]; simp only [sum_mul]

lemma weighted_finite_interchange {A J : Type} (members : Finset A) (low : Finset J)
    (z : A → R) (F : A → J → R) (Y : J → R) :
    (∑ a ∈ members, z a * ∑ j ∈ low, F a j * Y j) =
      ∑ j ∈ low, (∑ a ∈ members, z a * F a j) * Y j := by
  calc
    _ = ∑ a ∈ members, ∑ j ∈ low, z a * (F a j * Y j) := by
      apply sum_congr rfl
      intro a ha
      exact mul_sum _ _ _
    _ = ∑ j ∈ low, ∑ a ∈ members, z a * (F a j * Y j) := sum_comm
    _ = _ := by simp only [sum_mul, mul_assoc]

lemma weighted_split {I J A : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (small : Finset I) (low : Finset J)
    (C : I → J → R) (hC : ∀ i ∉ small, ∀ j ∉ low, C i j = 0)
    (members : Finset A) (z : A → R) (X : A → I → R) (Y : J → R) :
    (∑ a ∈ members, z a * ∑ i, ∑ j, C i j * X a i * Y j) =
      (∑ j ∈ low, (∑ a ∈ members, z a * ∑ i, C i j * X a i) * Y j) +
      ∑ i ∈ small, (∑ a ∈ members, z a * X a i) *
        (∑ j ∈ lowᶜ, C i j * Y j) := by
  simp_rw [split_support small low C hC, mul_add]
  rw [sum_add_distrib]
  congr 1
  · exact weighted_finite_interchange members low z (fun a j => ∑ i, C i j * X a i) Y
  · exact weighted_finite_interchange members small z X (fun i => ∑ j ∈ lowᶜ, C i j * Y j)

def degree {d s : ℕ} (i : Fin d → Fin s) : ℕ := ∑ k, (i k).val
noncomputable def lowSet (b d : ℕ) : Finset (Fin d → Fin b) :=
  univ.filter (fun j => 2*degree j ≤ (b-3)*d)
noncomputable def smallSet (m d : ℕ) : Finset (Fin d → Fin m) :=
  univ.filter (fun i => degree i ≤ 3*d)
def cutoff (b d : ℕ) : ℕ := ((b+3)*d)/2

def monomial {d s : ℕ} (x i : Fin d → Fin s) : R :=
  ∏ k, ((x k).val : R)^(i k).val

lemma source_support {d m b : ℕ} (hb : 3 ≤ b)
    (P : MvPolynomial (Fin d) R) (hP : P.totalDegree ≤ cutoff b d)
    (i : Fin d → Fin m) (hi : i ∉ smallSet m d)
    (j : Fin d → Fin b) (hj : j ∉ lowSet b d) :
    Sparse.coefficient R m b P i j = 0 := by
  have hi' : 3*d < degree i := by simpa [smallSet] using hi
  have hj' : (b-3)*d < 2*degree j := by simpa [lowSet] using hj
  apply Sparse.coefficient_support R P hP i j
  have heq : (b+3)*d = (b-3)*d+6*d := by
    rw [show b+3 = (b-3)+6 by omega, add_mul]
  have hdiv : 2*cutoff b d ≤ (b+3)*d := Nat.mul_div_le _ _
  change cutoff b d < degree i + degree j
  omega

variable {d m b : ℕ}
noncomputable def U (P : MvPolynomial (Fin d) R) (j : Fin d → Fin b)
    (x : Fin d → Fin m) : R :=
  ∑ i, Sparse.coefficient R m b P i j * monomial x i
noncomputable def W (P : MvPolynomial (Fin d) R) (i : Fin d → Fin m)
    (y : Fin d → Fin b) : R :=
  ∑ j ∈ (lowSet b d)ᶜ, Sparse.coefficient R m b P i j * monomial y j

theorem polynomial_group_identity [Nontrivial R] (hm : 0 < m) (hb : 3 ≤ b)
    (P : MvPolynomial (Fin d) R) (hP : P.totalDegree ≤ cutoff b d)
    {A : Type} (members : Finset A) (x : A → Fin d → Fin m)
    (y : Fin d → Fin b) (z : A → R) :
    (∑ a ∈ members, z a * MvPolynomial.eval
      (fun k => ((x a k).val : R) + ((y k).val : R)) P) =
      (∑ j ∈ lowSet b d, (∑ a ∈ members, z a * U P j (x a)) * monomial y j) +
      ∑ i ∈ smallSet m d, (∑ a ∈ members, z a * monomial (x a) i) * W P i y := by
  simp_rw [Sparse.coefficient_evaluation R hm (show 0 < b by omega)]
  exact weighted_split (smallSet m d) (lowSet b d) (Sparse.coefficient R m b P)
    (fun i hi j hj => source_support hb P hP i hi j hj) members z
    (fun a i => monomial (x a) i) (fun j => monomial y j)

end
end DeterministicThreeSum.Weighted

end OAI

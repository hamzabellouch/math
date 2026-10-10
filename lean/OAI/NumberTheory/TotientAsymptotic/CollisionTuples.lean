import OAI.NumberTheory.TotientAsymptotic.SuffixFactorization
import OAI.NumberTheory.TotientAsymptotic.CollisionAlgebra

namespace OAI

/-! Actual tuples, their basic witnesses, and the first differing prime. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

structure TotientTuple (R : ℕ) where
  head : ℕ
  tail : PrefixDatum R

def tuplePrimes {R : ℕ} (τ : TotientTuple R) : Fin (R+1) → ℕ :=
  Fin.cons τ.head τ.tail.primes

def tupleValue {R : ℕ} (τ : TotientTuple R) : ℕ :=
  τ.tail.d*∏ i, (tuplePrimes τ i-1)

def IsBasicTuple (x : ℝ) (H : ℕ) (t : ℝ) (τ : TotientTuple (R x H)) : Prop :=
  τ.head.Prime ∧ x^(9/10 : ℝ) ≤ τ.head ∧ IsPrefixDatum x H τ.tail ∧ (tupleValue τ : ℝ) ≤ t

lemma basic_prefix_data_positive {x : ℝ} {H : ℕ} {ζ : PrefixDatum (R x H)}
    (hPH : P H ≤ H) (hζ : IsPrefixDatum x H ζ) :
    0 < ζ.d ∧ ∀ i, (ζ.primes i).Prime := by
  obtain ⟨η, hη, hd, hp⟩ := hζ
  constructor
  · rw [← hd]
    exact Nat.totient_pos.mpr (suffixPreimage_pos (i := R x H) hη)
  · intro i
    rw [hp i]
    apply (hη.2.1 _ _).1
    have hi := i.isLt
    apply Finset.mem_Icc.mpr
    unfold R L at *
    omega

lemma basic_tuple_primes {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) :
    ∀ i, (tuplePrimes τ i).Prime := by
  intro i
  refine Fin.cases hτ.1 (fun j => ?_) i
  exact (basic_prefix_data_positive hPH hτ.2.2.1).2 j

lemma basic_tuple_value_pos {x t : ℝ} {H : ℕ} {τ : TotientTuple (R x H)}
    (hPH : P H ≤ H) (hτ : IsBasicTuple x H t τ) : 0 < tupleValue τ := by
  apply Nat.mul_pos (basic_prefix_data_positive hPH hτ.2.2.1).1
  exact Finset.prod_pos (fun i _ => Nat.sub_pos_of_lt (basic_tuple_primes hPH hτ i).one_lt)

lemma tuple_eq_of_value_and_primes {R : ℕ} {τ σ : TotientTuple R}
    (hp : ∀ i, 2 ≤ tuplePrimes τ i) (hv : tupleValue τ = tupleValue σ)
    (he : tuplePrimes τ = tuplePrimes σ) : τ = σ := by
  have hprod : 0 < ∏ i, (tuplePrimes τ i-1) :=
    Finset.prod_pos (fun i _ => by have := hp i; omega)
  have hd : τ.tail.d = σ.tail.d := by
    unfold tupleValue at hv
    rw [← he] at hv
    exact Nat.eq_of_mul_eq_mul_right hprod hv
  have hh : τ.head = σ.head := by
    simpa only [tuplePrimes, Fin.cons_zero] using congrFun he 0
  have ht : τ.tail.primes = σ.tail.primes := by
    funext j
    simpa only [tuplePrimes, Fin.cons_succ] using congrFun he j.succ
  cases τ with
  | mk th tt =>
    cases σ with
    | mk sh st =>
      cases tt
      cases st
      simp_all

lemma basic_collision_first_difference {x t : ℝ} {H : ℕ}
    {τ σ : TotientTuple (R x H)} (hPH : P H ≤ H)
    (hτ : IsBasicTuple x H t τ) (hv : tupleValue τ = tupleValue σ) (hne : τ ≠ σ) :
    ∃ i : Fin (R x H+1), tuplePrimes τ i ≠ tuplePrimes σ i ∧
      ∀ j, j < i → tuplePrimes τ j = tuplePrimes σ j := by
  classical
  have hex : ∃ i, tuplePrimes τ i ≠ tuplePrimes σ i := by
    by_contra! he
    exact hne (tuple_eq_of_value_and_primes
      (fun i => (basic_tuple_primes hPH hτ i).two_le) hv (funext he))
  obtain ⟨i, hi, hmin⟩ := (Finset.univ.filter (fun i => tuplePrimes τ i ≠ tuplePrimes σ i)).exists_min_image
    (fun i => i.val) (by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, by simpa using hi⟩)
  refine ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
  intro j hji
  by_contra hj
  have hmem : j ∈ Finset.univ.filter (fun i => tuplePrimes τ i ≠ tuplePrimes σ i) := by simp [hj]
  have := hmin j hmem
  exact (not_le_of_gt hji) (by exact_mod_cast this)

/-- The common displayed prefix cancels before the comparison estimate is
applied. The remaining product still contains the true tail totient. -/
lemma tuple_collision_suffix_identity {R : ℕ} {τ σ : TotientTuple R}
    (hp : ∀ i, 2 ≤ tuplePrimes τ i) (hv : tupleValue τ = tupleValue σ)
    (i : Fin (R+1)) (hcommon : ∀ j, j < i → tuplePrimes τ j = tuplePrimes σ j) :
    τ.tail.d*(∏ j ∈ Finset.Ici i, (tuplePrimes τ j-1)) =
      σ.tail.d*(∏ j ∈ Finset.Ici i, (tuplePrimes σ j-1)) := by
  have hsplit (p : Fin (R+1) → ℕ) : (∏ j, (p j-1)) =
      (∏ j ∈ Finset.Iio i, (p j-1))*(∏ j ∈ Finset.Ici i, (p j-1)) := by
    have hpart : Finset.Iio i ∪ Finset.Ici i = Finset.univ := by
      ext j
      simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici, Finset.mem_univ]
      exact iff_true_intro (lt_or_ge j i)
    have hdis : Disjoint (Finset.Iio i) (Finset.Ici i) := by
      apply Finset.disjoint_left.mpr
      intro j hj hk
      exact (not_lt_of_ge (Finset.mem_Ici.mp hk)) (Finset.mem_Iio.mp hj)
    rw [← hpart, Finset.prod_union hdis]
  have he : (∏ j ∈ Finset.Iio i, (tuplePrimes τ j-1)) =
      ∏ j ∈ Finset.Iio i, (tuplePrimes σ j-1) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hcommon j (Finset.mem_Iio.mp hj)]
  have hpos : 0 < ∏ j ∈ Finset.Iio i, (tuplePrimes τ j-1) :=
    Finset.prod_pos (fun j _ => by have := hp j; omega)
  unfold tupleValue at hv
  rw [hsplit, hsplit, ← he] at hv
  apply Nat.eq_of_mul_eq_mul_left hpos
  nlinarith [hv]

end TotientAsymptotic

end

end OAI

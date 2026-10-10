import Lean
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Operations

namespace OAI

/-!
# Two-generator ideal powers, monomial membership, and polynomial jet ideals
-/

section

/-!
# Finite jet-row indices and their cardinality
-/

namespace Nagata.Workers.W30

open scoped BigOperators

/-- A dependent finite type encoding the manuscript's row set without duplicates.
The sigma order is `(b,ell)`; `jetIndexPair` restores the manuscript order. -/
abbrev JetIndex (q m : ℕ) := Σ b : Fin m, Fin (q * (m - b.val))

def jetIndexPair {q m : ℕ} (x : JetIndex q m) : ℕ × ℕ :=
  (x.2.val, x.1.val)

@[simp] theorem jetIndexPair_bounds {q m : ℕ} (x : JetIndex q m) :
    (jetIndexPair x).2 < m ∧ (jetIndexPair x).1 < q * (m - (jetIndexPair x).2) :=
  ⟨x.1.isLt, x.2.isLt⟩

/-- Explicit equivalence with the subset of natural-number pairs written in §03. -/
def jetIndexEquivPairs (q m : ℕ) :
    JetIndex q m ≃ {p : ℕ × ℕ // p.2 < m ∧ p.1 < q * (m - p.2)} where
  toFun x := ⟨jetIndexPair x, jetIndexPair_bounds x⟩
  invFun x := ⟨⟨x.1.2, x.2.1⟩, ⟨x.1.1, x.2.2⟩⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

/-- The row count as the sum of the widths of its `m` horizontal slices. -/
theorem card_jetIndex_sum (q m : ℕ) :
    Fintype.card (JetIndex q m) = ∑ b ∈ Finset.range m, q * (m - b) := by
  simp only [JetIndex, Fintype.card_sigma, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun b => q * (m - b)) m

private theorem row_sum_succ (q m : ℕ) :
    (∑ b ∈ Finset.range (m + 1), q * (m + 1 - b)) =
      (∑ b ∈ Finset.range m, q * (m - b)) + q * (m + 1) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero]

/-- An integral form of the cardinality formula, avoiding division. -/
theorem card_jetIndex_mul_two (q m : ℕ) :
    Fintype.card (JetIndex q m) * 2 = q * m * (m + 1) := by
  rw [card_jetIndex_sum]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [row_sum_succ, Nat.add_mul, ih]
    simp only [Nat.add_mul, Nat.mul_succ]
    omega

/-- The exact cardinality stated after the collision lemma. -/
theorem card_jetIndex (q m : ℕ) :
    Fintype.card (JetIndex q m) = q * m * (m + 1) / 2 := by
  rw [← card_jetIndex_mul_two q m, Nat.mul_div_cancel]
  decide

end Nagata.Workers.W30

end

section

/-!
# Membership in a monomial ideal
-/

namespace Nagata.Workers.W30

open MvPolynomial
open scoped Pointwise

variable {σ R : Type*} [CommRing R]

/-- A polynomial lies in a monomial ideal iff each support exponent dominates
one of the generating exponents. -/
theorem mem_monomial_span_iff {p : MvPolynomial σ R} {s : Set (σ →₀ ℕ)} :
    p ∈ Ideal.span ((fun a => monomial a (1 : R)) '' s) ↔
      ∀ a ∈ p.support, ∃ g ∈ s, g ≤ a := by
  classical
  let J : Ideal (MvPolynomial σ R) :=
    { carrier := {f | ∀ a ∈ f.support, ∃ g ∈ s, g ≤ a}
      add_mem' {x y} hx hy a ha :=
        (Finset.mem_union.mp (Finsupp.support_add ha)).elim (hx a) (hy a)
      zero_mem' := by simp
      smul_mem' x y hy a ha := by
        change a ∈ (x*y).support at ha
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul x y ha)
        obtain ⟨g,hg,hgv⟩ := hy v hv
        exact ⟨g,hg,hgv.trans (le_add_of_nonneg_left zero_le)⟩ }
  change _ ↔ p ∈ J
  constructor
  · suffices Ideal.span ((fun a => monomial a (1 : R)) '' s) ≤ J from @this p
    rw [Ideal.span_le]
    rintro _ ⟨g,hg,rfl⟩ a ha
    have heq : a = g := Finset.mem_singleton.mp (support_monomial_subset ha)
    exact ⟨g,hg,heq ▸ le_rfl⟩
  · intro hp
    rw [p.as_sum]
    apply Submodule.sum_mem _
    intro a ha
    obtain ⟨g,hg,hga⟩ := hp a ha
    obtain ⟨c,hc⟩ := le_iff_exists_add.mp hga
    have hgen : monomial g (1:R) ∈ Ideal.span ((fun a => monomial a (1:R)) '' s) :=
      Ideal.subset_span ⟨g,hg,rfl⟩
    have hprod := Ideal.mul_mem_left _ (monomial c (p.coeff a)) hgen
    simpa [monomial_mul_monomial, hc, add_comm] using hprod

end Nagata.Workers.W30

end

section

/-!
# The monomial exponent arithmetic behind `(x^q,y)^m`
-/

namespace Nagata.Workers.W30

/-- An exponent pair divisible by one of the listed monomial generators. -/
def GeneratorDivides (q m ell b : Nat) : Prop :=
  ∃ k : Nat, k ≤ m ∧ q * (m - k) ≤ ell ∧ k ≤ b

/-- A generator divides precisely when the exponent escapes the finite jet region. -/
theorem generatorDivides_iff {q m ell b : Nat} :
    GeneratorDivides q m ell b ↔ m ≤ b ∨ q * (m - b) ≤ ell := by
  constructor
  · rintro ⟨k, hkm, hell, hkb⟩
    right
    have hsub : m - b ≤ m - k := by omega
    exact Nat.le_trans (Nat.mul_le_mul_left q hsub) hell
  · rintro (hmb | hell)
    · exact ⟨m, Nat.le_refl m, by simp, hmb⟩
    · by_cases hbm : b ≤ m
      · exact ⟨b, hbm, hell, Nat.le_refl b⟩
      · exact ⟨m, Nat.le_refl m, by simp, by omega⟩

/-- The complement of the monomial-generator divisibility region is exactly
`I={(ell,b):b<m,ell<q*(m-b)}` from the manuscript. -/
theorem not_generatorDivides_iff {q m ell b : Nat} :
    ¬ GeneratorDivides q m ell b ↔ b < m ∧ ell < q * (m - b) := by
  rw [generatorDivides_iff]
  omega

/-- The divisibility region is closed under multiplication by any monomial,
expressed as addition of nonnegative exponents. -/
theorem GeneratorDivides.add {q m ell b c d : Nat}
    (h : GeneratorDivides q m ell b) : GeneratorDivides q m (ell + c) (b + d) := by
  rcases h with ⟨k, hkm, hell, hkb⟩
  exact ⟨k, hkm, by omega, by omega⟩

end Nagata.Workers.W30

end

section

/-! An explicit generator formula for a power of a two-generated ideal. -/

namespace Nagata.Workers.W30

open scoped Pointwise

variable {A : Type*} [CommRing A]

/-- The products of `m` choices from `{x,y}` are precisely `x^(m-k)*y^k`. -/
theorem pair_set_pow (x y : A) (m : ℕ) :
    ({x,y} : Set A) ^ m = {z | ∃ k ≤ m, z = x ^ (m - k) * y ^ k} := by
  induction m with
  | zero =>
    ext z
    simp
  | succ m ih =>
    rw [pow_succ, ih]
    ext z
    simp only [Set.mem_mul, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, ⟨k, hk, rfl⟩, c, hc, rfl⟩
      rcases hc with rfl | rfl
      · refine ⟨k, by omega, ?_⟩
        have hsub : m + 1 - k = (m - k) + 1 := by omega
        rw [hsub, pow_succ]
        ac_rfl
      · refine ⟨k + 1, by omega, ?_⟩
        rw [Nat.add_sub_add_right, pow_succ]
        ac_rfl
    · rintro ⟨k, hk, rfl⟩
      cases k with
      | zero =>
        refine ⟨x ^ m * y ^ 0, ⟨0, Nat.zero_le m, by simp⟩, x, Or.inl rfl, ?_⟩
        simp [pow_succ]
      | succ k =>
        refine ⟨x ^ (m - k) * y ^ k, ⟨k, by omega, rfl⟩, y, Or.inr rfl, ?_⟩
        rw [Nat.add_sub_add_right, pow_succ]
        ac_rfl

/-- Exact generating set for the genuine ideal power. -/
theorem pair_ideal_pow (x y : A) (m : ℕ) :
    (Ideal.span {x,y}) ^ m =
      Ideal.span {z | ∃ k ≤ m, z = x ^ (m - k) * y ^ k} := by
  rw [Ideal.span, Submodule.span_pow, pair_set_pow]

end Nagata.Workers.W30

end

section

namespace Nagata.Workers.W30

/-- Bivariate exponent vector in coordinate order `(X,Y)`. -/
noncomputable def exponentPair (ell b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ell + Finsupp.single 1 b

@[simp] theorem exponentPair_zero (ell b : ℕ) : exponentPair ell b 0 = ell := by
  simp [exponentPair]

@[simp] theorem exponentPair_one (ell b : ℕ) : exponentPair ell b 1 = b := by
  simp [exponentPair]

lemma exponentPair_eta (a : Fin 2 →₀ ℕ) : exponentPair (a 0) (a 1) = a := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp

lemma exponentPair_le_iff {ell b : ℕ} {a : Fin 2 →₀ ℕ} :
    exponentPair ell b ≤ a ↔ ell ≤ a 0 ∧ b ≤ a 1 := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h0,h1⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h0
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa using h1

lemma exponentPair_injective : Function.Injective (fun p : ℕ × ℕ => exponentPair p.1 p.2) := by
  intro p t h
  apply Prod.ext
  · simpa using congrArg (fun a : Fin 2 →₀ ℕ => a 0) h
  · simpa using congrArg (fun a : Fin 2 →₀ ℕ => a 1) h

noncomputable def jetExponent {q m : ℕ} (i : JetIndex q m) : Fin 2 →₀ ℕ :=
  exponentPair i.2.val i.1.val

theorem jetIndexPair_injective {q m : ℕ} :
    Function.Injective (@jetIndexPair q m) := by
  intro i j h
  apply (jetIndexEquivPairs q m).injective
  exact Subtype.ext h

theorem jetExponent_injective {q m : ℕ} :
    Function.Injective (@jetExponent q m) := by
  intro i j h
  apply jetIndexPair_injective
  exact exponentPair_injective h

@[simp] theorem jetExponent_inj {q m : ℕ} (i j : JetIndex q m) :
    jetExponent i = jetExponent j ↔ i = j :=
  jetExponent_injective.eq_iff

end Nagata.Workers.W30

end

section

/-! Actual coefficient projection and polynomial section for the finite jet shape.
These maps are defined on genuine bivariate polynomials. -/

namespace Nagata.Workers.W30

open MvPolynomial
open scoped BigOperators

variable (R : Type*) [CommRing R] (q m : ℕ)

/-- Extract the coefficients at the finite collision jet indices. -/
noncomputable def jetCoeffMap :
    MvPolynomial (Fin 2) R →ₗ[R] (JetIndex q m → R) :=
  LinearMap.pi fun i => lcoeff R (jetExponent i)

@[simp] theorem jetCoeffMap_apply (p : MvPolynomial (Fin 2) R) (i : JetIndex q m) :
    jetCoeffMap R q m p i = p.coeff (jetExponent i) := rfl

/-- The polynomial with exactly the prescribed finite jet coefficients. -/
noncomputable def jetPolynomial (v : JetIndex q m → R) : MvPolynomial (Fin 2) R :=
  ∑ i, monomial (jetExponent i) (v i)

@[simp] theorem jetCoeffMap_jetPolynomial (v : JetIndex q m → R) :
    jetCoeffMap R q m (jetPolynomial R q m v) = v := by
  classical
  funext i
  simp [jetPolynomial]

/-- Coefficient projection onto the prescribed finite jet indices is surjective. -/
theorem jetCoeffMap_surjective : Function.Surjective (jetCoeffMap R q m) := by
  intro v
  exact ⟨jetPolynomial R q m v, jetCoeffMap_jetPolynomial R q m v⟩

end Nagata.Workers.W30

end

section

/-! The actual ideal `(X^q,Y)^m` and its finite coefficient conditions. -/

namespace Nagata.Workers.W30

open MvPolynomial

variable {R : Type*} [CommRing R]

abbrev Bivariate (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R

/-- `(X^q,Y)^m` in the genuine bivariate polynomial ring. -/
noncomputable def collisionIdeal (R : Type*) [CommRing R] (q m : ℕ) : Ideal (Bivariate R) :=
  (Ideal.span {X (0 : Fin 2) ^ q, X (1 : Fin 2)}) ^ m

lemma monomial_exponentPair (ell b : ℕ) :
    (monomial (exponentPair ell b) 1 : Bivariate R) = X 0 ^ ell * X 1 ^ b := by
  rw [exponentPair, monomial_add_single, ← X_pow_eq_monomial]

/-- Exact set of the exponent vectors of the standard generators of `(X^q,Y)^m`. -/
def collisionGenerators (q m : ℕ) : Set (Fin 2 →₀ ℕ) :=
  {a | ∃ k ≤ m, a = exponentPair (q * (m - k)) k}

/-- The ordinary power ideal is exactly the monomial ideal with these generators. -/
theorem collisionIdeal_eq_monomial_span (q m : ℕ) :
    collisionIdeal R q m =
      Ideal.span ((fun a => monomial a (1 : R)) '' collisionGenerators q m) := by
  rw [collisionIdeal, pair_ideal_pow]
  congr 1
  ext p
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨exponentPair (q * (m-k)) k, ⟨k,hk,rfl⟩, ?_⟩
    simp only [monomial_exponentPair, pow_mul]
  · rintro ⟨a, ⟨k,hk,rfl⟩, rfl⟩
    exact ⟨k,hk, by simp only [monomial_exponentPair, pow_mul]⟩

lemma exists_collisionGenerator_le_iff (q m : ℕ) (a : Fin 2 →₀ ℕ) :
    (∃ g ∈ collisionGenerators q m, g ≤ a) ↔ GeneratorDivides q m (a 0) (a 1) := by
  constructor
  · rintro ⟨g, ⟨k,hk,rfl⟩, hle⟩
    exact ⟨k,hk,(exponentPair_le_iff.mp hle).1,(exponentPair_le_iff.mp hle).2⟩
  · rintro ⟨k,hk,h0,h1⟩
    exact ⟨exponentPair (q*(m-k)) k, ⟨k,hk,rfl⟩, exponentPair_le_iff.mpr ⟨h0,h1⟩⟩

/-- Membership in the genuine ideal power is the support divisibility criterion. -/
theorem mem_collisionIdeal_iff_support (q m : ℕ) (p : Bivariate R) :
    p ∈ collisionIdeal R q m ↔
      ∀ a ∈ p.support, GeneratorDivides q m (a 0) (a 1) := by
  rw [collisionIdeal_eq_monomial_span, mem_monomial_span_iff]
  simp only [exists_collisionGenerator_le_iff]

/-- The exact coefficient-vanishing characterization of `(X^q,Y)^m`.
No positive-parameter assumption is needed, including the zero ideal-power case. -/
theorem mem_collisionIdeal_iff_coefficients (q m : ℕ) (p : Bivariate R) :
    p ∈ collisionIdeal R q m ↔
      ∀ b < m, ∀ ell < q * (m-b), p.coeff (exponentPair ell b) = 0 := by
  rw [mem_collisionIdeal_iff_support]
  constructor
  · intro h b hb ell hell
    by_contra hne
    have hm := h (exponentPair ell b) (mem_support_iff.mpr hne)
    exact (not_generatorDivides_iff.mpr ⟨hb,hell⟩) (by simpa using hm)
  · intro h a ha
    by_contra hn
    obtain ⟨hb,hell⟩ := not_generatorDivides_iff.mp hn
    have heq := h (a 1) hb (a 0) hell
    rw [exponentPair_eta] at heq
    exact (mem_support_iff.mp ha) heq

/-- Membership is equivalent to vanishing of the actual finite jet coefficient map. -/
theorem mem_collisionIdeal_iff_jetCoeffMap (q m : ℕ) (p : Bivariate R) :
    p ∈ collisionIdeal R q m ↔ jetCoeffMap R q m p = 0 := by
  rw [mem_collisionIdeal_iff_coefficients]
  constructor
  · intro h
    funext i
    exact h i.1.val i.1.isLt i.2.val i.2.isLt
  · intro h b hb ell hell
    have hv := congrFun h (⟨⟨b,hb⟩,⟨ell,hell⟩⟩ : JetIndex q m)
    exact hv

end Nagata.Workers.W30

end

section

/-! The ordinary bivariate maximal-ideal specialization of the collision ideal. -/

namespace Nagata.Workers.W30

open MvPolynomial

variable {R : Type*} [CommRing R]

lemma range_X_fin_two :
    Set.range (X : Fin 2 → Bivariate R) = {X 0, X 1} := by
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Or.inl rfl
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩

/-- Membership in the ordinary origin maximal ideal to power `m` is exactly
vanishing of every coefficient of total degree less than `m`. -/
theorem mem_originIdeal_pow_iff (m : ℕ) (p : Bivariate R) :
    p ∈ (Ideal.span (Set.range (X : Fin 2 → Bivariate R))) ^ m ↔
      ∀ ell b : ℕ, ell + b < m → p.coeff (exponentPair ell b) = 0 := by
  have hbase := mem_collisionIdeal_iff_coefficients (R := R) 1 m p
  simp only [collisionIdeal, pow_one, Nat.one_mul, range_X_fin_two] at hbase ⊢
  rw [hbase]
  constructor
  · intro h ell b hlt
    exact h b (by omega) ell (by omega)
  · intro h b hb ell hell
    exact h ell b (by omega)

end Nagata.Workers.W30

end

end OAI

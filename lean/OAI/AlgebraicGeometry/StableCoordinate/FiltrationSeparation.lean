import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FilteredAlgebra.Basic
import Mathlib.Tactic

namespace OAI

/-!
# Separation for the integer filtration

The variables are ordered `(p,s,u,F,J)`.  The integer weight is
`-exp(p) + exp(F) + exp(J)`.  This file proves the negative-weight
power-divisibility estimate, and separates every image filtration in a
Noetherian domain whenever the image of `p` is a nonunit.
-/

noncomputable section

namespace StableCoordinate
namespace Filtration

open MvPolynomial

/-- The source weight `(-1,0,0,1,1)` on exponent vectors. -/
def monomialWeight : (Fin 5 →₀ ℕ) →+ ℤ where
  toFun e := (e 3 : ℤ) + (e 4 : ℤ) - (e 0 : ℤ)
  map_zero' := by simp
  map_add' e f := by simp; omega

@[simp] theorem monomialWeight_apply (e : Fin 5 →₀ ℕ) :
    monomialWeight e = (e 3 : ℤ) + (e 4 : ℤ) - (e 0 : ℤ) := rfl

/-- A monomial of weight at most `-r` has at least `r` factors of `p`. -/
theorem exponent_zero_ge_of_weight_le_neg {e : Fin 5 →₀ ℕ} {r : ℕ}
    (h : monomialWeight e ≤ -(r : ℤ)) : r ≤ e 0 := by
  simp only [monomialWeight_apply] at h
  omega

variable (K : Type*) [CommRing K]

/-- The span of the monomials of integer source weight at most `d`. -/
def piece (d : ℤ) : Submodule K (MvPolynomial (Fin 5) K) :=
  Submodule.span K {q | ∃ e, monomialWeight e ≤ d ∧ q = monomial e 1}

/-- The source filtration is increasing. -/
theorem piece_mono : Monotone (piece K) := by
  intro d e hde
  apply Submodule.span_mono
  rintro q ⟨m, hm, rfl⟩
  exact ⟨m, hm.trans hde, rfl⟩

/-- Every negative-weight monomial is divisible by the corresponding power of `p`. -/
theorem pow_X_zero_dvd_monomial {e : Fin 5 →₀ ℕ} {r : ℕ}
    (h : monomialWeight e ≤ -(r : ℤ)) (c : K) :
    (X (0 : Fin 5) : MvPolynomial (Fin 5) K) ^ r ∣ monomial e c := by
  rw [X_pow_eq_monomial, monomial_dvd_monomial]
  refine ⟨Or.inr ?_, one_dvd _⟩
  exact Finsupp.single_le_iff.mpr (exponent_zero_ge_of_weight_le_neg h)

/-- The negative source piece is contained in the principal ideal `(p^r)`. -/
theorem piece_neg_le_span_pow (r : ℕ) :
    piece K (-(r : ℤ)) ≤
      (Ideal.span {((X (0 : Fin 5) : MvPolynomial (Fin 5) K) ^ r)}).restrictScalars K := by
  apply Submodule.span_le.mpr
  rintro q ⟨e, he, rfl⟩
  exact Ideal.mem_span_singleton.mpr (pow_X_zero_dvd_monomial K he 1)

/-- A monomial belongs to its assigned filtration piece. -/
theorem monomial_mem_piece {e : Fin 5 →₀ ℕ} {d : ℤ}
    (h : monomialWeight e ≤ d) (c : K) : monomial e c ∈ piece K d := by
  have hm : monomial e (1 : K) ∈ piece K d :=
    Submodule.subset_span ⟨e, h, rfl⟩
  simpa only [smul_monomial, smul_eq_mul, mul_one] using (piece K d).smul_mem c hm

/-- Membership can equivalently be tested on the support. -/
theorem mem_piece_iff {q : MvPolynomial (Fin 5) K} {d : ℤ} :
    q ∈ piece K d ↔ ∀ e ∈ q.support, monomialWeight e ≤ d := by
  classical
  constructor
  · intro hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨e, he, rfl⟩ := hq
      intro m hm
      have hm' : m = e := Finset.mem_singleton.mp (support_monomial_subset hm)
      simpa [hm'] using he
    | zero => simp
    | add q r hq hr ihq ihr =>
      intro e he
      rcases Finset.mem_union.mp (support_add he) with he | he
      · exact ihq e he
      · exact ihr e he
    | smul c q hq ihq =>
      intro e he
      exact ihq e (support_smul he)
  · intro hq
    rw [q.as_sum]
    apply Submodule.sum_mem
    intro e he
    exact monomial_mem_piece K (hq e he) _

/-- Exhaustiveness of the filtration on the five-variable polynomial ring. -/
theorem exists_mem_piece (q : MvPolynomial (Fin 5) K) :
    ∃ d : ℤ, q ∈ piece K d := by
  classical
  refine ⟨(q.support.sup fun e => (monomialWeight e).toNat : ℕ), mem_piece_iff K |>.mpr ?_⟩
  intro e he
  have hsup : (monomialWeight e).toNat ≤ q.support.sup (fun e => (monomialWeight e).toNat) :=
    Finset.le_sup (f := fun e => (monomialWeight e).toNat) he
  omega

/-- The constant one has weight zero. -/
theorem one_mem_piece : (1 : MvPolynomial (Fin 5) K) ∈ piece K 0 := by
  simpa only [monomial_zero', C_1] using
    (monomial_mem_piece K (e := 0) (d := 0) (by simp) 1)

/-- Multiplication adds filtration indices, including negative indices. -/
theorem mul_mem_piece {q r : MvPolynomial (Fin 5) K} {d e : ℤ}
    (hq : q ∈ piece K d) (hr : r ∈ piece K e) : q * r ∈ piece K (d + e) := by
  classical
  induction hq, hr using Submodule.span_induction₂ with
  | mem_mem q r hq hr =>
    obtain ⟨m, hm, rfl⟩ := hq
    obtain ⟨n, hn, rfl⟩ := hr
    rw [monomial_mul_monomial]
    apply monomial_mem_piece
    simpa only [map_add] using add_le_add hm hn
  | zero_left => simp
  | zero_right => simp
  | add_left q r s hq hr hs ihq ihr =>
    rw [add_mul]
    exact (piece K _).add_mem ihq ihr
  | add_right q r s hq hr hs ihr ihs =>
    rw [mul_add]
    exact (piece K _).add_mem ihr ihs
  | smul_left c q r hq hr ihr =>
    rw [smul_mul_assoc]
    exact (piece K _).smul_mem c ihr
  | smul_right c q r hq hr ihr =>
    rw [mul_smul_comm]
    exact (piece K _).smul_mem c ihr

instance : SetLike.GradedMonoid (piece K) where
  one_mem := one_mem_piece K
  mul_mem := fun _ _ _ _ hq hr => mul_mem_piece K hq hr

instance : IsRingFiltration (piece K) (fun d => piece K (d - 1)) :=
  IsRingFiltration.mk_int _ (piece_mono K)

variable {K}
variable {A : Type*} [CommRing A] [Algebra K A]

/-- The image filtration under a polynomial presentation.  In particular this
is the quotient filtration when `φ` is an ideal quotient homomorphism. -/
def imagePiece (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (d : ℤ) : Submodule K A :=
  (piece K d).map φ.toLinearMap

/-- The image filtration is increasing. -/
theorem imagePiece_mono (φ : MvPolynomial (Fin 5) K →ₐ[K] A) :
    Monotone (imagePiece φ) := by
  intro d e hde
  exact Submodule.map_mono (piece_mono K hde)

/-- A surjective polynomial presentation gives an exhaustive image filtration. -/
theorem exists_mem_imagePiece (φ : MvPolynomial (Fin 5) K →ₐ[K] A)
    (hφ : Function.Surjective φ) (a : A) : ∃ d : ℤ, a ∈ imagePiece φ d := by
  obtain ⟨q, rfl⟩ := hφ a
  obtain ⟨d, hd⟩ := exists_mem_piece K q
  exact ⟨d, q, hd, rfl⟩

/-- A source generator belongs to the piece specified by its weight. -/
theorem X_mem_piece (i : Fin 5) :
    (X i : MvPolynomial (Fin 5) K) ∈ piece K (monomialWeight (Finsupp.single i 1)) := by
  exact monomial_mem_piece K le_rfl 1

/-- The negative degree of the distinguished variable is available before
separation or identification of the associated graded ring. -/
theorem X_zero_mem_piece_neg_one :
    (X (0 : Fin 5) : MvPolynomial (Fin 5) K) ∈ piece K (-1) := by
  simpa [monomialWeight] using (X_mem_piece (K := K) 0)

/-- The image of the distinguished variable belongs to degree `-1`. -/
theorem image_X_zero_mem_neg_one (φ : MvPolynomial (Fin 5) K →ₐ[K] A) :
    φ (X 0) ∈ imagePiece φ (-1) :=
  ⟨X 0, X_zero_mem_piece_neg_one, rfl⟩

/-- The image filtration is multiplicative. -/
theorem mul_mem_imagePiece (φ : MvPolynomial (Fin 5) K →ₐ[K] A)
    {a b : A} {d e : ℤ} (ha : a ∈ imagePiece φ d) (hb : b ∈ imagePiece φ e) :
    a * b ∈ imagePiece φ (d + e) := by
  obtain ⟨q, hq, rfl⟩ := ha
  obtain ⟨r, hr, rfl⟩ := hb
  exact ⟨q * r, mul_mem_piece K hq hr, map_mul φ q r⟩

instance (φ : MvPolynomial (Fin 5) K →ₐ[K] A) : SetLike.GradedMonoid (imagePiece φ) where
  one_mem := ⟨1, one_mem_piece K, map_one φ⟩
  mul_mem := fun _ _ _ _ ha hb => mul_mem_imagePiece φ ha hb

instance (φ : MvPolynomial (Fin 5) K →ₐ[K] A) :
    IsRingFiltration (imagePiece φ) (fun d => imagePiece φ (d - 1)) :=
  IsRingFiltration.mk_int _ (imagePiece_mono φ)

/-- Divisibility survives the polynomial presentation. -/
theorem pow_dvd_of_mem_imagePiece_neg (φ : MvPolynomial (Fin 5) K →ₐ[K] A)
    {r : ℕ} {a : A} (ha : a ∈ imagePiece φ (-(r : ℤ))) :
    φ (X 0) ^ r ∣ a := by
  obtain ⟨q, hq, rfl⟩ := ha
  have hdiv : (X (0 : Fin 5) : MvPolynomial (Fin 5) K) ^ r ∣ q :=
    Ideal.mem_span_singleton.mp (piece_neg_le_span_pow K r hq)
  simpa only [map_pow, AlgHom.toLinearMap_apply] using map_dvd φ hdiv

/-- Krull intersection separates the image filtration.  No claim that every
image has this property is made: the noetherian-domain and nonunit hypotheses
are explicit and must be supplied by a polynomial-presentation theorem. -/
theorem eq_zero_of_mem_all_imagePieces [IsNoetherianRing A] [IsDomain A]
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (hp : ¬ IsUnit (φ (X 0)))
    {a : A} (ha : ∀ d : ℤ, a ∈ imagePiece φ d) : a = 0 := by
  let I : Ideal A := Ideal.span {φ (X 0)}
  have hI : I ≠ ⊤ := by
    simpa only [I, ne_eq, Ideal.span_singleton_eq_top] using hp
  have hmem : a ∈ ⨅ r : ℕ, I ^ r := by
    apply Ideal.mem_iInf.mpr
    intro r
    change a ∈ (Ideal.span {φ (X 0)}) ^ r
    rw [Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton.mpr (pow_dvd_of_mem_imagePiece_neg φ (ha (-(r : ℤ))))
  rw [Ideal.iInf_pow_eq_bot_of_isDomain I hI] at hmem
  exact hmem

/-- Equivalent submodule-valued statement of separation. -/
theorem iInf_imagePiece_eq_bot [IsNoetherianRing A] [IsDomain A]
    (φ : MvPolynomial (Fin 5) K →ₐ[K] A) (hp : ¬ IsUnit (φ (X 0))) :
    (⨅ d : ℤ, imagePiece φ d) = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  exact eq_zero_of_mem_all_imagePieces φ hp ((Submodule.mem_iInf _).mp ha)

end Filtration
end StableCoordinate

end

end OAI

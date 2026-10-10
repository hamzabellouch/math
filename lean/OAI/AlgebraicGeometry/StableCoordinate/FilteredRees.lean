import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.FilteredAlgebra.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

namespace OAI

/-!
# The associated graded algebra via the extended Rees algebra

For an increasing integer filtration `F`, the Rees algebra consists of Laurent
polynomials whose coefficient at `d` belongs to `F d`.  Its quotient by `T`
is the associated graded algebra.  This construction supplies an actual ring,
including negative filtration indices, without treating the associated-graded
algebra or its multiplicative structure as an assumed interface.
-/

namespace StableCoordinate.FilteredRees

open AddMonoidAlgebra

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (F : ℤ → Submodule k A) [SetLike.GradedMonoid F]

/-- The extended Rees algebra with integer-indexed, increasing convention. -/
noncomputable def rees : Subalgebra k (LaurentPolynomial A) where
  carrier := {p | ∀ d, p.coeff d ∈ F d}
  zero_mem' := by intro d; exact (F d).zero_mem
  one_mem' := by
    intro d
    by_cases hd : d = 0
    · subst d
      simpa only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_same] using SetLike.one_mem_graded F
    · simpa only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, ite_eq_right (Ne.symm hd)] using (F d).zero_mem
  add_mem' hp hq := by
    intro d
    exact (F d).add_mem (hp d) (hq d)
  mul_mem' {p q} hp hq := by
    intro d
    rw [AddMonoidAlgebra.coeff_mul]
    simp only [Finsupp.sum]
    apply (F d).sum_mem
    intro i hi
    apply (F d).sum_mem
    intro j hj
    split_ifs with hij
    · simpa only [← hij] using SetLike.mul_mem_graded (hp i) (hq j)
    · exact (F d).zero_mem
  algebraMap_mem' r := by
    intro d
    rw [Algebra.algebraMap_eq_smul_one, AddMonoidAlgebra.coeff_smul_apply]
    by_cases hd : d = 0
    · subst d
      simpa only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_eq_same] using (F 0).smul_mem r (SetLike.one_mem_graded F)
    · simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply, ite_eq_right (Ne.symm hd), smul_zero, Submodule.zero_mem]

@[simp] theorem mem_rees (p : LaurentPolynomial A) :
    p ∈ rees F ↔ ∀ d, p.coeff d ∈ F d := Iff.rfl

/-- A homogeneous element of the Rees algebra. -/
noncomputable def homogeneous (d : ℤ) (a : F d) : rees F :=
  ⟨AddMonoidAlgebra.single d (a : A), by
    intro i
    by_cases hi : d = i
    · subst i
      simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using a.property
    · simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right hi] using (F i).zero_mem⟩

@[simp] theorem homogeneous_coe (d : ℤ) (a : F d) :
    (homogeneous F d a : LaurentPolynomial A) = AddMonoidAlgebra.single d (a : A) := rfl

/-- The positive Laurent parameter lies in the Rees algebra by monotonicity. -/
noncomputable def parameter (hmono : Monotone F) : rees F :=
  homogeneous F 1 ⟨1, hmono (by decide : (0 : ℤ) ≤ 1) (SetLike.one_mem_graded F)⟩

@[simp] theorem parameter_coe (hmono : Monotone F) :
    (parameter F hmono : LaurentPolynomial A) = AddMonoidAlgebra.single 1 1 := rfl

noncomputable def parameterIdeal (hmono : Monotone F) : Ideal (rees F) :=
  Ideal.span {parameter F hmono}

/-- The genuine associated graded algebra, modeled as the Rees special fiber. -/
abbrev Gr (hmono : Monotone F) := rees F ⧸ parameterIdeal F hmono

/-- The class of `a` in degree `d`. -/
noncomputable def initial (hmono : Monotone F) (d : ℤ) (a : F d) : Gr F hmono :=
  Ideal.Quotient.mk (parameterIdeal F hmono) (homogeneous F d a)

/-- A homogeneous class vanishes precisely when its representative is in the
previous filtration step.  In particular, minimal-degree representatives have
nonzero initial forms even when the degree is negative. -/
theorem initial_eq_zero_iff (hmono : Monotone F) (d : ℤ) (a : F d) :
    initial F hmono d a = 0 ↔ (a : A) ∈ F (d - 1) := by
  change Ideal.Quotient.mk (parameterIdeal F hmono) (homogeneous F d a) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, parameterIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩
    have he := congrArg (fun p : rees F => (p : LaurentPolynomial A).coeff d) hq
    have hae : (a : A) = (q : LaurentPolynomial A).coeff (d - 1) := by
      change (AddMonoidAlgebra.single d (a : A)).coeff d =
        (AddMonoidAlgebra.single 1 1 * (q : LaurentPolynomial A)).coeff d at he
      rw [AddMonoidAlgebra.coeff_single_mul_apply] at he
      simpa only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same, one_mul,
        sub_eq_add_neg, add_comm] using he
    rw [hae]
    exact q.property (d - 1)
  · intro ha
    refine ⟨homogeneous F (d - 1) ⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    change AddMonoidAlgebra.single d (a : A) =
      AddMonoidAlgebra.single 1 1 * AddMonoidAlgebra.single (d - 1) (a : A)
    rw [AddMonoidAlgebra.single_mul_single, one_mul]
    congr 1
    omega

/-- The associated-graded multiplication is induced by multiplication of
filtration representatives. -/
theorem initial_mul (hmono : Monotone F) (d e : ℤ) (a : F d) (b : F e) :
    initial F hmono d a * initial F hmono e b =
      initial F hmono (d + e) ⟨(a : A) * (b : A),
        SetLike.mul_mem_graded a.property b.property⟩ := by
  rw [initial, initial, ← map_mul]
  congr 1
  apply Subtype.ext
  exact AddMonoidAlgebra.single_mul_single d e (a : A) (b : A)


/-- Every Rees element is the finite sum of its homogeneous coefficients. -/
theorem rees_eq_sum (p : rees F) :
    p = ∑ d ∈ (p : LaurentPolynomial A).coeff.support,
      homogeneous F d ⟨(p : LaurentPolynomial A).coeff d, p.property d⟩ := by
  apply Subtype.ext
  change (p : LaurentPolynomial A) = (rees F).val
    (∑ d ∈ (p : LaurentPolynomial A).coeff.support,
      homogeneous F d ⟨(p : LaurentPolynomial A).coeff d, p.property d⟩)
  rw [map_sum]
  exact (AddMonoidAlgebra.sum_coeff_single (p : LaurentPolynomial A)).symm

/-- Addition of initial forms within one degree. -/
theorem initial_add (hmono : Monotone F) (d : ℤ) (a b : F d) :
    initial F hmono d (a + b) = initial F hmono d a + initial F hmono d b := by
  rw [initial, initial, initial, ← map_add]
  congr 1
  apply Subtype.ext
  exact AddMonoidAlgebra.single_add d (a : A) (b : A)

/-- Algebra homomorphisms from the associated graded algebra are determined by
all homogeneous classes. -/
theorem hom_ext {S : Type*} [CommRing S] [Algebra k S]
    (hmono : Monotone F) (f g : Gr F hmono →ₐ[k] S)
    (h : ∀ (d : ℤ) (a : F d), f (initial F hmono d a) = g (initial F hmono d a)) :
    f = g := by
  ext z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [rees_eq_sum F p, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact h d _

/-- All homogeneous classes generate the actual associated graded algebra. -/
theorem adjoin_initials_eq_top (hmono : Monotone F) :
    Algebra.adjoin k (Set.range fun a : (d : ℤ) × (F d) => initial F hmono a.1 a.2) = ⊤ := by
  apply top_unique
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [rees_eq_sum F p, map_sum]
  apply Subalgebra.sum_mem
  intro d hd
  exact Algebra.subset_adjoin ⟨⟨d, _⟩, rfl⟩

end StableCoordinate.FilteredRees

end OAI

import Mathlib.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.IsPrincipal
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

namespace OAI

/-!
# Homogeneous factorization and height-one prime generators
-/

section

namespace Nagata.Workers.W30

open UniqueFactorizationMonoid

noncomputable section

abbrev TernaryPolynomial := MvPolynomial (Fin 3) ℂ

local instance : DecidableEq (Associates TernaryPolynomial) := Classical.decEq _

/-- An actual multiset of irreducible polynomial factors; repetitions retain multiplicity. -/
def equationFactors (F : TernaryPolynomial) : Multiset TernaryPolynomial := factors F

theorem equationFactors_irreducible (F : TernaryPolynomial) :
    ∀ P ∈ equationFactors F, Irreducible P := irreducible_of_factor

theorem equationFactors_product (F : TernaryPolynomial) (hF : F ≠ 0) :
    Associated (equationFactors F).prod F := factors_prod hF

/-- Uniqueness means a multiset matching of associated irreducible factors,
which includes arbitrary reorderings and multiplication of each factor by a unit. -/
theorem equationFactors_unique {F : TernaryPolynomial} (hF : F ≠ 0)
    (L : Multiset TernaryPolynomial) (hL : ∀ P ∈ L, Irreducible P)
    (hprod : Associated L.prod F) : Multiset.Rel Associated L (equationFactors F) :=
  factors_unique hL (equationFactors_irreducible F)
    (hprod.trans (equationFactors_product F hF).symm)

/-- Canonical multiplicities indexed by polynomial associate classes. -/
def equationMultiplicity (F : TernaryPolynomial) : Associates TernaryPolynomial →₀ ℕ :=
  factorization (Associates.mk F)

theorem equationMultiplicity_mul {F G : TernaryPolynomial} (hF : F ≠ 0) (hG : G ≠ 0) :
    equationMultiplicity (F * G) = equationMultiplicity F + equationMultiplicity G := by
  unfold equationMultiplicity
  rw [← Associates.mk_mul_mk, factorization_mul (Associates.mk_ne_zero.mpr hF)
    (Associates.mk_ne_zero.mpr hG)]

theorem equationMultiplicity_pow (F : TernaryPolynomial) (n : ℕ) :
    equationMultiplicity (F ^ n) = n • equationMultiplicity F := by
  unfold equationMultiplicity
  rw [Associates.mk_pow, factorization_pow]

/-- No equation multiplicity is discarded: equality of canonical multiplicity
vectors is equivalent to association of nonzero polynomial equations. -/
theorem equationMultiplicity_eq_iff {F G : TernaryPolynomial} (hF : F ≠ 0) (hG : G ≠ 0) :
    equationMultiplicity F = equationMultiplicity G ↔ Associated F G := by
  constructor
  · intro h
    have ha := associated_of_factorization_eq (Associates.mk F) (Associates.mk G)
      (Associates.mk_ne_zero.mpr hF) (Associates.mk_ne_zero.mpr hG) h
    exact Associates.mk_eq_mk_iff_associated.mp (associated_iff_eq.mp ha)
  · intro h
    unfold equationMultiplicity
    rw [Associates.mk_eq_mk_iff_associated.mpr h]

/-- Send an associate class to its actual principal ideal. -/
def associatePrincipalIdeal (a : Associates TernaryPolynomial) : Ideal TernaryPolynomial :=
  (Ideal.associatesEquivIsPrincipal TernaryPolynomial a).val

theorem associatePrincipalIdeal_injective : Function.Injective associatePrincipalIdeal := by
  intro a b h
  apply (Ideal.associatesEquivIsPrincipal TernaryPolynomial).injective
  exact Subtype.ext h

@[simp] theorem associatePrincipalIdeal_mk (F : TernaryPolynomial) :
    associatePrincipalIdeal (Associates.mk F) = Ideal.span {F} := rfl

/-- A finite effective cycle of actual principal ideals, with natural weights. -/
def equationIdealCycle (F : TernaryPolynomial) : Ideal TernaryPolynomial →₀ ℕ :=
  (equationMultiplicity F).mapDomain associatePrincipalIdeal

theorem equationIdealCycle_mul {F G : TernaryPolynomial} (hF : F ≠ 0) (hG : G ≠ 0) :
    equationIdealCycle (F * G) = equationIdealCycle F + equationIdealCycle G := by
  simp only [equationIdealCycle, equationMultiplicity_mul hF hG, Finsupp.mapDomain_add]

theorem equationIdealCycle_eq_iff {F G : TernaryPolynomial} (hF : F ≠ 0) (hG : G ≠ 0) :
    equationIdealCycle F = equationIdealCycle G ↔ Associated F G := by
  change Finsupp.mapDomain associatePrincipalIdeal (equationMultiplicity F) =
    Finsupp.mapDomain associatePrincipalIdeal (equationMultiplicity G) ↔ _
  rw [(Finsupp.mapDomain_injective associatePrincipalIdeal_injective).eq_iff,
    equationMultiplicity_eq_iff hF hG]

/-- Every supported associate class is prime. -/
theorem equationMultiplicity_support_prime (F : TernaryPolynomial)
    {a : Associates TernaryPolynomial} (ha : a ∈ (equationMultiplicity F).support) :
    Prime a := by
  apply prime_of_normalized_factor a
  simpa only [equationMultiplicity, support_factorization, Multiset.mem_toFinset] using ha

/-- The effective ideal cycle is supported on nonzero prime principal ideals. -/
theorem equationIdealCycle_support (F : TernaryPolynomial)
    {I : Ideal TernaryPolynomial} (hI : I ∈ (equationIdealCycle F).support) :
    I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal := by
  classical
  rw [equationIdealCycle,
    Finsupp.mapDomain_support_of_injective associatePrincipalIdeal_injective] at hI
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hI
  have hprime := equationMultiplicity_support_prime F ha
  obtain ⟨P, rfl⟩ := Associates.mk_surjective a
  have hP : Prime P := Associates.prime_mk.mp hprime
  rw [associatePrincipalIdeal_mk]
  exact ⟨(Ideal.span_singleton_prime hP.ne_zero).mpr hP,
    fun h => hP.ne_zero (Ideal.span_singleton_eq_bot.mp h), inferInstance⟩

/-- Each cycle coefficient is the full factor multiplicity, without merging
nonassociated factors. -/
theorem equationIdealCycle_coefficient (F : TernaryPolynomial)
    (a : Associates TernaryPolynomial) :
    equationIdealCycle F (associatePrincipalIdeal a) = equationMultiplicity F a := by
  exact Finsupp.mapDomain_apply_of_injective associatePrincipalIdeal_injective _ _

/-- The multiplicity vector reconstructs the original equation's associate class. -/
theorem equationMultiplicity_reconstruct (F : TernaryPolynomial) (hF : F ≠ 0) :
    (equationMultiplicity F).prod (fun a n => a ^ n) = Associates.mk F := by
  rw [← Finsupp.prod_toMultiset]
  change (Finsupp.toMultiset (Multiset.toFinsupp (normalizedFactors (Associates.mk F)))).prod = _
  rw [Multiset.toFinsupp_toMultiset]
  exact associated_iff_eq.mp (prod_normalizedFactors (Associates.mk_ne_zero.mpr hF))

end
end Nagata.Workers.W30

end

section

/-! Height-one prime ideals in a UFD are generated by an actual prime element. -/
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid

variable {R : Type*} [CommRing R] [IsDomain R]

/-- There is no proper inclusion between a nonzero prime and a prime of height at most one. -/
theorem nonzero_prime_eq_of_le_height_one {I P : Ideal R} [I.IsPrime] [P.IsPrime]
    (hI : I ≠ ⊥) (hIP : I ≤ P) (hP : P.height ≤ 1) : I = P := by
  by_contra hne
  have hlt : I < P := lt_of_le_of_ne hIP hne
  have hIheight : I.height < 1 :=
    (Ideal.height_le_iff (n := 1)).mp hP I inferInstance hlt
  have hzero : I.height = 0 := Order.lt_one_iff.mp hIheight
  have hbad : (⊥ : Ideal R).height < (0 : ℕ∞) :=
    (Ideal.height_le_iff (n := 0)).mp (by simp [hzero]) ⊥ inferInstance
      (bot_lt_iff_ne_bot.mpr hI)
  exact (not_lt_of_ge bot_le) hbad

variable [UniqueFactorizationMonoid R]

/-- A nonzero prime ideal of height at most one is the principal ideal of a prime element. -/
theorem height_one_prime_generator (P : Ideal R) [hPprime : P.IsPrime]
    (hP : P ≠ ⊥) (hheight : P.height ≤ 1) :
    ∃ f : R, Prime f ∧ P = Ideal.span {f} := by
  classical
  obtain ⟨x,hx,hx0⟩ := P.ne_bot_iff.mp hP
  have hprod : (factors x).prod ∈ P := P.mem_of_dvd (factors_prod hx0).dvd' hx
  obtain ⟨f,hf,hfP⟩ := (hPprime.multiset_prod_mem_iff_exists_mem (factors x)).mp hprod
  have hprime : Prime f := prime_of_factor f hf
  let : (Ideal.span ({f} : Set R)).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  refine ⟨f,hprime, ?_⟩
  exact (nonzero_prime_eq_of_le_height_one
    (fun h => hprime.ne_zero (Ideal.span_singleton_eq_bot.mp h))
    ((Ideal.span_singleton_le_iff_mem P).mpr hfP) hheight).symm

end Nagata.Workers.W30

end

section

/-! Homogeneous factorization by degree induction on actual multivariate polynomials. -/

namespace Nagata.Workers.W30

open MvPolynomial
open scoped BigOperators

variable {σ K : Type*} [Field K]

/-- The top homogeneous component never vanishes for a nonzero polynomial. -/
lemma topHomogeneousComponent_ne_zero {p : MvPolynomial σ K} (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  classical
  obtain ⟨a,ha,hdeg⟩ := Finset.exists_mem_eq_sup p.support
    (support_nonempty.mpr hp) (fun a => a.sum fun _ e => e)
  intro hz
  have hz' := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff a) hz
  have heq : a.degree = p.totalDegree := hdeg.symm
  have hc : p.coeff a = 0 := by
    simpa [coeff_homogeneousComponent, heq] using hz'
  exact (mem_support_iff.mp ha) hc

/-- Only the two top-degree components contribute to the top component of a product. -/
lemma topHomogeneousComponent_mul (p q : MvPolynomial σ K) :
    homogeneousComponent (p.totalDegree + q.totalDegree) (p*q) =
      homogeneousComponent p.totalDegree p * homogeneousComponent q.totalDegree q := by
  classical
  have hdecomp : p*q =
      (∑ i ∈ Finset.range (p.totalDegree+1), homogeneousComponent i p) *
      (∑ j ∈ Finset.range (q.totalDegree+1), homogeneousComponent j q) := by
    rw [sum_homogeneousComponent, sum_homogeneousComponent]
  rw [hdecomp]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single p.totalDegree]
  · rw [Finset.sum_eq_single q.totalDegree]
    · rw [homogeneousComponent_of_mem
        ((homogeneousComponent_isHomogeneous p.totalDegree p).mul
          (homogeneousComponent_isHomogeneous q.totalDegree q))]
      simp
    · intro j hj hne
      rw [homogeneousComponent_of_mem
        ((homogeneousComponent_isHomogeneous p.totalDegree p).mul
          (homogeneousComponent_isHomogeneous j q))]
      simp only [ite_eq_right_iff]
      intro h
      exfalso
      apply hne
      omega
    · simp
  · intro i hi hne
    apply Finset.sum_eq_zero
    intro j hj
    rw [homogeneousComponent_of_mem
      ((homogeneousComponent_isHomogeneous i p).mul
        (homogeneousComponent_isHomogeneous j q))]
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    have hne' : p.totalDegree + q.totalDegree ≠ i+j := by omega
    simp [hne']
  · simp

lemma degree_pos_of_nonzero_nonunit {p : MvPolynomial σ K} (hp : p ≠ 0)
    (hu : ¬ IsUnit p) : 0 < p.totalDegree := by
  by_contra hn
  have hz : p.totalDegree = 0 := by omega
  have heq := totalDegree_eq_zero_iff_eq_C.mp hz
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    apply hp
    rw [heq,hc,C_0]
  apply hu
  rw [heq]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- Every nonzero homogeneous polynomial is, up to a unit, a finite product of
irreducible homogeneous polynomials. Repeated factors are retained in the multiset. -/
theorem exists_homogeneous_irreducible_factors (p : MvPolynomial σ K) {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) :
    ∃ L : Multiset (MvPolynomial σ K),
      (∀ P ∈ L, Irreducible P ∧ P.IsHomogeneous P.totalDegree) ∧ Associated L.prod p := by
  classical
  suffices H : ∀ n (p : MvPolynomial σ K), p.totalDegree = n → p ≠ 0 →
      p.IsHomogeneous n → ∃ L : Multiset (MvPolynomial σ K),
      (∀ P ∈ L, Irreducible P ∧ P.IsHomogeneous P.totalDegree) ∧ Associated L.prod p from
    H d p (hhom.totalDegree hp) hp hhom
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hdeg hp hhom
    by_cases hu : IsUnit p
    · refine ⟨0, by simp, ?_⟩
      simpa using (associated_one_iff_isUnit.mpr hu).symm
    rcases irreducible_or_factor hu with hirr | ⟨a,b,hau,hbu,hab⟩
    · refine ⟨{p}, ?_, ?_⟩
      · intro P hP
        have heq : P = p := Multiset.mem_singleton.mp hP
        subst P
        exact ⟨hirr, by simpa only [hdeg] using hhom⟩
      · simp
    · have ha : a ≠ 0 := by intro h; simp [h] at hab; exact hp hab
      have hb : b ≠ 0 := by intro h; simp [h] at hab; exact hp hab
      have hsum : a.totalDegree+b.totalDegree = n := by
        rw [← totalDegree_mul_of_isDomain ha hb, ← hab, hdeg]
      have hapos := degree_pos_of_nonzero_nonunit ha hau
      have hbpos := degree_pos_of_nonzero_nonunit hb hbu
      let A := homogeneousComponent a.totalDegree a
      let B := homogeneousComponent b.totalDegree b
      have hA : A ≠ 0 := topHomogeneousComponent_ne_zero ha
      have hB : B ≠ 0 := topHomogeneousComponent_ne_zero hb
      have hAh : A.IsHomogeneous a.totalDegree := homogeneousComponent_isHomogeneous _ _
      have hBh : B.IsHomogeneous b.totalDegree := homogeneousComponent_isHomogeneous _ _
      have hprod : A*B = p := by
        change homogeneousComponent a.totalDegree a * homogeneousComponent b.totalDegree b = p
        rw [← topHomogeneousComponent_mul, ← hab, hsum,
          homogeneousComponent_of_mem hhom]
        simp
      obtain ⟨L,hL,hLp⟩ := ih a.totalDegree (by omega) A (hAh.totalDegree hA) hA hAh
      obtain ⟨M,hM,hMp⟩ := ih b.totalDegree (by omega) B (hBh.totalDegree hB) hB hBh
      refine ⟨L+M, ?_, ?_⟩
      · intro P hP
        exact (Multiset.mem_add.mp hP).elim (hL P) (hM P)
      · rw [Multiset.prod_add, ← hprod]
        exact hLp.mul_mul hMp

end Nagata.Workers.W30

end

section

/-! Units preserve genuine homogeneity; all irreducible factors of homogeneous forms are homogeneous. -/
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
variable {σ K : Type*} [Field K]

lemma unit_polynomial_totalDegree (u : (MvPolynomial σ K)ˣ) :
    (u : MvPolynomial σ K).totalDegree = 0 := by
  have h := totalDegree_mul_of_isDomain u.ne_zero (u⁻¹).ne_zero
  simp only [← Units.val_mul, mul_inv_cancel, Units.val_one, totalDegree_one] at h
  omega

lemma homogeneous_of_associated {p q : MvPolynomial σ K} {d : ℕ}
    (hp : p.IsHomogeneous d) (h : Associated p q) : q.IsHomogeneous d := by
  obtain ⟨u,rfl⟩ := h
  have hu : (u : MvPolynomial σ K).IsHomogeneous 0 :=
    (totalDegree_zero_iff_isHomogeneous σ).mp (unit_polynomial_totalDegree u)
  simpa only [add_zero] using hp.mul hu

/-- All irreducible factors returned by the actual UFD factorization are homogeneous. -/
theorem factors_homogeneous {p : MvPolynomial σ K} {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) :
    ∀ f ∈ factors p, f.IsHomogeneous f.totalDegree := by
  classical
  obtain ⟨L,hL,hprod⟩ := exists_homogeneous_irreducible_factors p hp hhom
  have hrel : Multiset.Rel Associated (factors p) L :=
    factors_unique irreducible_of_factor (fun f hf => (hL f hf).1)
      ((factors_prod hp).trans hprod.symm)
  intro f hf
  obtain ⟨g,hg,hfg⟩ := Multiset.exists_mem_of_rel_of_mem hrel hf
  have hgHom := homogeneous_of_associated (hL g hg).2 hfg.symm
  have hf0 : f ≠ 0 := (prime_of_factor f hf).ne_zero
  simpa only [hgHom.totalDegree hf0] using hgHom

end Nagata.Workers.W30

end

section

/-! Homogeneous equations for actual homogeneous height-one prime ideals. -/
namespace Nagata.Workers.W30
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ K : Type*} [Field K]

/-- An actual nonzero homogeneous element of a prime ideal has an irreducible
homogeneous factor in that ideal. -/
theorem homogeneous_prime_factor_in_ideal (P : Ideal (MvPolynomial σ K)) [hP : P.IsPrime]
    {x : MvPolynomial σ K} {d : ℕ} (hx : x ∈ P) (hx0 : x ≠ 0)
    (hhom : x.IsHomogeneous d) :
    ∃ f : MvPolynomial σ K, f ∈ P ∧ Irreducible f ∧ f.IsHomogeneous f.totalDegree := by
  obtain ⟨L,hL,hprod⟩ := exists_homogeneous_irreducible_factors x hx0 hhom
  have hmem : L.prod ∈ P := P.mem_of_dvd hprod.dvd' hx
  obtain ⟨f,hf,hfP⟩ := (hP.multiset_prod_mem_iff_exists_mem L).mp hmem
  exact ⟨f,hfP,hL f hf⟩

/-- Every nonzero homogeneous prime ideal of height at most one is generated
by an irreducible homogeneous polynomial of positive degree. -/
theorem homogeneous_height_one_prime_generator (P : Ideal (MvPolynomial σ K))
    [hP : P.IsPrime] (hP0 : P ≠ ⊥) (hheight : P.height ≤ 1)
    (hhom : P.IsHomogeneous (homogeneousSubmodule σ K)) :
    ∃ f : MvPolynomial σ K, Prime f ∧ f.IsHomogeneous f.totalDegree ∧
      0 < f.totalDegree ∧ P = Ideal.span {f} := by
  obtain ⟨x,hx,hx0⟩ := P.ne_bot_iff.mp hP0
  have hcompEq (D : DirectSum.Decomposition (homogeneousSubmodule σ K)) :
      (D.decompose' x x.totalDegree : MvPolynomial σ K) = homogeneousComponent x.totalDegree x := by
    rw [Subsingleton.elim D MvPolynomial.decomposition,
      MvPolynomial.decomposition.decompose'_apply]
  have hcomp := (hhom.mem_iff.mp hx) x.totalDegree
  rw [← DirectSum.Decomposition.decompose'_eq, hcompEq] at hcomp
  obtain ⟨f,hf,hfirr,hfhom⟩ := homogeneous_prime_factor_in_ideal P hcomp
    (topHomogeneousComponent_ne_zero hx0) (homogeneousComponent_isHomogeneous _ _)
  have hfprime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hfirr
  let : (Ideal.span ({f} : Set (MvPolynomial σ K))).IsPrime :=
    (Ideal.span_singleton_prime hfprime.ne_zero).mpr hfprime
  refine ⟨f,hfprime,hfhom,degree_pos_of_nonzero_nonunit hfprime.ne_zero hfprime.not_isUnit,?_⟩
  exact (nonzero_prime_eq_of_le_height_one
    (fun h => hfprime.ne_zero (Ideal.span_singleton_eq_bot.mp h))
    ((Ideal.span_singleton_le_iff_mem P).mpr hf) hheight).symm

end Nagata.Workers.W30

end

section

/-! Arbitrary divisors, including reducible and nonreduced divisors, preserve homogeneity. -/
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
variable {σ K : Type*} [Field K]

lemma homogeneous_multiset_prod (L : Multiset (MvPolynomial σ K))
    (hL : ∀ f ∈ L, f.IsHomogeneous f.totalDegree) :
    L.prod.IsHomogeneous (L.map MvPolynomial.totalDegree).sum := by
  induction L using Multiset.induction_on with
  | empty => simpa using (isHomogeneous_one σ K)
  | @cons f L ih =>
    simpa only [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons] using
      (hL f (Multiset.mem_cons_self _ _)).mul
        (ih (fun g hg => hL g (Multiset.mem_cons_of_mem hg)))

/-- Every actual polynomial divisor of a nonzero homogeneous polynomial is homogeneous. -/
theorem homogeneous_of_dvd {p f : MvPolynomial σ K} {d : ℕ}
    (hp : p ≠ 0) (hhom : p.IsHomogeneous d) (hf : f ∣ p) :
    f.IsHomogeneous f.totalDegree := by
  classical
  have hf0 : f ≠ 0 := by rintro rfl; exact hp (by simpa using hf)
  have hfac : ∀ a ∈ factors f, a.IsHomogeneous a.totalDegree := by
    intro a ha
    have hairr : Irreducible a := irreducible_of_factor a ha
    have hadvd : a ∣ p :=
      (Multiset.dvd_prod ha).trans ((factors_prod hf0).dvd.trans hf)
    obtain ⟨b,hb,hab⟩ := exists_mem_factors_of_dvd hp hairr hadvd
    have hah := homogeneous_of_associated (factors_homogeneous hp hhom b hb) hab.symm
    simpa only [hah.totalDegree hairr.ne_zero] using hah
  have hprod := homogeneous_multiset_prod (factors f) hfac
  have hfh := homogeneous_of_associated hprod (factors_prod hf0)
  simpa only [hfh.totalDegree hf0] using hfh

end Nagata.Workers.W30

end

section

/-! Homogeneity of a principal ideal is equivalent to genuine polynomial homogeneity. -/
namespace Nagata.Workers.W30
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {σ K : Type*} [Field K]

/-- A homogeneous principal ideal has a homogeneous generator. -/
theorem homogeneous_of_span_homogeneous {f : MvPolynomial σ K} (hf : f ≠ 0)
    (hI : (Ideal.span ({f} : Set (MvPolynomial σ K))).IsHomogeneous
      (homogeneousSubmodule σ K)) : f.IsHomogeneous f.totalDegree := by
  have hfmem : f ∈ Ideal.span ({f} : Set (MvPolynomial σ K)) := Ideal.subset_span (by simp)
  have hcompEq (D : DirectSum.Decomposition (homogeneousSubmodule σ K)) :
      (D.decompose' f f.totalDegree : MvPolynomial σ K) = homogeneousComponent f.totalDegree f := by
    rw [Subsingleton.elim D MvPolynomial.decomposition,
      MvPolynomial.decomposition.decompose'_apply]
  have hcomp := (hI.mem_iff.mp hfmem) f.totalDegree
  rw [← DirectSum.Decomposition.decompose'_eq, hcompEq] at hcomp
  exact homogeneous_of_dvd (topHomogeneousComponent_ne_zero hf)
    (homogeneousComponent_isHomogeneous _ _) (Ideal.mem_span_singleton.mp hcomp)

/-- Conversely, a homogeneous equation generates a homogeneous ideal. -/
theorem span_homogeneous_of_homogeneous {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    (Ideal.span ({f} : Set (MvPolynomial σ K))).IsHomogeneous (homogeneousSubmodule σ K) := by
  apply Ideal.homogeneous_span
  intro x hx
  have heq : x = f := Set.mem_singleton_iff.mp hx
  subst x
  exact ⟨d,hf⟩

theorem span_homogeneous_iff {f : MvPolynomial σ K} (hf : f ≠ 0) :
    (Ideal.span ({f} : Set (MvPolynomial σ K))).IsHomogeneous (homogeneousSubmodule σ K) ↔
      f.IsHomogeneous f.totalDegree :=
  ⟨homogeneous_of_span_homogeneous hf, span_homogeneous_of_homogeneous⟩

end Nagata.Workers.W30

end

end OAI

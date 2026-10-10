import OAI.AlgebraicGeometry.PlaneCurves.Factorization

namespace OAI

/-!
# Reconstruction of effective homogeneous prime ideal cycles
-/

section

/-! Reconstruct an equation from any finite effective cycle of prime associate classes. -/
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section

local instance cycleAssociateDecidableEq : DecidableEq (Associates TernaryPolynomial) := Classical.decEq _

/-- Choose an actual polynomial representing the product of prime classes with weights. -/
def cycleEquation (D : Associates TernaryPolynomial →₀ ℕ) : TernaryPolynomial :=
  Classical.choose (Associates.mk_surjective (D.prod fun a n => a ^ n))

@[simp] theorem cycleEquation_mk (D : Associates TernaryPolynomial →₀ ℕ) :
    Associates.mk (cycleEquation D) = D.prod (fun a n => a ^ n) :=
  Classical.choose_spec (Associates.mk_surjective (D.prod fun a n => a ^ n))

theorem cycleEquation_nonzero (D : Associates TernaryPolynomial →₀ ℕ)
    (hD : ∀ a ∈ D.support, Prime a) : cycleEquation D ≠ 0 := by
  classical
  apply Associates.mk_ne_zero.mp
  rw [cycleEquation_mk, ← Finsupp.prod_toMultiset]
  exact Multiset.prod_ne_zero_of_prime D.toMultiset (fun a ha => hD a ((D.mem_toMultiset a).mp ha))

/-- Full multiplicities of an arbitrary finite effective prime cycle are recovered exactly. -/
theorem cycleEquation_multiplicity (D : Associates TernaryPolynomial →₀ ℕ)
    (hD : ∀ a ∈ D.support, Prime a) : equationMultiplicity (cycleEquation D) = D := by
  classical
  unfold equationMultiplicity factorization
  rw [cycleEquation_mk, ← Finsupp.prod_toMultiset,
    normalizedFactors_prod_of_prime (fun a ha => hD a ((D.mem_toMultiset a).mp ha)),
    Finsupp.toMultiset_toFinsupp]

theorem cycleEquation_idealCycle (D : Associates TernaryPolynomial →₀ ℕ)
    (hD : ∀ a ∈ D.support, Prime a) :
    equationIdealCycle (cycleEquation D) = D.mapDomain associatePrincipalIdeal := by
  classical
  rw [equationIdealCycle, cycleEquation_multiplicity D hD]

/-- Reconstructing the divisor of a nonzero equation returns that equation up to a unit. -/
theorem cycleEquation_equationMultiplicity (F : TernaryPolynomial) (hF : F ≠ 0) :
    Associated (cycleEquation (equationMultiplicity F)) F := by
  classical
  apply Associates.mk_eq_mk_iff_associated.mp
  rw [cycleEquation_mk, equationMultiplicity_reconstruct F hF]

end
end Nagata.Workers.W30

end

section

/-! Zero-cycle exclusion and multiplicities of nonreduced equations. -/
namespace Nagata.Workers.W30

@[simp] theorem equationIdealCycle_one : equationIdealCycle (1 : TernaryPolynomial) = 0 := by
  simp only [equationIdealCycle, equationMultiplicity, Associates.mk_one,
    factorization_one, Finsupp.mapDomain_zero]

theorem equationIdealCycle_zero_iff {F : TernaryPolynomial} (hF : F ≠ 0) :
    equationIdealCycle F = 0 ↔ IsUnit F := by
  rw [← equationIdealCycle_one, equationIdealCycle_eq_iff hF one_ne_zero,
    associated_one_iff_isUnit]

/-- A nonzero effective cycle has positive polynomial degree. -/
theorem degree_pos_of_equationIdealCycle_ne_zero {F : TernaryPolynomial}
    (hF : F ≠ 0) (hcycle : equationIdealCycle F ≠ 0) : 0 < F.totalDegree := by
  exact degree_pos_of_nonzero_nonunit hF (fun hu => hcycle ((equationIdealCycle_zero_iff hF).mpr hu))

/-- Taking powers multiplies every actual prime-ideal cycle weight. -/
theorem equationIdealCycle_pow (F : TernaryPolynomial) (n : ℕ) :
    equationIdealCycle (F ^ n) = n • equationIdealCycle F := by
  rw [equationIdealCycle, equationMultiplicity_pow]
  exact (Finsupp.mapDomain.addMonoidHom associatePrincipalIdeal).map_nsmul _ _

end Nagata.Workers.W30

end

section

/-! Exact divisibility meaning of prime ideal cycle support. -/
namespace Nagata.Workers.W30
open UniqueFactorizationMonoid
noncomputable section
local instance supportAssociateDecidableEq : DecidableEq (Associates TernaryPolynomial) := Classical.decEq _

/-- A principal ideal occurs precisely when its generator is a prime divisor of the equation. -/
theorem span_mem_equationIdealCycle_iff (F f : TernaryPolynomial) (hF : F ≠ 0) :
    Ideal.span ({f} : Set TernaryPolynomial) ∈ (equationIdealCycle F).support ↔
      Prime f ∧ f ∣ F := by
  classical
  rw [Finsupp.mem_support_iff, ← associatePrincipalIdeal_mk,
    equationIdealCycle_coefficient, ← Finsupp.mem_support_iff]
  change Associates.mk f ∈ (factorization (Associates.mk F)).support ↔ _
  rw [support_factorization, Multiset.mem_toFinset,
    mem_normalizedFactors_iff (Associates.mk_ne_zero.mpr hF),
    Associates.prime_mk, Associates.mk_dvd_mk]

end
end Nagata.Workers.W30

end

section

/-! Reconstructing actual finite cycles of nonzero prime principal ideals. -/
namespace Nagata.Workers.W30
noncomputable section

/-- Associate class of a principal ideal; unsupported nonprincipal ideals map to zero. -/
def principalIdealAssociate (I : Ideal TernaryPolynomial) : Associates TernaryPolynomial := by
  classical
  exact if h : I.IsPrincipal then (Ideal.associatesEquivIsPrincipal TernaryPolynomial).symm ⟨I,h⟩
    else 0

theorem associatePrincipalIdeal_principalIdealAssociate (I : Ideal TernaryPolynomial)
    (hI : I.IsPrincipal) : associatePrincipalIdeal (principalIdealAssociate I) = I := by
  classical
  simp only [principalIdealAssociate, dite_eq_left hI, associatePrincipalIdeal]
  exact congrArg Subtype.val ((Ideal.associatesEquivIsPrincipal TernaryPolynomial).apply_symm_apply ⟨I,hI⟩)

theorem principalIdealAssociate_prime (I : Ideal TernaryPolynomial)
    (hI : I.IsPrime) (hI0 : I ≠ ⊥) (hprin : I.IsPrincipal) :
    Prime (principalIdealAssociate I) := by
  obtain ⟨f,hf⟩ := Associates.mk_surjective (principalIdealAssociate I)
  have hid : Ideal.span ({f} : Set TernaryPolynomial) = I := by
    rw [← associatePrincipalIdeal_mk, hf,
      associatePrincipalIdeal_principalIdealAssociate I hprin]
  have hf0 : f ≠ 0 := by
    intro h
    apply hI0
    rw [← hid,h,Ideal.span_singleton_eq_bot.mpr rfl]
  rw [← hf]
  exact Associates.prime_mk.mpr ((Ideal.span_singleton_prime hf0).mp (hid.symm ▸ hI))

/-- Every finite effective cycle on actual nonzero prime principal ideals is the
factor cycle of a nonzero polynomial. -/
theorem exists_equation_of_prime_principal_cycle (D : Ideal TernaryPolynomial →₀ ℕ)
    (hD : ∀ I ∈ D.support, I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal) :
    ∃ F : TernaryPolynomial, F ≠ 0 ∧ equationIdealCycle F = D := by
  classical
  let A := D.mapDomain principalIdealAssociate
  have hA : ∀ a ∈ A.support, Prime a := by
    intro a ha
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
    exact principalIdealAssociate_prime I (hD I hI).1 (hD I hI).2.1 (hD I hI).2.2
  refine ⟨cycleEquation A, cycleEquation_nonzero A hA, ?_⟩
  rw [cycleEquation_idealCycle A hA]
  change (D.mapDomain principalIdealAssociate).mapDomain associatePrincipalIdeal = D
  rw [← Finsupp.mapDomain_comp]
  calc
    D.mapDomain (associatePrincipalIdeal ∘ principalIdealAssociate) = D.mapDomain id :=
      Finsupp.mapDomain_congr (fun I hI =>
        associatePrincipalIdeal_principalIdealAssociate I (hD I hI).2.2)
    _ = D := Finsupp.mapDomain_id

end
end Nagata.Workers.W30

end

section

/-! Homogeneous equations correspond to finite effective cycles of homogeneous prime principal ideals. -/
namespace Nagata.Workers.W30
open MvPolynomial UniqueFactorizationMonoid
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section

/-- Every prime ideal in the cycle of a homogeneous equation is genuinely homogeneous. -/
theorem equationIdealCycle_homogeneous {F : TernaryPolynomial} {d : ℕ}
    (hF : F ≠ 0) (hhom : F.IsHomogeneous d) {I : Ideal TernaryPolynomial}
    (hI : I ∈ (equationIdealCycle F).support) :
    I.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ) := by
  classical
  rw [equationIdealCycle,
    Finsupp.mapDomain_support_of_injective associatePrincipalIdeal_injective] at hI
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨f,rfl⟩ := Associates.mk_surjective a
  have hs : Ideal.span ({f} : Set TernaryPolynomial) ∈ (equationIdealCycle F).support := by
    rw [equationIdealCycle,
      Finsupp.mapDomain_support_of_injective associatePrincipalIdeal_injective]
    exact Finset.mem_image.mpr ⟨Associates.mk f,ha,rfl⟩
  have hdiv := ((span_mem_equationIdealCycle_iff F f hF).mp hs).2
  rw [associatePrincipalIdeal_mk]
  exact span_homogeneous_of_homogeneous (homogeneous_of_dvd hF hhom hdiv)

/-- If every ideal in the factor cycle is homogeneous, the equation is homogeneous. -/
theorem homogeneous_of_equationIdealCycle {F : TernaryPolynomial} (hF : F ≠ 0)
    (hhom : ∀ I ∈ (equationIdealCycle F).support,
      I.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ)) :
    F.IsHomogeneous F.totalDegree := by
  have hfac : ∀ f ∈ factors F, f.IsHomogeneous f.totalDegree := by
    intro f hf
    have hprime : Prime f := prime_of_factor f hf
    have hdiv : f ∣ F := (Multiset.dvd_prod hf).trans (factors_prod hF).dvd
    have hs := (span_mem_equationIdealCycle_iff F f hF).mpr ⟨hprime,hdiv⟩
    exact homogeneous_of_span_homogeneous hprime.ne_zero (hhom _ hs)
  have hprod := homogeneous_multiset_prod (factors F) hfac
  have hFhom := homogeneous_of_associated hprod (factors_prod hF)
  simpa only [hFhom.totalDegree hF] using hFhom

/-- Every finite effective cycle of actual homogeneous nonzero prime principal ideals
comes from a nonzero homogeneous polynomial, with every multiplicity preserved. -/
theorem exists_homogeneous_equation_of_prime_principal_cycle
    (D : Ideal TernaryPolynomial →₀ ℕ)
    (hD : ∀ I ∈ D.support, I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal ∧
      I.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ)) :
    ∃ F : TernaryPolynomial, F ≠ 0 ∧ F.IsHomogeneous F.totalDegree ∧
      equationIdealCycle F = D := by
  obtain ⟨F,hF,hcycle⟩ := exists_equation_of_prime_principal_cycle D
    (fun I hI => ⟨(hD I hI).1,(hD I hI).2.1,(hD I hI).2.2.1⟩)
  refine ⟨F,hF,homogeneous_of_equationIdealCycle hF ?_,hcycle⟩
  intro I hI
  rw [hcycle] at hI
  exact (hD I hI).2.2.2

end
end Nagata.Workers.W30

end

section

/-! Preserve the nonzero-curve and positive-degree conditions in cycle reconstruction. -/
namespace Nagata.Workers.W30
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero finite effective cycle of homogeneous prime principal ideals is
represented by a nonzero homogeneous equation of positive degree, with exact weights. -/
theorem exists_positive_degree_equation_of_homogeneous_cycle
    (D : Ideal TernaryPolynomial →₀ ℕ) (hD0 : D ≠ 0)
    (hD : ∀ I ∈ D.support, I.IsPrime ∧ I ≠ ⊥ ∧ I.IsPrincipal ∧
      I.IsHomogeneous (homogeneousSubmodule (Fin 3) ℂ)) :
    ∃ F : TernaryPolynomial, F ≠ 0 ∧ F.IsHomogeneous F.totalDegree ∧
      0 < F.totalDegree ∧ equationIdealCycle F = D := by
  obtain ⟨F,hF,hhom,hcycle⟩ := exists_homogeneous_equation_of_prime_principal_cycle D hD
  exact ⟨F,hF,hhom,degree_pos_of_equationIdealCycle_ne_zero hF (hcycle.symm ▸ hD0),hcycle⟩

end Nagata.Workers.W30

end

end OAI

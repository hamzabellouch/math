import Mathlib

namespace OAI

namespace PiExponent.RamifiedLocalLength

open IsLocalRing

theorem scalarLocalization_isAtPrime_of_unique_fibre
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    (Rₚ Sₚ : Type*) [CommRing Rₚ] [CommRing Sₚ]
    [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
    [Algebra S Sₚ] [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    [Algebra R Sₚ] [Algebra Rₚ Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
    [Algebra.IsIntegral Rₚ Sₚ]
    (hunique : ∀ Q : Ideal S, Q.IsPrime → p ≤ Q.under R → Q = P) :
    IsLocalization.AtPrime Sₚ P := by
  let M := Algebra.algebraMapSubmonoid S p.primeCompl
  have hmapmax : (P.map (algebraMap S Sₚ)).IsMaximal :=
    IsLocalization.isMaximal_of_isMaximal_disjoint M Sₚ P
      (Ideal.disjoint_primeCompl_of_liesOver P p)
  have huniqueMax : ∀ Q : Ideal Sₚ, Q.IsMaximal → Q = P.map (algebraMap S Sₚ) := by
    intro Q hQ
    let : Q.IsMaximal := hQ
    have hQP : Q.LiesOver (maximalIdeal Rₚ) :=
      (IsLocalization.AtPrime.mem_primesOver_of_isPrime Rₚ Sₚ).2
    let : Q.LiesOver (maximalIdeal Rₚ) := hQP
    have hQp : (Q.under S).LiesOver p :=
      IsLocalization.AtPrime.liesOver_comap_of_liesOver p Rₚ Q
    let : (Q.under S).LiesOver p := hQp
    have hEq : Q.under S = P :=
      hunique (Q.under S) inferInstance (Ideal.over_def (Q.under S) p).le
    calc
      Q = (Q.under S).map (algebraMap S Sₚ) := (IsLocalization.map_under M Sₚ Q).symm
      _ = P.map (algebraMap S Sₚ) := by rw [hEq]
  let : IsLocalRing Sₚ := IsLocalRing.of_unique_max_ideal
    ⟨P.map (algebraMap S Sₚ), hmapmax, huniqueMax⟩
  have hmax : maximalIdeal Sₚ = P.map (algebraMap S Sₚ) :=
    (IsLocalRing.eq_maximalIdeal hmapmax).symm
  have hcomap : (maximalIdeal Sₚ).under S = P := by
    rw [hmax]
    exact IsLocalization.AtPrime.under_map_of_isMaximal S p Sₚ P
  apply IsLocalization.of_le M P.primeCompl
  · intro x hx
    exact fun hmem => Set.disjoint_left.mp (Ideal.disjoint_primeCompl_of_liesOver P p) hx hmem
  · intro r hr
    by_contra hu
    have hm : algebraMap S Sₚ r ∈ maximalIdeal Sₚ := hu
    have hrmem : r ∈ P := by
      rw [← hcomap]
      exact hm
    exact hr hrmem

noncomputable def basis_atPrime_of_unique_fibre
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P)]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R S)
    (hunique : ∀ Q : Ideal S, Q.IsPrime → p ≤ Q.under R → Q = P) :
    Module.Basis ι (Localization.AtPrime p) (Localization.AtPrime P) := by
  let : Module.Finite R S := Module.Finite.of_basis b
  let T := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let : IsLocalization.AtPrime T P :=
    scalarLocalization_isAtPrime_of_unique_fibre p P (Localization.AtPrime p) T hunique
  let e : T ≃ₐ[Localization.AtPrime p] Localization.AtPrime P :=
    ((IsLocalization.algEquiv P.primeCompl T (Localization.AtPrime P)).restrictScalars R).extendScalarsOfIsLocalization
       (Localization.AtPrime p) p.primeCompl
  exact (b.localizationLocalization (Localization.AtPrime p) p.primeCompl T).map e.toLinearEquiv

theorem finrank_atPrime_of_unique_fibre
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P)]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R S)
    (hunique : ∀ Q : Ideal S, Q.IsPrime → p ≤ Q.under R → Q = P) :
    Module.finrank (Localization.AtPrime p) (Localization.AtPrime P) = Fintype.card ι :=
  Module.finrank_eq_card_basis (basis_atPrime_of_unique_fibre p P b hunique)

end PiExponent.RamifiedLocalLength

end OAI

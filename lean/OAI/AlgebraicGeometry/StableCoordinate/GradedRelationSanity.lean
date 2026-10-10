import OAI.AlgebraicGeometry.StableCoordinate.ObstructionDefinitions
import Mathlib

namespace OAI

/-!
# Elementary certificates for the graded hypersurface

The negative-coordinate proof uses localization away from `p`.  This file
establishes that `p` is regular in the actual graded hypersurface quotient,
using the exact relation rather than a domain assumption.  It also supplies
localization-domain descent and nonvanishing certificates for the five
specified homogeneous generators.
-/

noncomputable section

namespace StableCoordinate.GradedRelationSanity

open MvPolynomial

section General

variable {R : Type*} [CommRing R] [DecompositionMonoid R]

/-- A coefficient relatively prime to a principal relation stays regular modulo it. -/
theorem quotient_mem_nonZeroDivisors {h p : R} (hr : IsRelPrime h p) :
    Ideal.Quotient.mk (Ideal.span ({h} : Set R)) p ∈
      nonZeroDivisors (R ⧸ Ideal.span ({h} : Set R)) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hx
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact hr.dvd_of_dvd_mul_left hx

/-- Localization away from such a regular element is injective. -/
theorem quotient_away_injective {h p : R} (hr : IsRelPrime h p)
    (S : Type*) [CommRing S] [Algebra (R ⧸ Ideal.span ({h} : Set R)) S]
    [IsLocalization.Away (Ideal.Quotient.mk (Ideal.span ({h} : Set R)) p) S] :
    Function.Injective (algebraMap (R ⧸ Ideal.span ({h} : Set R)) S) := by
  apply IsLocalization.injective (M := Submonoid.powers
    (Ideal.Quotient.mk (Ideal.span ({h} : Set R)) p)) S
  rintro _ ⟨n, rfl⟩
  exact pow_mem (quotient_mem_nonZeroDivisors hr) n

/-- Domain-ness descends from the localization, without assuming the quotient a domain. -/
theorem quotient_isDomain_of_away_isDomain {h p : R} (hr : IsRelPrime h p)
    (S : Type*) [CommRing S] [Algebra (R ⧸ Ideal.span ({h} : Set R)) S]
    [IsLocalization.Away (Ideal.Quotient.mk (Ideal.span ({h} : Set R)) p) S]
    [IsDomain S] : IsDomain (R ⧸ Ideal.span ({h} : Set R)) :=
  Function.Injective.isDomain (algebraMap (R ⧸ Ideal.span ({h} : Set R)) S)
    (quotient_away_injective hr S)

end General

section Actual

open StableCoordinate.Obstruction

variable (k : Type*) [Field k]

/-- `p` does not divide the displayed highest relation: specialize to (0,0,0,0,1). -/
theorem p_not_dvd_Hstar : ¬ (X 0 : P k 5) ∣ Hstar k := by
  rintro ⟨q, hq⟩
  have h := congrArg (eval (![0, 0, 0, 0, 1] : Fin 5 → k)) hq
  norm_num [Hstar, xP] at h

/-- The highest relation is a nonzero polynomial. -/
theorem Hstar_ne_zero : Hstar k ≠ 0 := by
  intro h
  apply p_not_dvd_Hstar k
  rw [h]
  exact dvd_zero _

/-- The independent variable `p` is irreducible, hence relatively prime to `Hstar`. -/
theorem Hstar_relPrime_p : IsRelPrime (Hstar k) (X 0 : P k 5) := by
  have hp : Irreducible (X 0 : P k 5) := by
    apply (MulEquiv.irreducible_iff (finSuccEquiv k 4)).mp
    rw [finSuccEquiv_X_zero]
    exact Polynomial.irreducible_X
  exact (hp.isRelPrime_iff_not_dvd.mpr (p_not_dvd_Hstar k)).symm

/-- The class of `p` is not a zero divisor in the ACTUAL quotient, before domain descent. -/
theorem gX_zero_mem_nonZeroDivisors : gX k 0 ∈ nonZeroDivisors (G k) :=
  quotient_mem_nonZeroDivisors (Hstar_relPrime_p k)

/-- The canonical map from `G` into its `p`-localization is injective. -/
theorem G_away_injective (S : Type*) [CommRing S] [Algebra (G k) S]
    [IsLocalization.Away (gX k 0) S] : Function.Injective (algebraMap (G k) S) := by
  let : Algebra (P k 5 ⧸ Ideal.span ({Hstar k} : Set (P k 5))) S :=
    ‹Algebra (G k) S›
  let : IsLocalization.Away
      (Ideal.Quotient.mk (Ideal.span ({Hstar k} : Set (P k 5))) (X 0)) S :=
    ‹IsLocalization.Away (gX k 0) S›
  exact quotient_away_injective (Hstar_relPrime_p k) S

/-- A domain certificate for the explicit localized model proves the original `G` a domain. -/
theorem G_isDomain_of_away_isDomain (S : Type*) [CommRing S] [Algebra (G k) S]
    [IsLocalization.Away (gX k 0) S] [IsDomain S] : IsDomain (G k) := by
  exact Function.Injective.isDomain (algebraMap (G k) S) (G_away_injective k S)

end Actual

end StableCoordinate.GradedRelationSanity

end

end OAI

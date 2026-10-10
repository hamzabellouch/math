import OAI.AlgebraicGeometry.StableCoordinate.LocalizationLND
import OAI.AlgebraicGeometry.StableCoordinate.DerivationScalarUpgrade
import OAI.AlgebraicGeometry.StableCoordinate.UnivariateLND
import Mathlib.RingTheory.Localization.Away.Basic

namespace OAI

/-!
# Constant coefficients forced by a locally nilpotent derivation on a chart

This is the complete one-chart part of the §5 rigidity argument.  Starting
with a locally nilpotent derivation of `A`, not with an assumed derivation on
the chart, we localize at an invariant element, transport through a polynomial
chart, and enlarge the coefficient ring to its localization.  The one-variable
LND theorem then forces a vertical coefficient to be constant on the chart.
-/

noncomputable section

namespace StableCoordinate.ChartLNDConstant

open Polynomial LocalizationLND

variable {k R A L S : Type*}
  [CommRing k] [CommRing R] [CommRing A] [CommRing L] [CommRing S]
  [Algebra k R] [Algebra k A] [Algebra k L] [Algebra k S]
  [Algebra A L] [IsScalarTower k A L]
  [Algebra R S]
  [IsDomain S] [CharZero S]
  (i : R →ₐ[k] A) (a : R)
  [IsLocalization.Away (i a) L] [IsLocalization.Away a S]

/-- A chart coordinate coefficient is constant if it occurs in the derivative
of the polynomial chart variable, multiplied by the inverted coefficient.
All localization, transport, scalar-linearity, and nilpotence obligations are
proved from the original derivation and the displayed chart identities. -/
theorem chart_coefficient_eq_C
    (D : Derivation k A A)
    (hD : ∀ x : A, ∃ n : ℕ, ((D : A → A)^[n]) x = 0)
    (hi : ∀ r : R, D (i r) = 0)
    (e : L ≃ₐ[k] S[X])
    (he : ∀ r : R, e (algebraMap A L (i r)) = C (algebraMap R S r))
    (b q : A)
    (hb : e (algebraMap A L b) = X)
    (hDb : D b = i a * q) :
    e (algebraMap A L q) = C ((e (algebraMap A L q)).coeff 0) := by
  have hden : ∀ m : Submonoid.powers (i a), D (m : A) = 0 := by
    rintro ⟨m, hm⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff m (i a)).mp hm
    simp only [Derivation.leibniz_pow, hi a, smul_zero]
  let DL : Derivation k L L :=
    localizeTo D (Submonoid.powers (i a)) hden L
  let E : Derivation k S[X] S[X] := transport DL e
  have hEmap (x : A) :
      E (e (algebraMap A L x)) = e (algebraMap A L (D x)) := by
    dsimp only [E, DL]
    rw [transport_apply, localizeTo_algebraMap]
  have hELND : ∀ p : S[X], ∃ n : ℕ, ((E : S[X] → S[X])^[n]) p = 0 :=
    transport_locallyNilpotent DL e
      (localizeTo_locallyNilpotent D (Submonoid.powers (i a)) hden L hD)
  have hEC : ∀ s : S, E (C s) = 0 := by
    apply DerivationScalarUpgrade.annihilates_localization
      (Submonoid.powers a) E (C : S →+* S[X])
    intro r
    rw [← he r, hEmap, hi, map_zero, map_zero]
  let ES : Derivation S S[X] S[X] := DerivationScalarUpgrade.upgrade E hEC
  have hESLND : ∀ p : S[X], ∃ n : ℕ, ((ES : S[X] → S[X])^[n]) p = 0 :=
    DerivationScalarUpgrade.upgrade_locallyNilpotent E hEC hELND
  have hESX : ES X = C (algebraMap R S a) * e (algebraMap A L q) := by
    change E X = _
    rw [← hb, hEmap, hDb, map_mul, map_mul, he]
  have hconst := UnivariateLND.apply_X_eq_C_of_locallyNilpotent ES hESLND
  rw [hESX, coeff_C_mul, C_mul] at hconst
  exact ((IsLocalization.Away.algebraMap_isUnit (S := S) a).map
    (C : S →+* S[X])).mul_left_cancel hconst

/-- Existential form of the chart-constant conclusion. -/
theorem exists_chart_coefficient
    (D : Derivation k A A)
    (hD : ∀ x : A, ∃ n : ℕ, ((D : A → A)^[n]) x = 0)
    (hi : ∀ r : R, D (i r) = 0)
    (e : L ≃ₐ[k] S[X])
    (he : ∀ r : R, e (algebraMap A L (i r)) = C (algebraMap R S r))
    (b q : A)
    (hb : e (algebraMap A L b) = X)
    (hDb : D b = i a * q) :
    ∃ s : S, e (algebraMap A L q) = C s :=
  ⟨_, chart_coefficient_eq_C i a D hD hi e he b q hb hDb⟩

end StableCoordinate.ChartLNDConstant

end

end OAI

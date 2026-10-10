import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters
import OAI.NumberTheory.PiExponent.LocalAlgebra.TriangularLocalParameters

namespace OAI

noncomputable section
namespace PiExponentSiegel.W10.TriangularLocalParameters

open RingTheory.Sequence
universe u

theorem polynomialMaximal_regularParameters (n : ℕ) :
    ∀ (K : Type u) [Field K] (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal],
      ∃ xs : List (Localization.AtPrime m), xs.length = n ∧
        IsRegular (Localization.AtPrime m) xs ∧
        Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  induction n with
  | zero =>
    intro K _ m _
    exact zeroVariable_parameters K m
  | succ n ih =>
    intro K _ m _
    let A := MvPolynomial (Fin (n + 1)) K
    let f : Polynomial K := firstCoordinatePolynomial K n m
    let : Fact (Irreducible f) := ⟨firstCoordinatePolynomial_irreducible K n m⟩
    let I : Ideal A := PiExponentSiegel.W08.coordinateMinpolyIdeal n f
    have hI : I ≤ m := firstCoordinateIdeal_le K n m
    let e := (PiExponentSiegel.W08.coordinateMinpolyQuotientEquiv n f).toRingEquiv
    let qm := PiExponentSiegel.W23.quotientParameterPrime I m hI
    let p : Ideal (MvPolynomial (Fin n) (AdjoinRoot f)) := qm.map e.toRingHom
    let : p.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := e.toRingHom) (m := qm) e.surjective (by simp)
    obtain ⟨ys, hylen, hyreg, hyspan⟩ := ih (AdjoinRoot f) p
    let J : Ideal (Localization.AtPrime m) := PiExponentSiegel.W23.parameterLocalizedIdeal I m
    let E : (Localization.AtPrime m ⧸ J) ≃+* Localization.AtPrime p :=
      PiExponentSiegel.W23.localizationQuotientParametersEquivTrans I m hI e
    let π : Localization.AtPrime m →+* Localization.AtPrime p :=
      E.toRingHom.comp (Ideal.Quotient.mk J)
    have hπ : Function.Surjective π := E.surjective.comp Ideal.Quotient.mk_surjective
    let g : A := Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) f
    let r : Localization.AtPrime m := algebraMap A (Localization.AtPrime m) g
    have hg : g ≠ 0 := firstCoordinateRelation_ne_zero K n m
    have hr : r ≠ 0 :=
      (FaithfulSMul.algebraMap_eq_zero_iff A (Localization.AtPrime m)).not.mpr hg
    have hker : RingHom.ker π = Ideal.span {r} := by
      rw [show π = E.toRingHom.comp (Ideal.Quotient.mk J) from rfl,
        RingHom.ker_comp_of_injective _ E.injective, Ideal.mk_ker]
      change (Ideal.span {g}).map (algebraMap A (Localization.AtPrime m)) = Ideal.span {r}
      rw [Ideal.map_span, Set.image_singleton]
    obtain ⟨xs, hxlen, hxreg, hxspan⟩ := lift_parameters π hπ r hker
      (regular_element_of_ne_zero r hr) ys hyreg hyspan
    refine ⟨xs, ?_, hxreg, hxspan⟩
    simpa [hylen] using hxlen

end PiExponentSiegel.W10.TriangularLocalParameters

end

end OAI

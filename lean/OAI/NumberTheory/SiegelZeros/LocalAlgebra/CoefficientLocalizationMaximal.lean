import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Smooth.Basic

namespace OAI

namespace SiegelZeros

noncomputable section
namespace WeightedTorusJets.PolynomialLocalResidueResolution

section LocalCoefficientField
variable {K R ι : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]

def residueAlgHom : R →ₐ[K] IsLocalRing.ResidueField R :=
  { IsLocalRing.residue R with commutes' := fun _ => rfl }

theorem isUnit_aeval_of_residue_independent (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i)))
    (f : MvPolynomial ι K) (hf : f ≠ 0) : IsUnit (MvPolynomial.aeval x f) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (MvPolynomial.aeval x f)).mp
  intro hz
  apply hf
  apply hx.eq_zero_of_aeval_eq_zero
  have he := MvPolynomial.comp_aeval_apply (f := x) (residueAlgHom (K := K) (R := R)) f
  exact he.symm.trans hz

def rationalCoefficientMap (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i))) :
    FractionRing (MvPolynomial ι K) →+* R :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial ι K))
    (S := FractionRing (MvPolynomial ι K)) (g := (MvPolynomial.aeval x).toRingHom)
    (fun f => isUnit_aeval_of_residue_independent x hx f (nonZeroDivisors.coe_ne_zero f))

@[simp] theorem rationalCoefficientMap_polynomial (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i)))
    (f : MvPolynomial ι K) :
    rationalCoefficientMap x hx
      (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f) =
        MvPolynomial.aeval x f :=
  IsLocalization.lift_eq _ _

theorem rationalCoefficientMap_injective (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i))) :
    Function.Injective (rationalCoefficientMap x hx) :=
  (rationalCoefficientMap x hx).injective

theorem residue_rationalCoefficientMap_injective (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i))) :
    Function.Injective ((IsLocalRing.residue R).comp (rationalCoefficientMap x hx)) :=
  ((IsLocalRing.residue R).comp (rationalCoefficientMap x hx)).injective

end LocalCoefficientField

section PolynomialPrime
variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

abbrev LocalPolynomialRing := Localization.AtPrime Q
abbrev LocalPolynomialResidue := Q.ResidueField

theorem actual_residue_field : LocalPolynomialResidue K n Q =
    IsLocalRing.ResidueField (LocalPolynomialRing K n Q) := rfl

def residueCoordinate (i : Fin n) : LocalPolynomialResidue K n Q :=
  algebraMap (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) (MvPolynomial.X i)

theorem localPolynomial_essFiniteType :
    Algebra.EssFiniteType K (LocalPolynomialRing K n Q) := by infer_instance

theorem localResidue_essFiniteType :
    Algebra.EssFiniteType K (LocalPolynomialResidue K n Q) := by
  exact Algebra.EssFiniteType.comp K (MvPolynomial (Fin n) K) _

theorem exists_separating_residue_basis [PerfectField K] :
    ∃ s : Finset (LocalPolynomialResidue K n Q),
      IsTranscendenceBasis K ((↑) : s → LocalPolynomialResidue K n Q) ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (s : Set (LocalPolynomialResidue K n Q)))
        (LocalPolynomialResidue K n Q) := by
  let := localResidue_essFiniteType K n Q
  exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField K _

theorem exists_local_lifts (s : Finset (LocalPolynomialResidue K n Q)) :
    ∃ x : s → LocalPolynomialRing K n Q,
      ∀ i, IsLocalRing.residue (LocalPolynomialRing K n Q) (x i) = (i : LocalPolynomialResidue K n Q) := by
  classical
  choose x hx using fun i : s =>
    IsLocalRing.residue_surjective (R := LocalPolynomialRing K n Q) (i : LocalPolynomialResidue K n Q)
  exact ⟨x, hx⟩

theorem residue_coordinate_equations
    (s : Finset (LocalPolynomialResidue K n Q))
    [Algebra.IsSeparable
      (IntermediateField.adjoin K (s : Set (LocalPolynomialResidue K n Q)))
      (LocalPolynomialResidue K n Q)] (i : Fin n) :
    let F := IntermediateField.adjoin K (s : Set (LocalPolynomialResidue K n Q))
    let a := residueCoordinate K n Q i
    (minpoly F a).Monic ∧ Polynomial.aeval a (minpoly F a) = 0 ∧
      Polynomial.aeval a (Polynomial.derivative (minpoly F a)) ≠ 0 := by
  dsimp only
  refine ⟨minpoly.monic (Algebra.IsSeparable.isIntegral _ _), minpoly.aeval _ _, ?_⟩
  exact (Algebra.IsSeparable.isSeparable _ _).aeval_derivative_ne_zero (minpoly.aeval _ _)

end PolynomialPrime
end WeightedTorusJets.PolynomialLocalResidueResolution

end

noncomputable section
namespace WeightedTorusJets.PolynomialLocalResidueResolution

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

lemma residueCoordinate_aeval (f : MvPolynomial (Fin n) K) :
    MvPolynomial.aeval (residueCoordinate K n Q) f =
      algebraMap (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) f := by
  have he : MvPolynomial.aeval (residueCoordinate K n Q) =
      IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) := by
    ext i
    simp only [MvPolynomial.aeval_X]
    rfl
  exact AlgHom.congr_fun he f

theorem residueCoordinate_adjoin_top :
    IntermediateField.adjoin K (Set.range (residueCoordinate K n Q)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a, b, hb, hz⟩ :=
    IsFractionRing.div_surjective (MvPolynomial (Fin n) K ⧸ Q) z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (IntermediateField.mem_adjoin_range_iff K (residueCoordinate K n Q) z).mpr
  refine ⟨f, g, ?_⟩
  simpa only [residueCoordinate_aeval,
    Ideal.algebraMap_quotient_residueField_mk] using hz.symm

theorem exists_coordinate_residue_basis :
    ∃ t : Set (LocalPolynomialResidue K n Q),
      t.Finite ∧ t ⊆ Set.range (residueCoordinate K n Q) ∧
      IsTranscendenceBasis K ((↑) : t → LocalPolynomialResidue K n Q) := by
  have htop := residueCoordinate_adjoin_top K n Q
  let : Algebra.IsAlgebraic
      (Algebra.adjoin K (Set.range (residueCoordinate K n Q)))
      (LocalPolynomialResidue K n Q) := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  obtain ⟨t, ht, htb⟩ :=
    exists_isTranscendenceBasis_subset (R := K) (Set.range (residueCoordinate K n Q))
  exact ⟨t, (Set.finite_range _).subset ht, ht, htb⟩

theorem exists_coordinate_basis_indices :
    ∃ (t : Set (LocalPolynomialResidue K n Q)) (j : t → Fin n),
      t.Finite ∧ Function.Injective j ∧
      (∀ a, residueCoordinate K n Q (j a) = (a : LocalPolynomialResidue K n Q)) ∧
      IsTranscendenceBasis K ((↑) : t → LocalPolynomialResidue K n Q) := by
  classical
  obtain ⟨t, hfin, ht, htb⟩ := exists_coordinate_residue_basis K n Q
  choose j hj using fun a : t => ht a.property
  refine ⟨t, j, hfin, ?_, hj, htb⟩
  intro a b hab
  apply Subtype.ext
  exact (hj a).symm.trans ((congrArg (residueCoordinate K n Q) hab).trans (hj b))

end WeightedTorusJets.PolynomialLocalResidueResolution

end

noncomputable section
namespace WeightedTorusJets.PolynomialLocalResidueResolution
open scoped IntermediateField.algebraAdjoinAdjoin

variable {K R ι : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
variable (x : ι → R)
variable (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i)))

def rationalResidueEquiv : FractionRing (MvPolynomial ι K) ≃ₐ[K]
    IntermediateField.adjoin K (Set.range (fun i => IsLocalRing.residue R (x i))) :=
  IsFractionRing.algEquivOfAlgEquiv hx.aevalEquiv

@[simp] theorem rationalResidueEquiv_polynomial (f : MvPolynomial ι K) :
    ((rationalResidueEquiv x hx
      (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f)) :
        IsLocalRing.ResidueField R) =
      MvPolynomial.aeval (fun i => IsLocalRing.residue R (x i)) f := by
  rw [rationalResidueEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

def residueCoefficientSection :
    IntermediateField.adjoin K (Set.range (fun i => IsLocalRing.residue R (x i))) →+* R :=
  (rationalCoefficientMap x hx).comp (rationalResidueEquiv x hx).symm.toRingHom

theorem residueCoefficientSection_residue :
    (IsLocalRing.residue R).comp (residueCoefficientSection x hx) =
      (IntermediateField.adjoin K
        (Set.range (fun i => IsLocalRing.residue R (x i)))).val.toRingHom := by
  have h : (IsLocalRing.residue R).comp (rationalCoefficientMap x hx) =
      ((IntermediateField.adjoin K
        (Set.range (fun i => IsLocalRing.residue R (x i)))).val.toRingHom).comp
          (rationalResidueEquiv x hx).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial ι K))
    apply RingHom.ext
    intro f
    change IsLocalRing.residue R
      (rationalCoefficientMap x hx (algebraMap _ (FractionRing (MvPolynomial ι K)) f)) =
      ((rationalResidueEquiv x hx (algebraMap _ (FractionRing (MvPolynomial ι K)) f)) :
        IsLocalRing.ResidueField R)
    rw [rationalCoefficientMap_polynomial, rationalResidueEquiv_polynomial]
    exact MvPolynomial.comp_aeval_apply (f := x) (residueAlgHom (K := K) (R := R)) f
  apply RingHom.ext
  intro a
  have ha := RingHom.congr_fun h ((rationalResidueEquiv x hx).symm a)
  change IsLocalRing.residue R
    (rationalCoefficientMap x hx ((rationalResidueEquiv x hx).symm a)) = (a : IsLocalRing.ResidueField R)
  change IsLocalRing.residue R
    (rationalCoefficientMap x hx ((rationalResidueEquiv x hx).symm a)) =
      ((rationalResidueEquiv x hx ((rationalResidueEquiv x hx).symm a)) :
        IsLocalRing.ResidueField R) at ha
  rw [AlgEquiv.apply_symm_apply] at ha
  exact ha

end WeightedTorusJets.PolynomialLocalResidueResolution

end

noncomputable section
namespace WeightedTorusJets.PolynomialLocalResidueResolution

section MaximalKernel
variable {F A L : Type*} [Field F] [CommRing A] [Field L]
variable [Algebra F A] [Algebra F L] [Algebra.IsAlgebraic F L]

theorem algebraic_field_kernel_isMaximal (f : A →ₐ[F] L) :
    (RingHom.ker f.toRingHom).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Subalgebra.isField_of_algebraic f.range)
    (Ideal.quotientKerEquivRange f).toRingEquiv.toMulEquiv

end MaximalKernel

section Localization
variable {R A L : Type*} [CommRing R] [CommRing A] [CommRing L]
variable (M : Submonoid R) [Algebra R A] [IsLocalization M A]

include M in

theorem extended_kernel_eq (f : R →+* L) (g : A →+* L)
    (h : g.comp (algebraMap R A) = f) :
    (RingHom.ker f).map (algebraMap R A) = RingHom.ker g := by
  have hk : (RingHom.ker g).comap (algebraMap R A) = RingHom.ker f := by
    ext x
    change g (algebraMap R A x) = 0 ↔ f x = 0
    have he := RingHom.congr_fun h x
    change g (algebraMap R A x) = f x at he
    rw [he]
  rw [← hk]
  exact IsLocalization.map_under M A (RingHom.ker g)

end Localization
end WeightedTorusJets.PolynomialLocalResidueResolution

end

end SiegelZeros

end OAI

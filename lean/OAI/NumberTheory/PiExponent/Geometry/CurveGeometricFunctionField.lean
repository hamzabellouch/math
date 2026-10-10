import Mathlib.RingTheory.Spectrum.Prime.Topology
import OAI.NumberTheory.PiExponent.Ampleness.AffineFunctionFieldCompatibility
import OAI.NumberTheory.PiExponent.Geometry.CurveParameterFinite
import OAI.NumberTheory.PiExponent.LocalAlgebra.AffineTranscendenceDimension

namespace OAI

noncomputable section
namespace PiExponent.CurveGeometricFunctionField

open CategoryTheory AlgebraicGeometry

variable (k A E : Type*) [Field k] [CommRing A] [IsDomain A] [Field E]
  [Algebra k A] [Algebra k E] [Algebra A E] [IsScalarTower k A E]
  [IsFractionRing A E]

omit [IsDomain A] in
theorem fractionField_essFiniteType [Algebra.FiniteType k A] :
    Algebra.EssFiniteType k E := by
  let : Algebra.EssFiniteType A E :=
    Algebra.EssFiniteType.of_isLocalization E (nonZeroDivisors A)
  exact Algebra.EssFiniteType.comp k A E

theorem fractionField_trdeg_eq_one [Algebra.FiniteType k A]
    (hdim : ringKrullDim A = 1) : Algebra.trdeg k E = 1 := by
  let : FaithfulSMul A E :=
    (faithfulSMul_iff_algebraMap_injective A E).mpr (IsFractionRing.injective A E)
  have hd : (Algebra.trdeg k A).toNat = 1 := by
    rw [PiExponentJets.W24.finiteType_domain_krullDim_eq_trdeg k A] at hdim
    exact_mod_cast hdim
  have he := PiExponentJets.W24.localization_trdeg_toNat_eq k A E
    (nonZeroDivisors A)
  exact Cardinal.toNat_eq_one.mp (he.symm.trans hd)

def coordinates {ι : Type*} (φ : MvPolynomial ι k →ₐ[k] A) : ι → E :=
  fun i => algebraMap A E (φ (MvPolynomial.X i))

omit [IsDomain A] in
theorem adjoin_coordinates_eq_top {ι : Type*}
    (φ : MvPolynomial ι k →ₐ[k] A) (hφ : Function.Surjective φ) :
    IntermediateField.adjoin k (Set.range (coordinates k A E φ)) = ⊤ := by
  let x := coordinates k A E φ
  let K := IntermediateField.adjoin k (Set.range x)
  have hψ : (IsScalarTower.toAlgHom k A E).comp φ = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [x, coordinates]
  have hmem (a : A) : algebraMap A E a ∈ K := by
    obtain ⟨p, rfl⟩ := hφ a
    apply IntermediateField.algebra_adjoin_le_adjoin k (Set.range x)
    rw [← MvPolynomial.aeval_range]
    refine ⟨p, ?_⟩
    exact (congrArg (fun f : MvPolynomial ι k →ₐ[k] E => f p) hψ).symm
  apply top_le_iff.mp
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A z
  exact K.div_mem (hmem a) (hmem b)

theorem of_surjective_coordinates {ι : Type*} [Finite ι]
    (φ : MvPolynomial ι k →ₐ[k] A) (hφ : Function.Surjective φ)
    (hdim : ringKrullDim A = 1) :
    Algebra.EssFiniteType k E ∧ Algebra.trdeg k E = 1 ∧
      IntermediateField.adjoin k (Set.range (coordinates k A E φ)) = ⊤ := by
  let : Algebra.FiniteType k A := Algebra.FiniteType.of_surjective φ hφ
  exact ⟨fractionField_essFiniteType k A E,
    fractionField_trdeg_eq_one k A E hdim, adjoin_coordinates_eq_top k A E φ hφ⟩

theorem finite_over_every_parameter [Algebra.FiniteType k A]
    (hdim : ringKrullDim A = 1) :
    ∀ f : E, Transcendental k f →
      FiniteDimensional (IntermediateField.adjoin k {f}) E := by
  let := fractionField_essFiniteType k A E
  exact CurveParameterFinite.finite_over_every_parameter k E
    (fractionField_trdeg_eq_one k A E hdim)

omit [IsDomain A] in
theorem ringKrullDim_eq_one_of_affine_iso
    (X : Scheme) (e : X ≅ Spec (.of A)) (hdim : topologicalKrullDim X = 1) :
    ringKrullDim A = 1 := by
  have h := e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
  change topologicalKrullDim X = topologicalKrullDim (PrimeSpectrum A) at h
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  exact h.symm.trans hdim

theorem of_affine_curve {ι : Type*} [Finite ι]
    (X : Scheme) (e : X ≅ Spec (.of A)) (hdim : topologicalKrullDim X = 1)
    (φ : MvPolynomial ι k →ₐ[k] A) (hφ : Function.Surjective φ) :
    Algebra.EssFiniteType k E ∧ Algebra.trdeg k E = 1 ∧
      IntermediateField.adjoin k (Set.range (coordinates k A E φ)) = ⊤ :=
  of_surjective_coordinates k A E φ hφ
    (ringKrullDim_eq_one_of_affine_iso A X e hdim)

@[instance_reducible] def intrinsicSectionAlgebra (X : Scheme) [IsIntegral X] :
    Algebra Γ(X, ⊤) X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact (X.germToFunctionField ⊤).hom.toAlgebra

attribute [local instance] intrinsicSectionAlgebra

@[instance_reducible] def intrinsicFunctionFieldAlgebra (k : Type*) [Field k]
    (X : Scheme) [IsIntegral X] [Algebra k Γ(X, ⊤)] :
    Algebra k X.functionField :=
  ((algebraMap Γ(X, ⊤) X.functionField).comp (algebraMap k Γ(X, ⊤))).toAlgebra

theorem intrinsic_functionField (k : Type*) [Field k]
    (X : Scheme) [IsIntegral X] [IsAffine X] [Algebra k Γ(X, ⊤)]
    {ι : Type*} [Finite ι] (hdim : topologicalKrullDim X = 1)
    (φ : MvPolynomial ι k →ₐ[k] Γ(X, ⊤)) (hφ : Function.Surjective φ) :
    letI : Algebra k X.functionField := intrinsicFunctionFieldAlgebra k X
    Algebra.EssFiniteType k X.functionField ∧ Algebra.trdeg k X.functionField = 1 ∧
      IntermediateField.adjoin k
        (Set.range (coordinates k Γ(X, ⊤) X.functionField φ)) = ⊤ := by
  let : Algebra k X.functionField := intrinsicFunctionFieldAlgebra k X
  let : IsScalarTower k Γ(X, ⊤) X.functionField :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let : IsFractionRing Γ(X, ⊤) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X (⊤ : X.Opens) (isAffineOpen_top X)
  exact of_affine_curve k Γ(X, ⊤) X.functionField X X.isoSpec hdim φ hφ

end PiExponent.CurveGeometricFunctionField

end

end OAI

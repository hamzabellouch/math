/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

import OAI.AlgebraicGeometry.SurfaceCones.ModuleDepth
import OAI.AlgebraicGeometry.SurfaceCones.AffineModelRank

namespace OAI


noncomputable section
namespace ExplicitCone
open AlgebraicGeometry CategoryTheory

/-- The double dual of the pullback of a depth-three module has a nonzero torsion-free restriction to the exceptional affine chart. -/
theorem completedGlobalRestriction_of_depth_three
    (M : ModuleCat.{0} completedRing) [Module.Finite completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth completedRing M = 3) :
    Module.IsTorsionFree (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedGlobalRestrictionSections M) ∧
    0 < Module.finrank (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedGlobalRestrictionSections M) := by
  let : Module.IsTorsionFree completedRing M :=
    (module_properties_from_depth_three M hdepth).1
  exact ⟨completedGlobalRestriction_torsionFree M, completedGlobalRestriction_rank_pos M⟩

/-- The global double-dual extension is coherent and has positive-rank torsion-free restriction to the exceptional affine chart. -/
theorem actual_extension_of_CM_module
    (M : Type) [AddCommGroup M] [Module completedRing M]
    [Module.Finite completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth completedRing M = 3) :
    (completedModelE (ModuleCat.of completedRing M)).IsFinitePresentation ∧
    (∀ U : completedBlowup.Opens,
      @Module.IsTorsionFree Γ(completedBlowup, U)
        ((completedModelE (ModuleCat.of completedRing M)).val.obj (Opposite.op U)) _ _
        ((completedModelE (ModuleCat.of completedRing M)).val.obj (Opposite.op U)).isModule) ∧
    Module.IsTorsionFree (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedGlobalRestrictionSections (ModuleCat.of completedRing M)) ∧
    0 < Module.finrank (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedGlobalRestrictionSections (ModuleCat.of completedRing M)) := by
  exact ⟨completedModelE_coherent _, completedModelE_torsionFree _,
    completedGlobalRestriction_of_depth_three _ hdepth⟩
end ExplicitCone


open scoped TensorProduct
namespace PrincipalDivisorGeneric
variable {R M : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M]

/-- The generic local ring of a nonzero prime Cartier divisor really is a
DVR. The ambient ring need not already be assumed regular. -/
lemma local_dvr (t : R) (ht : t ≠ 0) [(Ideal.span ({t} : Set R)).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span ({t} : Set R))) := by
  let p := Ideal.span ({t} : Set R)
  let A := Localization.AtPrime p
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {algebraMap R A t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A]
    change Ideal.map (algebraMap R A) (Ideal.span {t}) = _
    rw [Ideal.map_span, Set.image_singleton]
  have hprincipal : (IsLocalRing.maximalIdeal A).IsPrincipal := by
    rw [hmax]
    infer_instance
  let : IsPrincipalIdealRing A :=
    (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 5 1 |>.mp hprincipal
  refine { not_a_field' := ?_ }
  rw [hmax, ne_eq, Ideal.span_singleton_eq_bot]
  simpa only [map_zero] using
    (IsLocalization.injective A p.primeCompl_le_nonZeroDivisors).ne ht

/-- A finite torsion-free sheaf therefore has a free stalk at the divisor's
generic point, as used in the manuscript's actual extension argument. -/
lemma localized_free (t : R) (ht : t ≠ 0) [(Ideal.span ({t} : Set R)).IsPrime]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.Free (Localization.AtPrime (Ideal.span ({t} : Set R)))
      (LocalizedModule (Ideal.span ({t} : Set R)).primeCompl M) := by
  let := local_dvr t ht
  infer_instance

omit [IsNoetherianRing R] in
/-- Localization at the generic point preserves the module rank. -/
lemma localized_rank (p : Ideal R) [p.IsPrime] :
    Module.finrank (Localization.AtPrime p) (LocalizedModule p.primeCompl M) =
      Module.finrank R M := by
  rw [IsLocalization.finrank_eq (Localization.AtPrime p) p.primeCompl
    p.primeCompl_le_nonZeroDivisors]
  exact IsLocalizedModule.finrank_eq p.primeCompl (LocalizedModule.mkLinearMap _ _)
    p.primeCompl_le_nonZeroDivisors

/-- A genuine open neighborhood (not only a stalk) of the generic divisor
point has a free module, with the same generic rank as the ambient module. -/
lemma exists_free_neighborhood (t : R) (ht : t ≠ 0)
    [(Ideal.span ({t} : Set R)).IsPrime] [Module.Finite R M] [Module.IsTorsionFree R M] :
    ∃ s : R, s ∉ Ideal.span ({t} : Set R) ∧
      Module.Free (Localization (.powers s)) (LocalizedModule.Away s M) ∧
      Module.finrank (Localization (.powers s)) (LocalizedModule.Away s M) =
        Module.finrank R M := by
  let p := Ideal.span ({t} : Set R)
  let := localized_free (M := M) t ht
  have := Module.finitePresentation_of_finite R M
  obtain ⟨s, hs, hfree, hrank⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers p.primeCompl
      (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p)
  exact ⟨s, hs, hfree, hrank.trans (localized_rank p)⟩
/-- The generic fiber on the actual principal divisor has exactly the
ambient generic rank, because its generic local ring is a DVR. -/
lemma residue_rank (t : R) (ht : t ≠ 0)
    [(Ideal.span ({t} : Set R)).IsPrime] [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.finrank (Ideal.span ({t} : Set R)).ResidueField
      ((Ideal.span ({t} : Set R)).ResidueField ⊗[R] M) = Module.finrank R M := by
  let p := Ideal.span ({t} : Set R)
  let A := Localization.AtPrime p
  let K := p.ResidueField
  let L := LocalizedModule p.primeCompl M
  let := localized_free (M := M) t ht
  let e : K ⊗[R] M ≃ₗ[K] K ⊗[A] L :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A K K M).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K)
        (LocalizedModule.isBaseChange p.primeCompl M).equiv)
  change Module.finrank K (K ⊗[R] M) = _
  rw [e.finrank_eq, Module.finrank_baseChange]
  exact localized_rank p

lemma quotient_rank (t : R) (ht : t ≠ 0)
    [(Ideal.span ({t} : Set R)).IsPrime] [Module.Finite R M] [Module.IsTorsionFree R M] :
    Module.finrank (R ⧸ Ideal.span ({t} : Set R))
      ((R ⧸ Ideal.span ({t} : Set R)) ⊗[R] M) = Module.finrank R M := by
  let p := Ideal.span ({t} : Set R)
  let Q := R ⧸ p
  let K := p.ResidueField
  let N := Q ⊗[R] M
  have hloc : Module.finrank K (K ⊗[Q] N) = Module.finrank Q N := by
    rw [IsLocalization.finrank_eq K (nonZeroDivisors Q) le_rfl]
    exact IsLocalizedModule.finrank_eq (nonZeroDivisors Q)
      (TensorProduct.mk Q K N 1) le_rfl
  change Module.finrank Q N = _
  rw [← hloc,
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R Q K K M).finrank_eq]
  exact residue_rank t ht

end PrincipalDivisorGeneric


end


noncomputable section
open scoped TensorProduct
open TensorProduct
namespace DomainModuleRank
variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

omit [IsDomain R] in
lemma fraction_rank :
    Module.finrank (FractionRing R) (FractionRing R ⊗[R] M) = Module.finrank R M := by
  rw [IsLocalization.finrank_eq (FractionRing R) (nonZeroDivisors R) le_rfl]
  exact IsLocalizedModule.finrank_eq (nonZeroDivisors R)
    (TensorProduct.mk R (FractionRing R) M 1) le_rfl

/-- The generic rank of an honest dual is the original generic rank.
Finite presentation supplies Hom-localization, not a false global freeness. -/
lemma dual_rank [Module.FinitePresentation R M] :
    Module.finrank R (Module.Dual R M) = Module.finrank R M := by
  let K := FractionRing R
  let e : K ⊗[R] Module.Dual R M ≃ₗ[K] Module.Dual K (K ⊗[R] M) :=
    (Module.FinitePresentation.isBaseChange_map R M R K).equiv.trans
      ((AlgebraTensorModule.rid R K K).congrRight)
  rw [← fraction_rank (M := Module.Dual R M), e.finrank_eq,
    Subspace.dual_finrank_eq, fraction_rank]

/-- Injective scalar extension preserves generic rank even if it is not
flat. The comparison is made over the two honest fraction fields. -/
lemma baseChange_rank (B : Type*) [CommRing B] [IsDomain B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B)) :
    Module.finrank B (B ⊗[R] M) = Module.finrank R M := by
  let K := FractionRing R
  let L := FractionRing B
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr
    ((IsFractionRing.injective B L).comp hinj)
  let : Algebra K L := FractionRing.liftAlgebra R L
  let : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  let e : L ⊗[B] (B ⊗[R] M) ≃ₗ[L] L ⊗[K] (K ⊗[R] M) :=
    (AlgebraTensorModule.cancelBaseChange R B L L M).trans
      (AlgebraTensorModule.cancelBaseChange R K L L M).symm
  rw [← fraction_rank (R := B) (M := B ⊗[R] M), e.finrank_eq,
    Module.finrank_baseChange, fraction_rank]

lemma doubleDual_rank [IsNoetherianRing R] [Module.Finite R M] :
    Module.finrank R (Module.Dual R (Module.Dual R M)) = Module.finrank R M := by
  have := Module.finitePresentation_of_finite R M
  have : IsNoetherian R (Module.Dual R M) := isNoetherian_linearMap R R M
  have : Module.Finite R (Module.Dual R M) := ⟨IsNoetherian.noetherian ⊤⟩
  have := Module.finitePresentation_of_finite R (Module.Dual R M)
  rw [dual_rank, dual_rank]

lemma doubleDual_baseChange_rank [Module.Finite R M]
    (B : Type*) [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B)) :
    Module.finrank B (Module.Dual B (Module.Dual B (B ⊗[R] M))) =
      Module.finrank R M := by
  rw [doubleDual_rank, baseChange_rank B hinj]

end DomainModuleRank


end


noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct
namespace CoherentModelActual
open CoherentDual Scheme.Modules
variable {A B : CommRingCat.{0}} [IsNoetherianRing B]
  (f : A ⟶ B) (M : ModuleCat A) [Module.Finite A M]
  [IsDomain A] [IsDomain B]

/-- Exact generic rank of the genuine double-dual model on a prime Cartier
divisor. No flatness of the model over the source and no freeness of M is
assumed. The source's original rank is retained through both duals and
restriction at the generic divisor point. -/
theorem affineE_cartier_rank_eq (hf : Function.Injective f)
    (t : B) (ht : t ≠ 0) [(Ideal.span ({t} : Set B)).IsPrime] :
    let q : B ⟶ CommRingCat.of (B ⧸ Ideal.span ({t} : Set B)) :=
      CommRingCat.ofHom (Ideal.Quotient.mk _)
    Module.finrank (B ⧸ Ideal.span ({t} : Set B))
      ((moduleSpecΓFunctor (R := CommRingCat.of (B ⧸ Ideal.span ({t} : Set B)))).obj
        ((Scheme.Modules.pullback (Spec.map q)).obj (E (Spec.map f) M))) =
      Module.finrank A M := by
  let : Algebra A B := f.hom.toAlgebra
  let p := Ideal.span ({t} : Set B)
  let q : B ⟶ CommRingCat.of (B ⧸ p) := CommRingCat.ofHom (Ideal.Quotient.mk p)
  let N := Module.Dual B (Module.Dual B (affineModule f M))
  have : IsNoetherian B N := isNoetherian_linearMap B B (Module.Dual B (affineModule f M))
  have : Module.Finite B N := ⟨IsNoetherian.noetherian ⊤⟩
  dsimp only
  rw [(affineEPullbackGammaIso f M q).toLinearEquiv.finrank_eq]
  change Module.finrank (B ⧸ p) ((B ⧸ p) ⊗[B] N) = _
  rw [PrincipalDivisorGeneric.quotient_rank t ht]
  exact DomainModuleRank.doubleDual_baseChange_rank B hf
end CoherentModelActual

end


noncomputable section
namespace ExplicitCone
open AlgebraicGeometry CategoryTheory

/-- Source paper.tex339–340: the generic rank of the actual restriction
equals the ORIGINAL completed-cone module rank, not only an unspecified
positive integer. This holds for arbitrary finite ungraded modules. -/
theorem completedChartRestriction_rank_eq (M : ModuleCat.{0} completedRing)
    [Module.Finite completedRing M] :
    Module.finrank (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedChartRestrictionSections M) = Module.finrank completedRing M := by
  let := actualCompletion_noetherian
  exact CoherentModelActual.affineE_cartier_rank_eq completedChartBaseMap M
    completedChartBaseMap_injective completedBlowupParameter completedBlowupParameter_ne_zero

/-- The comparison is made for the globally constructed coherent double
 dual E, using its honest restriction isomorphism with the affine model. -/
theorem completedGlobalRestriction_rank_eq (M : ModuleCat.{0} completedRing)
    [Module.Finite completedRing M] :
    Module.finrank (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedGlobalRestrictionSections M) = Module.finrank completedRing M := by
  rw [(completedGlobalRestrictionIso M).toLinearEquiv.finrank_eq]
  exact completedChartRestriction_rank_eq M

/-- The coherent double-dual extension has torsion-free restriction with the same generic rank as the original module. -/
theorem actual_extension_rank_of_CM_module
    (M : Type) [AddCommGroup M] [Module completedRing M]
    [Module.Finite completedRing M] [Nontrivial M]
    (hdepth : SmallCM.localDepth completedRing M = 3) :
    (completedModelE (ModuleCat.of completedRing M)).IsFinitePresentation ∧
    (∀ U : completedBlowup.Opens,
      @Module.IsTorsionFree Γ(completedBlowup, U)
        ((completedModelE (ModuleCat.of completedRing M)).val.obj (Opposite.op U)) _ _
        ((completedModelE (ModuleCat.of completedRing M)).val.obj (Opposite.op U)).isModule) ∧
    Module.IsTorsionFree (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedGlobalRestrictionSections (ModuleCat.of completedRing M)) ∧
    (Module.finrank (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
      (completedGlobalRestrictionSections (ModuleCat.of completedRing M)) =
        Module.finrank completedRing M) ∧ 0 < Module.finrank completedRing M := by
  refine ⟨completedModelE_coherent _, completedModelE_torsionFree _,
    completedGlobalRestriction_torsionFree _, completedGlobalRestriction_rank_eq _, ?_⟩
  exact (module_properties_from_depth_three M hdepth).2.1

end ExplicitCone


open scoped TensorProduct
namespace DomainModuleRank
variable {A R M : Type*} [CommRing A] [IsDomain A] [CommRing R] [IsDomain R]
  [Algebra A R] [FaithfulSMul A R] [Algebra.IsAlgebraic A R]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower A R M]

/-- The field-degree rank formula for arbitrary modules in a finite-domain
extension. Neither the ring extension nor the module is assumed free. -/
lemma tower_rank :
    Module.finrank A R * Module.finrank R M = Module.finrank A M := by
  let K := FractionRing A
  let L := FractionRing R
  let : Algebra K L := FractionRing.liftAlgebra A L
  let : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  let N := L ⊗[R] M
  let j : M →ₗ[R] N := TensorProduct.mk R L M 1
  have : IsLocalizedModule (nonZeroDivisors A) (j.restrictScalars A) :=
    IsLocalizedModule.restrictScalars (nonZeroDivisors A) j
  calc
    Module.finrank A R * Module.finrank R M =
        Module.finrank K L * Module.finrank L N := by
      rw [IsFractionRing.finrank_eq A K R L, fraction_rank]
    _ = Module.finrank K N := Module.finrank_mul_finrank K L N
    _ = Module.finrank A N := IsFractionRing.finrank_right_eq A K N
    _ = Module.finrank A M := IsLocalizedModule.finrank_eq (nonZeroDivisors A)
      (j.restrictScalars A) le_rfl
end DomainModuleRank

end


noncomputable section
namespace ExplicitCone
open AlgebraicGeometry CategoryTheory

/-- The free A-module rank of an arbitrary hypothetical CM module is the
normalization degree times the rank of its TRUE exceptional restriction.
This is an equality deduced from the constructed rings/maps/sheaf; the
source surface equality deg(f)=H² remains a geometric identification. -/
theorem completed_exceptional_rank_formula
    (M : Type) [AddCommGroup M] [Module completedRing M] [Module.Finite completedRing M] :
    letI := Module.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
    Module.finrank (MvPowerSeries (Fin 3) ℂ) M =
      Module.finrank (MvPowerSeries (Fin 3) ℂ) completedRing *
        Module.finrank (completedBlowupChart ⧸ Ideal.span {completedBlowupParameter})
          (completedGlobalRestrictionSections (ModuleCat.of completedRing M)) := by
  let : IsDomain (MvPowerSeries (Fin 3) ℂ) := NoZeroDivisors.to_isDomain _
  let := Module.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
  let : IsScalarTower (MvPowerSeries (Fin 3) ℂ) completedRing M :=
    IsScalarTower.restrictScalars (MvPowerSeries (Fin 3) ℂ) completedRing M
  rw [completedGlobalRestriction_rank_eq]
  exact DomainModuleRank.tower_rank.symm

/-- Positivity of the normalization degree, proved for the actual finite
injective three-parameter power-series map. -/
lemma completed_parameter_degree_pos :
    0 < Module.finrank (MvPowerSeries (Fin 3) ℂ) completedRing := by
  let : IsDomain (MvPowerSeries (Fin 3) ℂ) := NoZeroDivisors.to_isDomain _
  exact Module.finrank_pos
end ExplicitCone


open AlgebraicGeometry CategoryTheory
namespace GradedPolynomialMap
variable {k B σ : Type*} [CommRing k] [CommRing B] [Algebra k B]
  (ℬ : ℕ → Submodule k B) [GradedAlgebra ℬ]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma homogeneous_pow_le (n : ℕ) : (ℬ 1)^n ≤ ℬ n := by
  induction n with
  | zero => simpa using (Submodule.one_le.mpr (SetLike.one_mem_graded ℬ))
  | succ n ih =>
    rw [pow_succ]
    apply (mul_le_mul' ih le_rfl).trans
    exact Submodule.mul_le.mpr (fun _ hx _ hy => SetLike.mul_mem_graded hx hy)

lemma map_mem (f : MvPolynomial σ k →ₐ[k] B)
    (hX : ∀ i, f (MvPolynomial.X i) ∈ ℬ 1) {n : ℕ} {p : MvPolynomial σ k}
    (hp : p ∈ MvPolynomial.homogeneousSubmodule σ k n) : f p ∈ ℬ n := by
  have h1 : (MvPolynomial.homogeneousSubmodule σ k 1).map f.toLinearMap ≤ ℬ 1 := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro x ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hX i
  have hn : (MvPolynomial.homogeneousSubmodule σ k n).map f.toLinearMap ≤ ℬ n := by
    rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow]
    exact (pow_le_pow_left' h1 n).trans (homogeneous_pow_le ℬ n)
  exact hn ⟨p, hp, rfl⟩

/-- A degree-one substitution into a genuinely graded target is graded. -/
def lift (f : MvPolynomial σ k →ₐ[k] B)
    (hX : ∀ i, f (MvPolynomial.X i) ∈ ℬ 1) :
    MvPolynomial.homogeneousSubmodule σ k →ₐᵍ[k] ℬ :=
  { f with map_mem := fun hp => map_mem ℬ f hX hp }

lemma zero_component (p : MvPolynomial σ k)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule σ k 0) :
    ∃ c : k, algebraMap k (MvPolynomial σ k) c = p := by
  rw [MvPolynomial.homogeneousSubmodule_zero] at hp
  exact Submodule.mem_one.mp hp
end GradedPolynomialMap

end


section
/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in Mathlib's LICENSE.
The structure-sheaf calculations are adapted from Mathlib's projective
spectrum functor, using containment in the radical of the irrelevant ideal.

This code has been modified.
-/
universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj

namespace AlgebraicGeometry
open scoped _root_.AlgebraicGeometry

section universe_polymorphic

variable {A B C σ τ ψ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (hf : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f.toRingHom).radical)

namespace ProjectiveSpectrum
open scoped _root_.AlgebraicGeometry.ProjectiveSpectrum

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
@[simps] def radical_comapFun (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le le := by
    apply p.3
    change ℬ₊.toIdeal ≤ p.1.toIdeal
    apply hf.trans
    apply p.2.radical_le_iff.mpr
    exact Ideal.map_le_iff_le_comap.mpr le

/-- The underlying continuous function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
def radicalComap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := radical_comapFun f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp⟩

end ProjectiveSpectrum

namespace Proj
open scoped _root_.AlgebraicGeometry.Proj
open _root_.OAI.AlgebraicGeometry.ProjectiveSpectrum

open StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ _root_.OAI.AlgebraicGeometry.ProjectiveSpectrum.radicalComap f hf ⁻¹' U.1)

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def radical_comapStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
  localRingHom f _ y.1.asHomogeneousIdeal.toIdeal rfl <| s ⟨_root_.OAI.AlgebraicGeometry.ProjectiveSpectrum.radicalComap f hf y.1, hUV y.2⟩

lemma radical_isLocallyFraction_comapStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (radical_comapStructureSheafFun f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨_root_.OAI.AlgebraicGeometry.ProjectiveSpectrum.radicalComap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (_root_.OAI.AlgebraicGeometry.ProjectiveSpectrum.radicalComap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  change ProjectiveSpectrum ℬ at q
  ext
  specialize h_frac ⟨_, hqW⟩
  have : q.asHomogeneousIdeal.toIdeal.IsPrime := q.isPrime
  have : (Ideal.comap f q.asHomogeneousIdeal.toIdeal).IsPrime := q.isPrime.comap f
  simp_all only [radical_comapStructureSheafFun]
  change (localRingHom f _ q.asHomogeneousIdeal.toIdeal rfl (s ⟨radicalComap f hf q, leOfHom iWU hqW⟩)).val = _
  change s ⟨radicalComap f hf q, leOfHom iWU hqW⟩ = _ at h_frac
  erw [h_frac]
  erw [val_localRingHom, val_mk]

/-- The underlying ring hom of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
noncomputable def radical_comapStructureSheaf :
    (Proj.structureSheaf 𝒜).1.obj (.op U) →+* (Proj.structureSheaf ℬ).1.obj (.op V) where
  toFun s := ⟨radical_comapStructureSheafFun _ _ _ _ hUV s.1,
      radical_isLocallyFraction_comapStructureSheafFun _ _ _ _ hUV _ s.2⟩
  map_one' := by
    apply Subtype.ext
    funext y
    have : y.1.asHomogeneousIdeal.toIdeal.IsPrime := y.1.isPrime
    have : (Ideal.comap f y.1.asHomogeneousIdeal.toIdeal).IsPrime := y.1.isPrime.comap f
    change localRingHom f _ y.1.asHomogeneousIdeal.toIdeal rfl 1 = 1
    exact map_one _
  map_zero' := by
    apply Subtype.ext
    funext y
    have : y.1.asHomogeneousIdeal.toIdeal.IsPrime := y.1.isPrime
    have : (Ideal.comap f y.1.asHomogeneousIdeal.toIdeal).IsPrime := y.1.isPrime.comap f
    change localRingHom f _ y.1.asHomogeneousIdeal.toIdeal rfl 0 = 0
    exact map_zero _
  map_add' x y := by
    apply Subtype.ext
    funext p
    have : p.1.asHomogeneousIdeal.toIdeal.IsPrime := p.1.isPrime
    have : (Ideal.comap f p.1.asHomogeneousIdeal.toIdeal).IsPrime := p.1.isPrime.comap f
    change localRingHom f _ p.1.asHomogeneousIdeal.toIdeal rfl (_ + _) = _ + _
    exact map_add _ _ _
  map_mul' x y := by
    apply Subtype.ext
    funext p
    have : p.1.asHomogeneousIdeal.toIdeal.IsPrime := p.1.isPrime
    have : (Ideal.comap f p.1.asHomogeneousIdeal.toIdeal).IsPrime := p.1.isPrime.comap f
    change localRingHom f _ p.1.asHomogeneousIdeal.toIdeal rfl (_ * _) = _ * _
    exact map_mul _ _ _

end Proj

end universe_polymorphic


namespace Proj
open scoped _root_.AlgebraicGeometry.Proj
open _root_.OAI.AlgebraicGeometry.ProjectiveSpectrum

variable {A B C σ τ ψ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (hf : ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f.toRingHom).radical)

private local instance (p : ProjectiveSpectrum.top 𝒜) : p.1.toIdeal.IsPrime :=
  p.isPrime

/-- The underlying map of `Proj ℬ ⟶ Proj 𝒜` on the level of sheafed spaces. -/
@[simps! (isSimp := false)] noncomputable def radical_sheafedSpaceMap :
    _root_.AlgebraicGeometry.Proj.toSheafedSpace ℬ ⟶ _root_.AlgebraicGeometry.Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom <| radicalComap f hf
      c := { app U := (@CommRingCat.ofHom
        ((Proj.structureSheaf 𝒜).1.obj U)
        ((Proj.structureSheaf ℬ).1.obj
          (.op ((Opens.map (TopCat.ofHom (radicalComap f hf))).obj U.unop)))
        inferInstance inferInstance (radical_comapStructureSheaf f hf _ _ Set.Subset.rfl)) } }

lemma radical_germ_map_sectionInBasicOpen {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (_root_.OAI.AlgebraicGeometry.ProjectiveSpectrum.radicalComap f hf p).1.toIdeal.primeCompl) :
    (_root_.AlgebraicGeometry.Proj.toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (radical_sheafedSpaceMap f hf).hom.base).obj _) p (_root_.AlgebraicGeometry.mem_basicOpen_den _ _ _)
      ((radical_sheafedSpaceMap f hf).hom.c.app _ (_root_.AlgebraicGeometry.sectionInBasicOpen 𝒜 _ c)) =
    (_root_.AlgebraicGeometry.Proj.toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (_root_.AlgebraicGeometry.sectionInBasicOpen ℬ p (c.map _ le_rfl)) :=
  rfl

@[simp] lemma radical_val_sectionInBasicOpen_apply (p : ProjectiveSpectrum.top 𝒜)
    (c : NumDenSameDeg 𝒜 p.1.toIdeal.primeCompl)
    (q : ProjectiveSpectrum.basicOpen 𝒜 c.den) :
    ((_root_.AlgebraicGeometry.sectionInBasicOpen 𝒜 p c).val q).val = .mk c.num ⟨c.den, q.2⟩ :=
  rfl

@[elementwise] theorem radical_localRingHom_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (_root_.AlgebraicGeometry.Proj.stalkIso 𝒜 (_root_.OAI.AlgebraicGeometry.ProjectiveSpectrum.radicalComap f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (_root_.AlgebraicGeometry.Proj.stalkIso ℬ p).inv =
      (radical_sheafedSpaceMap f hf).hom.stalkMap p := by
  erw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, _root_.AlgebraicGeometry.Proj.stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom]
  ext x : 2
  change (localRingHom f _ p.asHomogeneousIdeal.toIdeal rfl x).val =
    (_root_.AlgebraicGeometry.Proj.stalkIso' ℬ p (((radical_sheafedSpaceMap f hf).hom.stalkMap p).hom
      ((_root_.AlgebraicGeometry.Proj.stalkIso' 𝒜 (_root_.OAI.AlgebraicGeometry.ProjectiveSpectrum.radicalComap f hf p)).symm x))).val
  obtain ⟨c, rfl⟩ := x.mk_surjective
  erw [val_localRingHom, val_mk]
  erw [Localization.localRingHom_mk]
  -- I sincerely apologise for your eyes.
  erw [_root_.AlgebraicGeometry.Proj.stalkIso'_symm_mk]
  erw [_root_.AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply]
  erw [radical_germ_map_sectionInBasicOpen]
  erw [_root_.AlgebraicGeometry.Proj.stalkIso'_germ]
  erw [radical_val_sectionInBasicOpen_apply]
  rfl

/-- Functoriality of `Proj`. -/
noncomputable def radicalMap : _root_.AlgebraicGeometry.Proj ℬ ⟶ _root_.AlgebraicGeometry.Proj 𝒜 where
  __ := (radical_sheafedSpaceMap f hf).hom
  prop p := .mk fun x hx ↦ by
    change ProjectiveSpectrum ℬ at p
    have : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
    have : (Ideal.comap f p.asHomogeneousIdeal.toIdeal).IsPrime := p.isPrime.comap f
    let φ := localRingHom f (Ideal.comap f p.asHomogeneousIdeal.toIdeal)
      p.asHomogeneousIdeal.toIdeal rfl
    have : IsLocalHom φ := by dsimp [φ]; infer_instance
    erw [← radical_localRingHom_comp_stalkIso f hf p] at hx
    change IsUnit ((_root_.AlgebraicGeometry.Proj.stalkIso ℬ p).inv.hom
      (φ ((_root_.AlgebraicGeometry.Proj.stalkIso 𝒜 (_root_.OAI.AlgebraicGeometry.ProjectiveSpectrum.radicalComap f hf p)).hom.hom x))) at hx
    have : IsLocalHom (_root_.AlgebraicGeometry.Proj.stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    have hφ := (isUnit_map_iff (_root_.AlgebraicGeometry.Proj.stalkIso ℬ p).inv.hom _).mp hx
    have hy := IsLocalHom.map_nonunit (f := φ) _ hφ
    exact (isLocalHom_of_iso (_root_.AlgebraicGeometry.Proj.stalkIso 𝒜 (_root_.OAI.AlgebraicGeometry.ProjectiveSpectrum.radicalComap f hf p))).map_nonunit x hy

@[simp] theorem radical_map_preimage_basicOpen (s : A) :
    radicalMap f hf ⁻¹ᵁ _root_.AlgebraicGeometry.Proj.basicOpen 𝒜 s = _root_.AlgebraicGeometry.Proj.basicOpen ℬ (f s) := rfl

theorem radical_ι_comp_map (s : A) : (_root_.AlgebraicGeometry.Proj.basicOpen ℬ (f s)).ι ≫ radicalMap f hf =
    (radicalMap f hf).resLE _ _ le_rfl ≫ (_root_.AlgebraicGeometry.Proj.basicOpen 𝒜 s).ι :=
  (_root_.AlgebraicGeometry.Scheme.Hom.resLE_comp_ι (radicalMap f hf) (by rfl)).symm

@[reassoc] lemma radical_awayToSection_comp_appLE {i : ℕ} {s : A} (hs : s ∈ 𝒜 i) :
    _root_.AlgebraicGeometry.Proj.awayToSection 𝒜 s ≫
      _root_.AlgebraicGeometry.Scheme.Hom.appLE (radicalMap f hf) (_root_.AlgebraicGeometry.Proj.basicOpen 𝒜 s) (_root_.AlgebraicGeometry.Proj.basicOpen ℬ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f s : Away 𝒜 s →+* Away ℬ (f s)) ≫
      _root_.AlgebraicGeometry.Proj.awayToSection ℬ (f s) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (𝒜 := 𝒜) (f := s) hs x
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk (𝒜 := ℬ) _ = HomogeneousLocalization.mk (𝒜 := ℬ) _
  ext
  simp

/--
The following square commutes:
```
Proj ℬ         ⟶ Proj 𝒜₁
    ^                   ^
    |                   |
Spec A₂[f(s)⁻¹]₀ ⟶ Spec A₁[s⁻¹]₀
```
-/
@[reassoc] theorem radical_awayι_comp_map {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    _root_.AlgebraicGeometry.Proj.awayι ℬ (f s) (f.2 hs) hi ≫ radicalMap f hf =
    _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ _root_.AlgebraicGeometry.Proj.awayι 𝒜 s hs hi := by
  have hsq :
      (radicalMap f hf).resLE (_root_.AlgebraicGeometry.Proj.basicOpen 𝒜 s) (_root_.AlgebraicGeometry.Proj.basicOpen ℬ (f s)) (by rfl) ≫
        (_root_.AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs hi).hom =
      (_root_.AlgebraicGeometry.Proj.basicOpenIsoSpec ℬ (f s) (f.2 hs) hi).hom ≫
        _root_.AlgebraicGeometry.Spec.map (CommRingCat.ofHom (Away.map f s)) := by
    refine _root_.AlgebraicGeometry.ext_to_Spec <| (cancel_mono (_root_.AlgebraicGeometry.Proj.basicOpen ℬ (f s)).topIso.hom).mp ?_
    simp only [_root_.AlgebraicGeometry.Proj.basicOpenIsoSpec_hom, _root_.AlgebraicGeometry.Scheme.Γ_map_op, _root_.AlgebraicGeometry.Scheme.Hom.comp_appTop,
      _root_.AlgebraicGeometry.Scheme.Hom.appTop]
    erw [_root_.AlgebraicGeometry.Proj.basicOpenToSpec_app_top, _root_.AlgebraicGeometry.Proj.basicOpenToSpec_app_top, _root_.AlgebraicGeometry.Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simp
    erw [radical_awayToSection_comp_appLE_assoc f hf hs]
  have hres := (Iso.eq_comp_inv (_root_.AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs hi)).mpr hsq
  calc
    _ = (_root_.AlgebraicGeometry.Proj.basicOpenIsoSpec ℬ (f s) (f.2 hs) hi).inv ≫
        ((radicalMap f hf).resLE (_root_.AlgebraicGeometry.Proj.basicOpen 𝒜 s) (_root_.AlgebraicGeometry.Proj.basicOpen ℬ (f s)) (by rfl) ≫
          (_root_.AlgebraicGeometry.Proj.basicOpen 𝒜 s).ι) := by
      erw [_root_.AlgebraicGeometry.Proj.awayι, Category.assoc, radical_ι_comp_map]
      rfl
    _ = _ := by
      rw [hres]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rfl

end Proj
end AlgebraicGeometry


end


noncomputable section
open HomogeneousIdeal _root_.AlgebraicGeometry
namespace GradedIntegralProj
variable {k A B : Type*} [Field k] [IsAlgClosed k]
  [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {𝒜 : ℕ → Submodule k A} {ℬ : ℕ → Submodule k B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]

omit [IsAlgClosed k] in
lemma sub_zero_component (a : A) :
    a - GradedRing.projZeroRingHom 𝒜 a ∈ 𝒜₊ := by
  change GradedRing.projZeroRingHom 𝒜 (a - GradedRing.projZeroRingHom 𝒜 a) = 0
  rw [map_sub]
  have he := congrArg Subtype.val (GradedRing.projZeroRingHom'_apply_coe 𝒜
    (GradedRing.projZeroRingHom' 𝒜 a))
  exact sub_eq_zero.mpr he.symm

omit [IsAlgClosed k] in
lemma quotient_base_scalars (f : 𝒜 →ₐᵍ[k] ℬ)
    (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a)
    (P : Ideal B) (hP : 𝒜₊.toIdeal.map f.toAlgHom.toRingHom ≤ P) (a : A) :
    ((Ideal.Quotient.mkₐ k P).comp f.toAlgHom) a ∈ (⊥ : Subalgebra k (B ⧸ P)) := by
  obtain ⟨c, hc⟩ := hzero (GradedRing.projZeroRingHom 𝒜 a)
    (GradedRing.projZeroRingHom' 𝒜 a).property
  rw [Algebra.mem_bot]
  refine ⟨c, ?_⟩
  have he : (Ideal.Quotient.mk P) (f (a - algebraMap k A c)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hP (Ideal.mem_map_of_mem _
      (hc ▸ sub_zero_component (𝒜 := 𝒜) a)))
  change ((Ideal.Quotient.mkₐ k P).comp f.toAlgHom) (a - algebraMap k A c) = 0 at he
  rw [map_sub, AlgHom.commutes] at he
  exact (sub_eq_zero.mp he).symm

/-- A finite/integral homogeneous normalization cannot acquire projective
points above the vertex. Radical inclusion is DERIVED, not an extra map
hypothesis. The connected degree-zero algebra is the ground field. -/
lemma irrelevant_le_radical (f : 𝒜 →ₐᵍ[k] ℬ)
    (hint : f.toAlgHom.toRingHom.IsIntegral)
    (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a) :
    ℬ₊.toIdeal ≤ (𝒜₊.toIdeal.map f.toAlgHom.toRingHom).radical := by
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  intro Q hQ
  let P := Q.homogeneousCore ℬ
  have hp : P.toIdeal.IsPrime := hQ.2.homogeneousCore
  let := hp
  have hmap : 𝒜₊.toIdeal.map f.toAlgHom.toRingHom ≤ P.toIdeal := by
    have hc : (𝒜₊.map f.toGradedRingHom).toIdeal ≤ Q := hQ.1
    exact ((𝒜₊.map f.toGradedRingHom).isHomogeneous.toIdeal_homogeneousCore_eq_self).symm.trans_le
      (Ideal.homogeneousCore_mono ℬ hc)
  apply le_trans ?_ (Q.toIdeal_homogeneousCore_le ℬ)
  apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).mpr
  intro n hn b hb
  let : Algebra A B := f.toAlgHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  have hi : IsIntegral A b := hint b
  have hi' : IsIntegral k ((Ideal.Quotient.mkₐ k P.toIdeal) b) :=
    SmallCM.integral_image_of_base_scalars (B := A) (N := B)
      (Ideal.Quotient.mkₐ k P.toIdeal)
      (quotient_base_scalars f hzero P.toIdeal hmap) hi
  obtain ⟨c, hc⟩ := SmallCM.integral_eq_scalar_of_algClosed hi'
  have hd : b - algebraMap k B c ∈ P := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub]
    exact sub_eq_zero.mpr hc.symm
  have hd' := P.isHomogeneous n hd
  have hscalar : algebraMap k B c ∈ ℬ 0 := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (ℬ 0).smul_mem c SetLike.GradedOne.one_mem
  change b ∈ ℬ n at hb
  change (DirectSum.decompose ℬ (b - algebraMap k B c) n : B) ∈ P.toIdeal at hd'
  rw [DirectSum.decompose_sub] at hd'
  change (DirectSum.decompose ℬ b n : B) -
    (DirectSum.decompose ℬ (algebraMap k B c) n : B) ∈ P.toIdeal at hd'
  change b ∈ P.toIdeal
  simpa only [DirectSum.decompose_of_mem_same ℬ hb,
    DirectSum.decompose_of_mem_ne ℬ hscalar (Nat.ne_of_gt hn).symm,
    ZeroMemClass.coe_zero, sub_zero] using hd' 

end GradedIntegralProj

universe u
namespace GradedIntegralProj
open CategoryTheory
variable {k A B : Type u} [Field k] [IsAlgClosed k]
  [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  {𝒜 : ℕ → Submodule k A} {ℬ : ℕ → Submodule k B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
/-- Actual projective scheme morphism induced by an integral homogeneous
map of connected graded algebras. -/
def integralMap (f : 𝒜 →ₐᵍ[k] ℬ)
    (hint : f.toAlgHom.toRingHom.IsIntegral)
    (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a) :
    Proj ℬ ⟶ Proj 𝒜 :=
  _root_.OAI.AlgebraicGeometry.Proj.radicalMap f.toGradedRingHom (irrelevant_le_radical f hint hzero)

@[reassoc] theorem integralMap_chart (f : 𝒜 →ₐᵍ[k] ℬ)
    (hint : f.toAlgHom.toRingHom.IsIntegral)
    (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a)
    {n : ℕ} (hn : 0 < n) (s : A) (hs : s ∈ 𝒜 n) :
    Proj.awayι ℬ (f s) (f.map_mem hs) hn ≫ integralMap f hint hzero =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f.toGradedRingHom s)) ≫
        Proj.awayι 𝒜 s hs hn :=
  _root_.OAI.AlgebraicGeometry.Proj.radical_awayι_comp_map f.toGradedRingHom (irrelevant_le_radical f hint hzero) hn s hs
end GradedIntegralProj

end


noncomputable section
open _root_.AlgebraicGeometry CategoryTheory Polynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace SectionCompletion
variable {k K σ : Type} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [Fintype σ]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
variable (w : σ → K) (hw : ∀ i, w i ∈ T 1)

/-- The genuine degree-one Noether-normalization map, now with its grading. -/
def linearGradedMap : MvPolynomial.homogeneousSubmodule σ k →ₐᵍ[k] homogeneous T :=
  GradedPolynomialMap.lift (homogeneous T) (linearPolynomialMap T w hw) (by
    intro i m hm
    change (linearPolynomialMap T w hw (MvPolynomial.X i)).val.coeff m = 0
    simp [linearPolynomialMap, Polynomial.coeff_monomial, Ne.symm hm])

/-- The actual projective morphism associated to a finite degree-one
normalization. Finiteness is used to PROVE the radical irrelevant containment. -/
def linearProjectiveMap (hfin : (linearPolynomialMap T w hw).Finite) :
    proj T ⟶ Proj (MvPolynomial.homogeneousSubmodule σ k) :=
  GradedIntegralProj.integralMap (linearGradedMap T w hw)
    (RingHom.IsIntegral.of_finite hfin) GradedPolynomialMap.zero_component

omit [Fintype σ] in
@[reassoc] lemma linearProjectiveMap_chart
    (hfin : (linearPolynomialMap T w hw).Finite) (i : σ) :
    Proj.awayι (homogeneous T) (linearGradedMap T w hw (MvPolynomial.X i))
      ((linearGradedMap T w hw).map_mem (MvPolynomial.isHomogeneous_X k i)) zero_lt_one ≫
      linearProjectiveMap T w hw hfin =
    Spec.map (CommRingCat.ofHom
      (HomogeneousLocalization.Away.map (linearGradedMap T w hw).toGradedRingHom
        (MvPolynomial.X i))) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule σ k) (MvPolynomial.X i)
        (MvPolynomial.isHomogeneous_X k i) zero_lt_one :=
  GradedIntegralProj.integralMap_chart (linearGradedMap T w hw)
    (RingHom.IsIntegral.of_finite hfin) GradedPolynomialMap.zero_component zero_lt_one _ _

end SectionCompletion
namespace ExplicitCone
/-- Finite homogeneous normalization of the literal normalized Kummer cone,
without substituting abstract numerical invariants for its rings. -/
lemma exists_finite_linear_projective_parameters :
    ∃ (w : Fin 3 → L) (hw : ∀ i, w i ∈ pieces 1),
      (SectionCompletion.linearPolynomialMap pieces w hw).Finite ∧
      Function.Injective (SectionCompletion.linearPolynomialMap pieces w hw) := by
  obtain ⟨w, h, hinj, hfin⟩ := exists_linear_parameters
  obtain ⟨hw, hf⟩ := GradedNormalization.finite_normalized_linear_parameters
    polynomialAlgebra polynomialAlgebra_scale w h hfin
  refine ⟨w, hw, hf, ?_⟩
  intro a b hab
  apply hinj
  have he : (SectionCompletion.polynomials pieces).val.comp
      (SectionCompletion.linearPolynomialMap pieces w hw) =
      MvPolynomial.aeval (fun i => Polynomial.monomial 1 (w i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [SectionCompletion.linearPolynomialMap]
  rw [← he]
  exact congrArg (SectionCompletion.polynomials pieces).val hab

abbrev plane : Scheme := Proj (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ)

def projectiveParameter : Fin 3 → L := exists_finite_linear_projective_parameters.choose

theorem projectiveParameter_mem : ∀ i, projectiveParameter i ∈ pieces 1 :=
  exists_finite_linear_projective_parameters.choose_spec.choose

lemma projectiveParameter_finite :
    (SectionCompletion.linearPolynomialMap pieces projectiveParameter projectiveParameter_mem).Finite :=
  exists_finite_linear_projective_parameters.choose_spec.choose_spec.1

/-- Actual morphism X→P² from the precise normalized section cone.
No claim identifying all of X with the source's smooth Kummer surface is
included, and no finite W→V conclusion is assumed. -/
def projectiveNormalization : projectiveSurface ⟶ plane :=
  SectionCompletion.linearProjectiveMap pieces projectiveParameter
    projectiveParameter_mem projectiveParameter_finite
end ExplicitCone

end


noncomputable section
namespace SectionCompletion
open Polynomial
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
variable (c : K) (hc : c ∈ T 1) (hn : c ≠ 0)

def homogeneousChartAlgMap : homogeneousChart T c hc →ₐ[k] K :=
  { homogeneousChartMap T c hc hn with
    commutes' := homogeneousChartMap_scalar T c hc hn }

def evaluateInv : polynomials T →ₐ[k] K :=
  ((Polynomial.aeval c⁻¹).restrictScalars k).comp (polynomials T).val

lemma evaluateInv_homogeneous (n : ℕ) (p : polynomials T)
    (hp : p ∈ homogeneous T (n • 1)) :
    evaluateInv T c p = p.val.coeff n / c ^ n := by
  change p.val.eval c⁻¹ = _
  rw [homogeneous_eq_monomial T (by simpa using hp : p ∈ homogeneous T n)]
  simp [div_eq_mul_inv]

lemma evaluateInv_mem_range (p : polynomials T) :
    evaluateInv T c p ∈ (homogeneousChartAlgMap T c hc hn).range := by
  change p.val.eval c⁻¹ ∈ RingHom.range (R := homogeneousChart T c hc) (homogeneousChartMap T c hc hn)
  rw [eval_eq_sum_range]
  apply (RingHom.range (R := homogeneousChart T c hc) (homogeneousChartMap T c hc hn)).sum_mem
  intro n _
  simpa only [div_eq_mul_inv, inv_pow] using
    scaledCoefficient_mem_range T c hc hn n (p.val.coeff n) (p.property n)

/-- Literal degree-one dehomogenization of the section algebra into its
actual homogeneous affine Proj chart, constructed as an algebra map. -/
def dehomogenize : polynomials T →ₐ[k] homogeneousChart T c hc :=
  (AlgEquiv.ofInjective (homogeneousChartAlgMap T c hc hn)
    (homogeneousChartMap_injective T c hc hn)).symm.toAlgHom.comp
      ((evaluateInv T c).codRestrict _ (evaluateInv_mem_range T c hc hn))

lemma homogeneousChartMap_dehomogenize (p : polynomials T) :
    homogeneousChartMap T c hc hn (dehomogenize T c hc hn p) = evaluateInv T c p := by
  exact congrArg Subtype.val ((AlgEquiv.ofInjective (homogeneousChartAlgMap T c hc hn)
    (homogeneousChartMap_injective T c hc hn)).apply_symm_apply
      ⟨evaluateInv T c p, evaluateInv_mem_range T c hc hn p⟩)

/-- Every homogeneous fraction is the dehomogenization of its numerator;
this is not a flatness or geometric assumption. -/
lemma dehomogenize_surjective : Function.Surjective (dehomogenize T c hc hn) := by
  intro x
  obtain ⟨n,p,hp,rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (homogeneous T) (linearSection_homogeneous T c hc) x
  refine ⟨p, homogeneousChartMap_injective T c hc hn ?_⟩
  rw [homogeneousChartMap_dehomogenize, homogeneousChartMap_mk,
    evaluateInv_homogeneous T c n p hp]

lemma dehomogenize_linearSection (a : K) (ha : a ∈ T 1) :
    dehomogenize T c hc hn (linearSection T a ha) =
      HomogeneousLocalization.Away.mk (homogeneous T) (linearSection_homogeneous T c hc)
        1 (linearSection T a ha) (by simpa using linearSection_homogeneous T a ha) := by
  apply homogeneousChartMap_injective T c hc hn
  rw [homogeneousChartMap_dehomogenize, homogeneousChartMap_mk,
    evaluateInv_homogeneous T c 1 _ (by simpa using linearSection_homogeneous T a ha)]
end SectionCompletion

end

end OAI

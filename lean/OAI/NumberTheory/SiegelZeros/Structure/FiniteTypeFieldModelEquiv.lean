import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport
import OAI.NumberTheory.SiegelZeros.EntireFunctions.LogarithmicForm

namespace OAI

namespace SiegelZeros

open Module CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators TensorProduct
noncomputable section
namespace WeightedTorusJets.Geometry

theorem finiteTypeFieldModel_isFractionRing
    (k F : Type*) [CommRing k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] :
    IsFractionRing (Algebra.EssFiniteType.subalgebra k F) F := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj (Algebra.EssFiniteType.submonoid k F) z
  exact ⟨a, s, (eq_div_iff (IsLocalization.map_units F s).ne_zero).mpr h⟩

def finiteTypeFieldModelEquiv
    (k F : Type*) [CommRing k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] :
    F ≃ₐ[k] FractionRing (Algebra.EssFiniteType.subalgebra k F) := by
  have : IsFractionRing (Algebra.EssFiniteType.subalgebra k F) F :=
    finiteTypeFieldModel_isFractionRing k F
  exact (IsLocalization.algEquiv (nonZeroDivisors (Algebra.EssFiniteType.subalgebra k F))
    F (FractionRing (Algebra.EssFiniteType.subalgebra k F))).restrictScalars k

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

universe u

theorem exists_normal_proper_model_of_essFiniteType_field
    (k : Type u) (F : Type*) [Field k] [CharZero k] [Field F]
    [Algebra k F] [Algebra.EssFiniteType k F] :
    ∃ (N : Scheme.{u}) (hN : IsIntegral N),
      let : IsIntegral N := hN
      ∃ (p : N ⟶ Spec (CommRingCat.of k)),
        IsLocallyNoetherian N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
        LocallyOfFiniteType p ∧ UniversallyClosed p ∧
        (let : Algebra k N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
         Nonempty (F →ₐ[k] N.functionField)) := by
  have : Small.{u} (Algebra.EssFiniteType.subalgebra k F) :=
    Algebra.FiniteType.small (R := k)
  have : Small.{u} F := small_of_surjective
    (IsLocalization.mk'_surjective (S := F) (Algebra.EssFiniteType.submonoid k F))
  let e : Shrink.{u} F ≃ₐ[k] F := Shrink.algEquiv k F
  have : Algebra.EssFiniteType k (Shrink.{u} F) :=
    (Algebra.EssFiniteType.iff_of_algEquiv e).mpr inferInstance
  obtain ⟨N, hN, p, hnoeth, hnormal, hft, hclosed, ⟨φ⟩⟩ :=
    exists_normal_proper_model_of_finiteType_domain k
      (Algebra.EssFiniteType.subalgebra k (Shrink.{u} F))
  have := hN
  let : Algebra k N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
  exact ⟨N, hN, p, hnoeth, hnormal, hft, hclosed,
    ⟨φ.comp ((Geometry.finiteTypeFieldModelEquiv k (Shrink.{u} F)).toAlgHom.comp
      e.symm.toAlgHom)⟩⟩

end WeightedTorusJets

namespace WeightedTorusJets

universe u

theorem scheme_global_germ_isIntegral
    {k : Type u} [CommRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [UniversallyClosed p]
    (x : X) (s : Γ(X, ⊤)) :
    let : Algebra k (X.presheaf.stalk x) := schemeBaseStalkAlgebra p x
    IsIntegral k (X.presheaf.germ ⊤ x (by simp) s) := by
  let : Algebra k (X.presheaf.stalk x) := schemeBaseStalkAlgebra p x
  have hIntegral : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop).hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  have h := (hIntegral s).map (X.presheaf.germ ⊤ x (by simp)).hom
  rw [← schemeBaseToStalk_eq_global_germ p x] at h
  exact h

end WeightedTorusJets

namespace WeightedTorusJets.Geometry

universe u

theorem isAlgebraic_of_logarithmicForm_eq_zero
    {k F ι : Type*}
    [Field k] [CharZero k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    [Fintype ι] (c : ι → k) (hc : LinearIndependent ℚ c)
    (f : ι → F) (hf : ∀ i, f i ≠ 0) (hform : logarithmicForm c f = 0) :
    ∀ i, IsAlgebraic k (f i) := by
  obtain ⟨N, hN, p, hnoeth, hnormal, hft, hclosed, ⟨φ⟩⟩ :=
    exists_normal_proper_model_of_essFiniteType_field k F
  have := hN
  have := hnoeth
  have := hnormal
  have := hft
  have := hclosed
  let : Algebra k N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
  intro i
  have hf' (j) : φ (f j) ≠ 0 := (map_ne_zero_iff φ φ.injective).mpr (hf j)
  have hω : ∑ j, (algebraMap k F (c j) / f j) •
      KaehlerDifferential.D k F (f j) = 0 := by
    simpa only [logarithmicForm, div_eq_mul_inv] using hform
  obtain ⟨s, _, hs⟩ := scheme_global_units_of_locallyOfFiniteType_log_form p c hc
    (fun j => φ (f j)) hf' (logarithmic_relation_map_algHom φ c f hω) i
  apply (isAlgebraic_algHom_iff φ φ.injective).mp
  rw [← hs]
  exact (scheme_global_germ_isIntegral p (genericPoint N) s).isAlgebraic

end WeightedTorusJets.Geometry
namespace WeightedTorusJets.Geometry

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

def derivationOnIdeal (D : Derivation K R R) (I : Ideal R) : I →ₗ[R] R ⧸ I where
  toFun x := Ideal.Quotient.mk I (D x)
  map_add' x y := by simp
  map_smul' r x := by
    change Ideal.Quotient.mk I (D (r * x.val)) = r • Ideal.Quotient.mk I (D x.val)
    rw [D.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul, add_zero]
    rfl

def derivationCotangent (D : Derivation K R R) (I : Ideal R) :
    I.Cotangent →ₗ[R] R ⧸ I :=
  Ideal.Cotangent.lift (derivationOnIdeal D I) (by
    intro x y
    change Ideal.Quotient.mk I (D (x.val * y.val)) = 0
    rw [D.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property,
      Ideal.Quotient.eq_zero_iff_mem.mpr y.property]
    simp)

def derivationCotangentResidue (D : Derivation K R R) (I : Ideal R) :
    I.Cotangent →ₗ[R ⧸ I] R ⧸ I where
  toFun := derivationCotangent D I
  map_add' := (derivationCotangent D I).map_add
  map_smul' c x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    change derivationCotangent D I (r • x) =
      (algebraMap R (R ⧸ I)) r • derivationCotangent D I x
    rw [algebraMap_smul, map_smul]

theorem independent_functionals_surjective {k V ι : Type*} [Field k] [AddCommGroup V]
    [Module k V] [Finite ι] (f : ι → V →ₗ[k] k) (hf : LinearIndependent k f) :
    Function.Surjective (LinearMap.pi f) := by
  apply LinearMap.range_eq_top.mp
  rw [← Submodule.span_eq (LinearMap.range (LinearMap.pi f))]
  change Submodule.span k (Set.range (fun x i => f i x)) = ⊤
  apply span_flip_eq_top_iff_linearIndependent.mpr
  exact hf.map' (LinearMap.ltoFun k V k k) (LinearMap.ker_eq_bot.mpr DFunLike.coe_injective)

theorem exists_ideal_element_with_derivatives {ι : Type*} [Finite ι]
    (I : Ideal R) [I.IsMaximal] (D : ι → Derivation K R R)
    (hD : LinearIndependent (R ⧸ I) (fun i => derivationCotangentResidue (D i) I))
    (c : ι → R ⧸ I) :
    ∃ x : I, ∀ i, Ideal.Quotient.mk I (D i x) = c i := by
  let := Ideal.Quotient.field I
  obtain ⟨y, hy⟩ := independent_functionals_surjective
    (fun i => derivationCotangentResidue (D i) I) hD c
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective y
  exact ⟨x, fun i => congrFun hy i⟩

end WeightedTorusJets.Geometry


namespace WeightedTorusJets.Geometry

variable {K ι T : Type*} [CommRing K] [CommRing T] [Fintype ι]
  [Algebra K T] [Algebra (MvPolynomial ι K) T] [IsScalarTower K (MvPolynomial ι K) T]

theorem invariantDerivation_X (c : ι → K) (i : ι) :
    invariantDerivation c (MvPolynomial.X i) = c i • (MvPolynomial.X i : MvPolynomial ι K) := by
  classical
  simp [invariantDerivation, MvPolynomial.pderiv_X, Pi.single_apply]

theorem localize_invariantDerivation_X (M : Submonoid (MvPolynomial ι K))
    [IsLocalization M T] (c : ι → K) (i : ι) :
    localizeDerivation M (invariantDerivation c)
      (algebraMap (MvPolynomial ι K) T (MvPolynomial.X i)) =
    algebraMap K T (c i) * algebraMap (MvPolynomial ι K) T (MvPolynomial.X i) := by
  rw [localizeDerivation_algebraMap, invariantDerivation_X,
    MvPolynomial.smul_eq_C_mul, map_mul]
  congr 1
  exact (IsScalarTower.algebraMap_apply K (MvPolynomial ι K) T (c i)).symm

end WeightedTorusJets.Geometry
open scoped TensorProduct

namespace WeightedTorusJets.Geometry

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

noncomputable def derivationAmbientCovector (I : Ideal A) (D : Derivation K A A) :
    (A ⧸ I) ⊗[A] Ω[A⁄K] →ₗ[A ⧸ I] A ⧸ I :=
  ((Algebra.linearMap A (A ⧸ I)).comp D.liftKaehlerDifferential).liftBaseChange (A ⧸ I)

@[simp]
theorem derivationAmbientCovector_tmul_D (I : Ideal A) (D : Derivation K A A) (x : A) :
    derivationAmbientCovector I D (1 ⊗ₜ[A] KaehlerDifferential.D K A x) =
      Ideal.Quotient.mk I (D x) := by
  simp [derivationAmbientCovector, Derivation.liftKaehlerDifferential_comp_D]

theorem derivationAmbientCovector_conormal (I : Ideal A) (D : Derivation K A A) (x : I) :
    (conormalDifferential (K := K) I).dualMap (derivationAmbientCovector I D)
      (I.toCotangent x) = Ideal.Quotient.mk I (D x) := by
  simp [LinearMap.dualMap_apply]

theorem range_conormalDifferential (I : Ideal A) :
    LinearMap.range (conormalDifferential (K := K) I) =
      LinearMap.ker (KaehlerDifferential.mapBaseChange K A (A ⧸ I)) := by
  apply Submodule.restrictScalars_injective A (A ⧸ I) _
  change LinearMap.range ((KaehlerDifferential.kerCotangentToTensor K A (A ⧸ I)).comp
    (Ideal.Cotangent.equivOfEq I (RingHom.ker (algebraMap A (A ⧸ I)))
      Ideal.mk_ker.symm).toLinearMap) = _
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  exact KaehlerDifferential.range_kerCotangentToTensor K A (A ⧸ I)
    Ideal.Quotient.mk_surjective

noncomputable def residueTangentMap (I : Ideal A) :
    Derivation K (A ⧸ I) (A ⧸ I) →ₗ[A ⧸ I]
      Module.Dual (A ⧸ I) ((A ⧸ I) ⊗[A] Ω[A⁄K]) :=
  (KaehlerDifferential.mapBaseChange K A (A ⧸ I)).dualMap.comp
    (KaehlerDifferential.linearMapEquivDerivation K (A ⧸ I)).symm.toLinearMap

@[simp]
theorem residueTangentMap_tmul_D (I : Ideal A)
    (D : Derivation K (A ⧸ I) (A ⧸ I)) (x : A) :
    residueTangentMap I D (1 ⊗ₜ[A] KaehlerDifferential.D K A x) =
      D (Ideal.Quotient.mk I x) := by
  change D.liftKaehlerDifferential
    (KaehlerDifferential.mapBaseChange K A (A ⧸ I)
      (1 ⊗ₜ[A] KaehlerDifferential.D K A x)) = _
  simp [Derivation.liftKaehlerDifferential_comp_D]

theorem ker_conormalDual_eq_range_residueTangent (I : Ideal A) [I.IsMaximal] :
    LinearMap.ker (conormalDifferential (K := K) I).dualMap =
      LinearMap.range (residueTangentMap (K := K) I) := by
  let := Ideal.Quotient.field I
  rw [residueTangentMap, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker, range_conormalDifferential]

noncomputable def normalQuotientEquivCotangentDual (I : Ideal A) [I.IsMaximal]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (A ⧸ I)] :
    (Module.Dual (A ⧸ I) ((A ⧸ I) ⊗[A] Ω[A⁄K]) ⧸
      LinearMap.range (residueTangentMap (K := K) I)) ≃ₗ[A ⧸ I]
        Module.Dual (A ⧸ I) I.Cotangent := by
  letI := Ideal.Quotient.field I
  exact (Submodule.quotEquivOfEq _ _
    (ker_conormalDual_eq_range_residueTangent (K := K) I).symm).trans
      ((conormalDifferential (K := K) I).dualMap.quotKerEquivOfSurjective
        (LinearMap.dualMap_surjective_of_injective (conormalDifferential_injective I)))

@[simp]
theorem normalQuotientEquivCotangentDual_mk (I : Ideal A) [I.IsMaximal]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (A ⧸ I)]
    (φ : Module.Dual (A ⧸ I) ((A ⧸ I) ⊗[A] Ω[A⁄K])) :
    normalQuotientEquivCotangentDual (K := K) I (Submodule.Quotient.mk φ) =
      (conormalDifferential (K := K) I).dualMap φ := by
  simp [normalQuotientEquivCotangentDual]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K S ι : Type*} [CommRing K] [CommRing S]
    [Algebra K S] [Algebra (MvPolynomial ι K) S]
    [IsScalarTower K (MvPolynomial ι K) S]
    [Algebra.FormallyEtale (MvPolynomial ι K) S]

noncomputable def localizedPolynomialKaehlerBasis : Module.Basis ι S Ω[S⁄K] :=
  ((KaehlerDifferential.mvPolynomialBasis K ι).baseChange S).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial ι K) S)

@[simp]
theorem localizedPolynomialKaehlerBasis_apply (i : ι) :
    localizedPolynomialKaehlerBasis (K := K) (S := S) i =
      KaehlerDifferential.D K S (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) := by
  simp [localizedPolynomialKaehlerBasis, KaehlerDifferential.mvPolynomialBasis_apply]

noncomputable def logarithmicKaehlerBasis
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) :
    Module.Basis ι S Ω[S⁄K] :=
  localizedPolynomialKaehlerBasis.unitsSMul (fun i => (hx i).unit⁻¹)

@[simp]
theorem logarithmicKaehlerBasis_apply
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) (i : ι) :
    logarithmicKaehlerBasis hx i = ((hx i).unit⁻¹ : Sˣ) •
      KaehlerDifferential.D K S (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) := by
  rw [logarithmicKaehlerBasis, Module.Basis.unitsSMul_apply,
    localizedPolynomialKaehlerBasis_apply]

variable {L : Type*} [Field L] [Algebra S L] [Fintype ι]

noncomputable def logarithmicAmbientEquiv
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) :
    Module.Dual L (L ⊗[S] Ω[S⁄K]) ≃ₗ[L] (ι → L) := by
  classical
  exact ((logarithmicKaehlerBasis hx).baseChange L).dualBasis.equivFun

theorem logarithmicAmbientEquiv_apply
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))
    (φ : Module.Dual L (L ⊗[S] Ω[S⁄K])) (i : ι) :
    logarithmicAmbientEquiv hx φ i =
      (algebraMap S L (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))⁻¹ *
        φ (1 ⊗ₜ[S] KaehlerDifferential.D K S
          (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) := by
  simp only [logarithmicAmbientEquiv, Module.Basis.dualBasis_equivFun,
    Module.Basis.baseChange_apply, logarithmicKaehlerBasis_apply]
  rw [Units.smul_def, TensorProduct.tmul_smul, LinearMap.map_smul_of_tower,
    Algebra.smul_def]
  congr 1
  rw [map_units_inv, (hx i).unit_spec]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry
attribute [local instance] Ideal.Quotient.field
variable {K S ι : Type*} [Field K] [CommRing S] [Fintype ι]
    [Algebra K S] [Algebra (MvPolynomial ι K) S]
    [IsScalarTower K (MvPolynomial ι K) S]
    [Algebra.FormallyEtale (MvPolynomial ι K) S]

theorem logarithmicAmbientEquiv_residueTangentMap (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))
    (D : Derivation K (S ⧸ I) (S ⧸ I)) :
    logarithmicAmbientEquiv hx (residueTangentMap I D) =
      logarithmicTangentMap (fun i => Ideal.Quotient.mk I
        (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) D := by
  ext i
  rw [logarithmicAmbientEquiv_apply, residueTangentMap_tmul_D]
  rfl

theorem logarithmicAmbientEquiv_invariantDerivation (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))
    (D : Derivation K S S) (a : ι → S)
    (ha : ∀ i, D (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) =
      a i * algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) :
    logarithmicAmbientEquiv hx (derivationAmbientCovector I D) =
      fun i => Ideal.Quotient.mk I (a i) := by
  ext i
  rw [logarithmicAmbientEquiv_apply, derivationAmbientCovector_tmul_D, ha, map_mul]
  have hi : Ideal.Quotient.mk I
      (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) ≠ 0 :=
    ((hx i).map (Ideal.Quotient.mk I)).ne_zero
  change (Ideal.Quotient.mk I
    (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))⁻¹ *
      (Ideal.Quotient.mk I (a i) * Ideal.Quotient.mk I
        (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) = _
  rw [mul_left_comm, inv_mul_cancel₀ hi, mul_one]

theorem map_range_residueTangent_logarithmic (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) :
    (LinearMap.range (residueTangentMap (K := K) I)).map
      (logarithmicAmbientEquiv hx).toLinearMap =
      LinearMap.range (logarithmicTangentMap (k := K) (fun i => Ideal.Quotient.mk I
        (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))) := by
  rw [← LinearMap.range_comp]
  congr 1
  ext D i
  exact congrFun (logarithmicAmbientEquiv_residueTangentMap I hx D) i

noncomputable def coordinateNormalEquivCotangentDual [PerfectField K]
    [Algebra.EssFiniteType K S] (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i))) :
    ((ι → S ⧸ I) ⧸ LinearMap.range (logarithmicTangentMap (k := K)
      (fun i => Ideal.Quotient.mk I (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))))
      ≃ₗ[S ⧸ I] Module.Dual (S ⧸ I) I.Cotangent := by
  have : Algebra.FormallySmooth K S := Algebra.FormallySmooth.comp K (MvPolynomial ι K) S
  have : Algebra.FormallySmooth K (S ⧸ I) := inferInstance
  exact (Submodule.Quotient.equiv _ _ (logarithmicAmbientEquiv hx)
    (map_range_residueTangent_logarithmic I hx)).symm.trans
      (normalQuotientEquivCotangentDual I)

theorem coordinateNormalEquivCotangentDual_mk [PerfectField K]
    [Algebra.EssFiniteType K S] (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))
    (φ : Module.Dual (S ⧸ I) ((S ⧸ I) ⊗[S] Ω[S⁄K])) :
    coordinateNormalEquivCotangentDual I hx
      (Submodule.Quotient.mk (logarithmicAmbientEquiv hx φ)) =
      (conormalDifferential (K := K) I).dualMap φ := by
  simp [coordinateNormalEquivCotangentDual, Submodule.Quotient.equiv_symm]

theorem coordinateNormal_invariant_pairing [PerfectField K]
    [Algebra.EssFiniteType K S] (I : Ideal S) [I.IsMaximal]
    (hx : ∀ i : ι, IsUnit (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)))
    (D : Derivation K S S) (a : ι → S)
    (ha : ∀ i, D (algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) =
      a i * algebraMap (MvPolynomial ι K) S (MvPolynomial.X i)) (x : I) :
    coordinateNormalEquivCotangentDual I hx
      (Submodule.Quotient.mk (fun i => Ideal.Quotient.mk I (a i))) (I.toCotangent x) =
        Ideal.Quotient.mk I (D x) := by
  rw [← logarithmicAmbientEquiv_invariantDerivation I hx D a ha,
    coordinateNormalEquivCotangentDual_mk, derivationAmbientCovector_conormal]

end WeightedTorusJets.Geometry

open Module

namespace WeightedTorusJets.Geometry

theorem exists_basis_ker_dotProduct_algebraMap {K L n ι : Type*}
    [Field K] [Field L] [Algebra K L] [Fintype n] [DecidableEq n] [Fintype ι]
    (c : n → K) (hc : c ≠ 0)
    (b : Basis ι K (LinearMap.ker (dotProductEquiv K n c))) :
    ∃ bL : Basis ι L (LinearMap.ker (dotProductEquiv L n (algebraMap K L ∘ c))),
      ∀ i, (bL i : n → L) = algebraMap K L ∘ (b i : n → K) := by
  let ωK := dotProductEquiv K n c
  let ωL := dotProductEquiv L n (algebraMap K L ∘ c)
  have hcL : algebraMap K L ∘ c ≠ 0 :=
    ((algebraMap K L).injective.comp_left.ne_iff' (by ext; simp)).mpr hc
  have hωK : ωK ≠ 0 := (dotProductEquiv K n).map_ne_zero_iff.mpr hc
  have hωL : ωL ≠ 0 := (dotProductEquiv L n).map_ne_zero_iff.mpr hcL
  have hmem (i : ι) : algebraMap K L ∘ (b i : n → K) ∈ LinearMap.ker ωL := by
    change (algebraMap K L ∘ c) ⬝ᵥ (algebraMap K L ∘ (b i : n → K)) = 0
    rw [← (algebraMap K L).map_dotProduct]
    have hi : c ⬝ᵥ (b i : n → K) = 0 := (b i).property
    rw [hi, map_zero]
  let w (i : ι) : LinearMap.ker ωL := ⟨algebraMap K L ∘ (b i : n → K), hmem i⟩
  have hbK : LinearIndependent K (fun i => (b i : n → K)) :=
    b.linearIndependent.map' (LinearMap.ker ωK).subtype (Submodule.ker_subtype _)
  have hbL : LinearIndependent L (fun i => algebraMap K L ∘ (b i : n → K)) :=
    linearIndependent_algebraMap_comp_iff.mpr hbK
  have hw : LinearIndependent L w :=
    LinearIndependent.of_comp (LinearMap.ker ωL).subtype hbL
  have hdK := Module.Dual.finrank_ker_add_one_of_ne_zero hωK
  have hdL := Module.Dual.finrank_ker_add_one_of_ne_zero hωL
  rw [finrank_pi] at hdK hdL
  have hd : finrank L (LinearMap.ker ωL) = finrank K (LinearMap.ker ωK) :=
    Nat.add_right_cancel (hdL.trans hdK.symm)
  have hcard : Fintype.card ι = finrank L (LinearMap.ker ωL) := by
    rw [hd, finrank_eq_card_basis b]
  let bL := Basis.mk hw (hw.span_eq_top_of_card_eq_finrank' hcard).ge
  refine ⟨bL, fun i => ?_⟩
  change (Basis.mk hw _ i : n → L) = _
  rw [Basis.mk_apply]



theorem finrank_normal_image_at_point
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K V) :
    Module.finrank K (LinearMap.range ((⊥ : Submodule K V).mkQ.domRestrict W)) =
      Module.finrank K W := by
  apply LinearMap.finrank_range_of_inj
  have hi : Function.Injective (⊥ : Submodule K V).mkQ := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mkQ]
  exact hi.comp W.injective_subtype

theorem exists_independent_image_finset
    {K U V ι : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K U]
    (b : Module.Basis ι K U) (f : U →ₗ[K] V) :
    ∃ I : Finset ι, I.card = Module.finrank K (LinearMap.range f) ∧
      LinearIndepOn K (fun i => f (b i)) (I : Set ι) := by
  classical
  have hs : Submodule.span K (Set.range (f.rangeRestrict ∘ b)) = ⊤ := by
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      LinearMap.range_rangeRestrict]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (f.rangeRestrict ∘ b)
  have : Finite κ := hli.finite
  let := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Module.finrank K (LinearMap.range f) := by
    rw [← finrank_span_eq_card hli, hspan, hs, finrank_top]
  refine ⟨Finset.univ.map ⟨a, ha⟩, by simpa using hcard, ?_⟩
  have hi := hli.map' (LinearMap.range f).subtype (Submodule.ker_subtype _)
  rw [Finset.coe_map, Finset.coe_univ, Set.image_univ]
  exact (linearIndepOn_range_iff ha _).mpr hi

theorem finrank_normal_image_eq_min
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ω : V →ₗ[K] K) (hω : ω ≠ 0) (hdim : Module.finrank K V = 4)
    (T : Submodule K V) (hT : T = ⊥ ∨ ¬ T ≤ LinearMap.ker ω) :
    Module.finrank K (LinearMap.range (T.mkQ.domRestrict (LinearMap.ker ω))) =
      min (4 - Module.finrank K T) 3 := by
  have hker : Module.finrank K (LinearMap.ker ω) = 3 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hω
    omega
  rcases hT with rfl | hT
  · rw [finrank_normal_image_at_point, hker]
    simp
  · have hr := finrank_normal_image_of_not_le ω T hT
    rw [hdim] at hr
    have hle := (T.mkQ.domRestrict (LinearMap.ker ω)).finrank_range_le
    rw [hker, hr] at hle
    rw [hr, Nat.min_eq_left hle]

theorem exists_independent_normal_finset
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ω : V →ₗ[K] K) (hω : ω ≠ 0) (hdim : Module.finrank K V = 4)
    (T : Submodule K V) (hT : T = ⊥ ∨ ¬ T ≤ LinearMap.ker ω)
    (b : Module.Basis (Fin 3) K (LinearMap.ker ω)) :
    ∃ I : Finset (Fin 3), I.card = min (4 - Module.finrank K T) 3 ∧
      LinearIndepOn K (fun i => T.mkQ (b i)) (I : Set (Fin 3)) := by
  obtain ⟨I, hI, hind⟩ :=
    exists_independent_image_finset b (T.mkQ.domRestrict (LinearMap.ker ω))
  refine ⟨I, ?_, hind⟩
  rw [hI, finrank_normal_image_eq_min ω hω hdim T hT]

end WeightedTorusJets.Geometry

end

end SiegelZeros

end OAI

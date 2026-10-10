import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.BirationalExtension

namespace OAI

/-! Projective Curves. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct

namespace NumericalDimensionOneCurveAux
open HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type*) [CommRing k]

abbrev planeGrading := MvPolynomial.homogeneousSubmodule (Fin 2) k
abbrev planeChart := HomogeneousLocalization.Away (planeGrading k) (MvPolynomial.X 1)

noncomputable def planeConstants : k →+* planeGrading k 0 where
  toFun c := ⟨MvPolynomial.C c, MvPolynomial.isHomogeneous_C _ c⟩
  map_one' := Subtype.ext (map_one MvPolynomial.C)
  map_zero' := Subtype.ext (map_zero MvPolynomial.C)
  map_add' a b := Subtype.ext (map_add MvPolynomial.C a b)
  map_mul' a b := Subtype.ext (map_mul MvPolynomial.C a b)

noncomputable def planeDehom : MvPolynomial (Fin 2) k →+* Polynomial k :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => if i = 0 then Polynomial.X else 1)

noncomputable def planeChartEval : planeChart k →+* Polynomial k :=
  (Localization.awayLift (planeDehom k) (MvPolynomial.X 1)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp [planeDehom]⟩)).comp
      (algebraMap (planeChart k) (Localization.Away (MvPolynomial.X (1 : Fin 2) :
        MvPolynomial (Fin 2) k)))

noncomputable def planeChartCoordinate : planeChart k :=
  HomogeneousLocalization.Away.mk (planeGrading k)
    (MvPolynomial.isHomogeneous_X k 1) 1 (MvPolynomial.X 0)
    (by simpa using MvPolynomial.isHomogeneous_X k (0 : Fin 2))

noncomputable def planeChartInv : Polynomial k →+* planeChart k :=
  Polynomial.eval₂RingHom
    ((HomogeneousLocalization.fromZeroRingHom (planeGrading k) _).comp (planeConstants k))
    (planeChartCoordinate k)

theorem planeConstants_surjective : Function.Surjective (planeConstants k) := by
  intro p
  refine ⟨p.val.coeff 0, Subtype.ext ?_⟩
  exact ((MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr p.property)).symm

theorem planeChartEval_mk (n : ℕ) (p : MvPolynomial (Fin 2) k)
    (hp : p ∈ planeGrading k (n • 1)) :
    planeChartEval k (HomogeneousLocalization.Away.mk (planeGrading k)
      (MvPolynomial.isHomogeneous_X k 1) n p hp) = planeDehom k p := by
  change (Localization.awayLift (planeDehom k) (MvPolynomial.X 1)
    (isUnit_iff_exists_inv.mpr ⟨1, by simp [planeDehom]⟩))
    (Localization.mk p ⟨MvPolynomial.X (1 : Fin 2) ^ n, n, rfl⟩) = _
  simpa using Localization.awayLift_mk (planeDehom k) (MvPolynomial.X 1) p 1
    (by simp [planeDehom]) n

theorem planeChartEval_constants (c : k) :
    planeChartEval k (HomogeneousLocalization.fromZeroRingHom (planeGrading k) _
      (planeConstants k c)) = Polynomial.C c := by
  change planeChartEval k (HomogeneousLocalization.Away.mk (planeGrading k)
    (MvPolynomial.isHomogeneous_X k 1) 0 (MvPolynomial.C c)
    (by change (MvPolynomial.C c).IsHomogeneous 0; exact MvPolynomial.isHomogeneous_C _ c)) = _
  rw [planeChartEval_mk]
  simp [planeDehom]

theorem planeChartEval_coordinate :
    planeChartEval k (planeChartCoordinate k) = Polynomial.X := by
  rw [planeChartCoordinate, planeChartEval_mk]
  simp [planeDehom]

theorem planeChartEval_inv : (planeChartEval k).comp (planeChartInv k) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro c
    simp [planeChartInv, planeChartEval_constants]
  · simp [planeChartInv, planeChartEval_coordinate]

theorem planeGrading_adjoin_X :
    Algebra.adjoin (planeGrading k 0) (Set.range (MvPolynomial.X : Fin 2 →
      MvPolynomial (Fin 2) k)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C c => exact (Algebra.adjoin _ _).algebraMap_mem (planeConstants k c)
  | add p q hp hq => exact (Algebra.adjoin _ _).add_mem hp hq
  | mul_X p i hp =>
    exact (Algebra.adjoin _ _).mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

theorem planeChart_monomial (a : ℕ) (ai : Fin 2 → ℕ)
    (hai : ∑ i, ai i • (1 : ℕ) = a • 1) :
    HomogeneousLocalization.Away.mk (planeGrading k)
        (MvPolynomial.isHomogeneous_X k 1) a (∏ i, MvPolynomial.X i ^ ai i)
        (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
          (fun i _ => MvPolynomial.isHomogeneous_X k i)) =
      planeChartCoordinate k ^ ai 0 := by
  have ha : a = ai 0 + ai 1 := by simpa [Fin.sum_univ_two] using hai.symm
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_pow]
  change (Localization.mk (∏ i, MvPolynomial.X i ^ ai i)
    ⟨(MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) ^ a, a, rfl⟩ :
      Localization.Away (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k)) =
    (Localization.mk (MvPolynomial.X (0 : Fin 2))
      ⟨(MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) ^ 1, 1, rfl⟩ :
        Localization.Away (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k)) ^ ai 0
  rw [Localization.mk_pow, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [ha, Fin.prod_univ_two, OneMemClass.coe_one, one_mul, pow_one,
    SubmonoidClass.coe_pow, pow_add]
  ring

theorem planeChartInv_bijective : Function.Bijective (planeChartInv k) := by
  constructor
  · exact Function.HasLeftInverse.injective ⟨planeChartEval k,
      fun p => congrArg (fun f : Polynomial k →+* Polynomial k => f p) (planeChartEval_inv k)⟩
  · intro x
    have hspan := HomogeneousLocalization.Away.span_mk_prod_pow_eq_top
      (MvPolynomial.isHomogeneous_X k 1) (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)
      (planeGrading_adjoin_X k) (fun _ => 1)
      (fun i => MvPolynomial.isHomogeneous_X k i)
    have hx : x ∈ Submodule.span (planeGrading k 0)
        { (HomogeneousLocalization.Away.mk (planeGrading k)
          (MvPolynomial.isHomogeneous_X k 1) a (∏ i, MvPolynomial.X i ^ ai i)
          (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _
            (fun i _ => MvPolynomial.isHomogeneous_X k i)) : planeChart k) |
            (a : ℕ) (ai : Fin 2 → ℕ) (hai : ∑ i, ai i • (1 : ℕ) = a • 1) } := by
      rw [hspan]
      trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ai, hai, rfl⟩ := hy
      refine ⟨Polynomial.X ^ ai 0, ?_⟩
      simpa [planeChartInv] using (planeChart_monomial k a ai hai).symm
    | zero => exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz =>
      obtain ⟨p, rfl⟩ := hy
      obtain ⟨q, rfl⟩ := hz
      exact ⟨p + q, map_add _ _ _⟩
    | smul c y _ hy =>
      obtain ⟨p, rfl⟩ := hy
      obtain ⟨c, rfl⟩ := planeConstants_surjective k c
      refine ⟨Polynomial.C c * p, ?_⟩
      simp [planeChartInv, Algebra.smul_def, HomogeneousLocalization.algebraMap_eq]

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G]

theorem proj_integral [IsDomain A] (hG : HomogeneousIdeal.irrelevant G ≠ ⊥) :
    IsIntegral (Proj G) := by
  let η : ProjectiveSpectrum G := ⟨⊥, Ideal.isPrime_bot,
    fun h => hG (le_antisymm h bot_le)⟩
  have hη : IsGenericPoint η Set.univ := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro y _
    exact (ProjectiveSpectrum.le_iff_mem_closure G η y).mp (show (⊥ : HomogeneousIdeal G) ≤ y.asHomogeneousIdeal from bot_le)
  let : IrreducibleSpace (Proj G) := (irreducibleSpace_def _).mpr hη.isIrreducible
  let : ∀ x : Proj G, _root_.IsReduced ((Proj G).presheaf.stalk x) := fun x => by
    let : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    let H := HomogeneousLocalization.AtPrime G x.asHomogeneousIdeal.toIdeal
    let : _root_.IsReduced H := isReduced_of_injective
      (algebraMap H (Localization.AtPrime x.asHomogeneousIdeal.toIdeal))
      (HomogeneousLocalization.val_injective _)
    exact isReduced_of_injective (Proj.stalkIso' G x) (Proj.stalkIso' G x).injective
  let : IsReduced (Proj G) := isReduced_of_isReduced_stalk _
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra

theorem planeXone_mem (k : Type*) [CommRing k] :
    (MvPolynomial.X 1 : MvPolynomial (Fin 2) k) ∈ planeGrading k 1 :=
  MvPolynomial.isHomogeneous_X k 1

noncomputable def complexAffineChart : Spec (.of (Polynomial ℂ)) ⟶ complexProjectiveSpace 1 :=
  Spec.map (CommRingCat.ofHom (planeChartEval ℂ)) ≫
    Proj.awayι (planeGrading ℂ) (MvPolynomial.X 1)
      (planeXone_mem ℂ) (by decide : 0 < (1 : ℕ))

theorem planeChartEval_bijective (k : Type*) [CommRing k] :
    Function.Bijective (planeChartEval k) := by
  have hleft : Function.LeftInverse (planeChartEval k) (planeChartInv k) :=
    fun p => congrArg (fun f : Polynomial k →+* Polynomial k => f p) (planeChartEval_inv k)
  refine ⟨?_, hleft.surjective⟩
  intro x y h
  obtain ⟨p, rfl⟩ := (planeChartInv_bijective k).2 x
  obtain ⟨q, rfl⟩ := (planeChartInv_bijective k).2 y
  rw [hleft p, hleft q] at h
  exact congrArg (planeChartInv k) h

theorem complexAffineChart_isOpenImmersion : IsOpenImmersion complexAffineChart := by
  let e := RingEquiv.ofBijective (planeChartEval ℂ) (planeChartEval_bijective ℂ)
  let : IsIso (CommRingCat.ofHom (planeChartEval ℂ)) := e.toCommRingCatIso.isIso_hom
  let : IsIso (Spec.map (CommRingCat.ofHom (planeChartEval ℂ))) := inferInstance
  exact IsOpenImmersion.comp _ (Proj.awayι (planeGrading ℂ) (MvPolynomial.X 1)
    (planeXone_mem ℂ) (by decide : 0 < (1 : ℕ)))

theorem planeAffineChart_toSpec (k : Type*) [CommRing k] :
    (Spec.map (CommRingCat.ofHom (planeChartEval k)) ≫
      Proj.awayι (planeGrading k) (MvPolynomial.X 1) (planeXone_mem k)
        (by decide : 0 < (1 : ℕ))) ≫
      (Proj.toSpecZero (planeGrading k) ≫ Spec.map (CommRingCat.ofHom (planeConstants k))) =
    Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (planeChartEval_constants k)

@[reassoc]
theorem complexAffineChart_over :
    complexAffineChart ≫ complexProjectiveSpaceMap 1 =
      Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) := by
  exact planeAffineChart_toSpec ℂ

theorem complexProjectiveLine_integral : IsIntegral (complexProjectiveSpace 1) := by
  apply proj_integral
  intro h
  have hX := HomogeneousIdeal.mem_irrelevant_of_mem (planeGrading ℂ)
    (by decide : 0 < (1 : ℕ)) (MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2))
  rw [h] at hX
  change MvPolynomial.X (1 : Fin 2) = (0 : MvPolynomial (Fin 2) ℂ) at hX
  exact (MvPolynomial.X_ne_zero (1 : Fin 2)) hX

theorem complexProjectiveLine_nontrivial : Nontrivial (complexProjectiveSpace 1) := by
  let : IsOpenImmersion complexAffineChart := complexAffineChart_isOpenImmersion
  have hi := complexAffineChart.isOpenEmbedding.injective
  let p : PrimeSpectrum (Polynomial ℂ) := ⟨⊥, Ideal.isPrime_bot⟩
  let q : PrimeSpectrum (Polynomial ℂ) :=
    ⟨RingHom.ker (Polynomial.evalRingHom (0 : ℂ)), RingHom.ker_isPrime _⟩
  have hpq : p ≠ q := by
    intro h
    have hX : Polynomial.X ∈ q.asIdeal := by simp [q]
    rw [← h] at hX
    change (Polynomial.X : Polynomial ℂ) = 0 at hX
    exact Polynomial.X_ne_zero hX
  exact ⟨⟨complexAffineChart p, complexAffineChart q, fun h => hpq (hi h)⟩⟩

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux

theorem ringKrullDim_le_of_quasiFinite (R S : Type*)
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.QuasiFinite R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (f := PrimeSpectrum.comap (algebraMap R S))
  intro p q hpq
  refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
  intro heq
  have hd := Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton
    (R := R) (S := S) (PrimeSpectrum.comap (algebraMap R S) p)
  have hsp : p ⤳ q := (PrimeSpectrum.le_iff_specializes p q).mp hpq.le
  have hp : p ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹'
      {PrimeSpectrum.comap (algebraMap R S) p} := rfl
  have hq : q ∈ PrimeSpectrum.comap (algebraMap R S) ⁻¹'
      {PrimeSpectrum.comap (algebraMap R S) p} := heq.symm
  exact hpq.ne (hd.eq_of_specializes hsp hp hq)

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
section SmoothCharts
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}}

noncomputable def schemeOpenScalar (sX : X ⟶ Spec (.of k)) (U : X.Opens) :
    k →+* Γ(X, U) :=
  (sX.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

@[instance_reducible]
noncomputable def schemeOpenAlgebra (sX : X ⟶ Spec (.of k)) (U : X.Opens) :
    Algebra k Γ(X, U) := (schemeOpenScalar sX U).toAlgebra

theorem exists_standard_smooth_chart (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (x : X) :
    ∃ (U : X.Opens), IsAffineOpen U ∧ x ∈ U ∧
      RingHom.IsStandardSmoothOfRelativeDimension n (schemeOpenScalar sX U) := by
  obtain ⟨U, _, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (f := sX) (n := n) x
  have hU : U = ⊤ := by
    ext y
    have hmem : sX.base x ∈ U := e hxV
    rw [show sX.base x = y from Subsingleton.elim _ _] at hmem
    exact ⟨fun _ => trivial, fun _ => hmem⟩
  subst U
  refine ⟨V, hV, hxV, ?_⟩
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right
    (sX.appLE ⊤ V e).hom
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv hf

end SmoothCharts
end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux

universe u

theorem coheight_le_of_smooth_dimension
    {k : Type u} [Field k] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n sX] (x : X) :
    Order.coheight x ≤ n := by
  obtain ⟨U, hU, hxU, hs⟩ := exists_standard_smooth_chart sX n x
  obtain ⟨g, _, hg⟩ := hs.exists_etale_mvPolynomial
  let : Algebra (MvPolynomial (Fin n) k) Γ(X, U) := g.toAlgebra
  let : Algebra.Etale (MvPolynomial (Fin n) k) Γ(X, U) := hg
  have hdim : ringKrullDim Γ(X, U) ≤ n := by
    have h := ringKrullDim_le_of_quasiFinite (MvPolynomial (Fin n) k) Γ(X, U)
    simpa using h
  let y : U := ⟨x, hxU⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := hU.isLocalization_stalk y
  have hstalk : ringKrullDim (X.presheaf.stalk x) ≤ n := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf y).asIdeal]
    exact (Ideal.height_le_ringKrullDim_of_ne_top
      (hU.primeIdealOf y).isPrime.ne_top).trans hdim
  rw [ringKrullDim_stalk_eq_coheight] at hstalk
  exact WithBot.coe_le_coe.mp hstalk

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux

theorem isIntegrallyClosed_of_etale_domain
    (R S : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.Etale R S] :
    IsIntegrallyClosed S := by
  let K := FractionRing R
  let T := S ⊗[R] K
  let : Algebra K T := Algebra.TensorProduct.rightAlgebra
  have hinj : Function.Injective (algebraMap R S) := FaithfulSMul.algebraMap_injective R S
  have hM : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      ((map_ne_zero_iff _ hinj).mpr (mem_nonZeroDivisors_iff_ne_zero.mp hy))
  let : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hM
  let : Algebra.Etale K T := Algebra.Etale.of_equiv
    (Algebra.TensorProduct.commRight R K S)
  let : Module.Finite K T := Algebra.FormallyUnramified.finite_of_free K T
  let : IsArtinianRing T := .of_finite K T
  let : Field T := (IsArtinianRing.isField_of_isDomain T).toField
  have hST : Function.Injective (algebraMap S T) := IsLocalization.injective T hM
  let : IsFractionRing S T := IsLocalization.of_le (Algebra.algebraMapSubmonoid S R⁰) S⁰ hM fun x hx =>
    isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hST).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hx))
  apply (isIntegrallyClosed_iff T).mpr
  intro x hx
  obtain ⟨z, hz⟩ :=
    (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := K)).2
      ⟨x, hx⟩
  have hmem : ∀ z : S ⊗[R] integralClosure R K,
      ∃ s : S, algebraMap S T s = (TensorProduct.toIntegralClosure R S K z).1 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨sx, hsx⟩ := hx
      obtain ⟨sy, hsy⟩ := hy
      exact ⟨sx + sy, by simp [hsx, hsy]⟩
    | tmul s y =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral y.2
      refine ⟨s * algebraMap R S r, ?_⟩
      simp only [map_mul, TensorProduct.toIntegralClosure, AlgHom.coe_codRestrict,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change (s ⊗ₜ[R] (1 : K)) * (algebraMap R S r ⊗ₜ[R] (1 : K)) =
        s ⊗ₜ[R] (y : K)
      rw [← hr]
      simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.algebraMap_eq_smul_one,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul]
  obtain ⟨s, hs⟩ := hmem z
  exact ⟨s, hs.trans (congrArg Subtype.val hz)⟩

theorem isIntegrallyClosed_of_smooth_field_domain
    (k S : Type*) [Field k] [CommRing S] [IsDomain S]
    [Algebra k S] [Algebra.Smooth k S] : IsIntegrallyClosed S := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  obtain ⟨f, hfp, n, af, ht, he⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  let : Algebra (MvPolynomial (Fin n) k) (Localization.Away f) := af
  let : IsScalarTower k (MvPolynomial (Fin n) k) (Localization.Away f) := ht
  let : Algebra.IsStandardEtale (MvPolynomial (Fin n) k) (Localization.Away f) := he
  have hf : f ≠ 0 := fun h => hfp (h ▸ p.zero_mem)
  let : IsDomain (Localization.Away f) := IsLocalization.Away.isDomain (Localization.Away f) hf
  let : IsIntegrallyClosed (Localization.Away f) :=
    isIntegrallyClosed_of_etale_domain (MvPolynomial (Fin n) k) (Localization.Away f)
  have hle : Submonoid.powers f ≤ p.primeCompl :=
    Submonoid.powers_le.mpr hfp
  let : Algebra (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  let : IsScalarTower S (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  let : IsLocalization (p.primeCompl.map (algebraMap S (Localization.Away f)))
      (Localization.AtPrime p) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ _ _ hle
  apply isIntegrallyClosed_of_isLocalization (Localization.AtPrime p)
    (p.primeCompl.map (algebraMap S (Localization.Away f)))
  rintro x ⟨y, hy, rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    ((map_ne_zero_iff _ (IsLocalization.injective (Localization.Away f)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hf))).mpr
      (fun h => hy (h ▸ p.zero_mem)))

open AlgebraicGeometry CategoryTheory
universe u

theorem integrallyClosed_stalk_of_smooth_field
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [Smooth f] (x : X) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hU.fromSpec ≫ f)
  have hs : Smooth (Spec.map φ) := hφ ▸ inferInstance
  have hs' : φ.hom.Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs
  let : Algebra k Γ(X, U) := φ.hom.toAlgebra
  let : Algebra.Smooth k Γ(X, U) := hs'
  let : IsIntegrallyClosed Γ(X, U) := isIntegrallyClosed_of_smooth_field_domain k Γ(X, U)
  let y : U := ⟨x, hxU⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf y
  let := hU.isLocalization_stalk y
  exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
    (hU.primeIdealOf y).asIdeal.primeCompl
    (hU.primeIdealOf y).asIdeal.primeCompl_le_nonZeroDivisors

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory
universe u

theorem valuationRing_stalk_of_smooth_curve
    {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (sC : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 sC] (x : C) :
    ValuationRing (C.presheaf.stalk x) := by
  let : Smooth sC := SmoothOfRelativeDimension.smooth 1 sC
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian sC
  let : IsIntegrallyClosed (C.presheaf.stalk x) :=
    integrallyClosed_stalk_of_smooth_field sC x
  let : Ring.KrullDimLE 1 (C.presheaf.stalk x) :=
    krullDimLE_of_coheight_le (coheight_le_of_smooth_dimension sC 1 x)
  by_cases hfield : IsField (C.presheaf.stalk x)
  · let := hfield.toField
    infer_instance
  · let : Ring.DimensionLEOne (C.presheaf.stalk x) :=
      ⟨fun {I} hI hprime =>
        Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance I hI hprime⟩
    let : IsDedekindDomain (C.presheaf.stalk x) := { }
    let : IsDiscreteValuationRing (C.presheaf.stalk x) :=
      ((IsDiscreteValuationRing.TFAE (C.presheaf.stalk x) hfield).out 3 1).mp
        (show IsDedekindDomain (C.presheaf.stalk x) from inferInstance)
    infer_instance

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory AlgebraicGeometry.Scheme
universe u

lemma partial_fromFunctionField_eq {C Y : Scheme.{u}} [IsIntegral C]
    (f : C.PartialMap Y) {x : C} (hx : x ∈ f.domain) :
    f.fromFunctionField =
      Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
        f.fromSpecStalkOfMem hx := by
  have hη : genericPoint C ∈ f.domain :=
    (genericPoint_specializes x).mem_open f.domain.2 hx
  have h : f.domain.fromSpecStalkOfMem (genericPoint C) hη =
      Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
        f.domain.fromSpecStalkOfMem x hx := by
    apply (cancel_mono f.domain.ι).mp
    rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact (C.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)).symm
  change f.domain.fromSpecStalkOfMem (genericPoint C) hη ≫ f.hom = _
  rw [h, Category.assoc]
  rfl

end NumericalDimensionOneCurveAux

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace NumericalDimensionOneCurveAux
open AlgebraicGeometry CategoryTheory AlgebraicGeometry.Scheme
universe u

theorem exists_extension_from_functionField_of_smooth_curve
    {k : Type u} [Field k] {C Y : Scheme.{u}} [IsIntegral C]
    (sC : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 sC]
    (sY : Y ⟶ Spec (.of k)) [IsProper sY]
    (g : Spec C.functionField ⟶ Y)
    (hg : g ≫ sY = C.fromSpecStalk (genericPoint C) ≫ sC) :
    ∃ f : C ⟶ Y, C.fromSpecStalk (genericPoint C) ≫ f = g ∧ f ≫ sY = sC := by
  let : Y.IsSeparated := by
    constructor
    rw [← Limits.terminal.comp_from sY]
    infer_instance
  let r := RationalMap.ofFunctionField sC sY g hg
  have hr : r.fromFunctionField = g := RationalMap.fromFunctionField_ofFunctionField _ _ _ _
  have hdomain : r.domain = ⊤ := by
    apply top_unique
    intro x _
    let : ValuationRing (C.presheaf.stalk x) := valuationRing_stalk_of_smooth_curve sC x
    have hv : ValuativeCriterion.Existence sY := by
      have h : UniversallyClosed sY := inferInstance
      rw [UniversallyClosed.eq_valuativeCriterion] at h
      exact h.1
    have hw : g ≫ sY =
        Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk x) C.functionField)) ≫
          (C.fromSpecStalk x ≫ sC) := by
      rw [hg, ← Category.assoc]
      exact congrArg (fun t => t ≫ sC)
        (C.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)).symm
    obtain ⟨l, hlg, hl⟩ := (hv {
      R := C.presheaf.stalk x
      commRing := inferInstanceAs (CommRing (C.presheaf.stalk x))
      domain := inferInstanceAs (IsDomain (C.presheaf.stalk x))
      K := C.functionField
      i₁ := g
      i₂ := C.fromSpecStalk x ≫ sC
      commSq := ⟨hw⟩ }).exists_lift
    let p := PartialMap.ofFromSpecStalk sC sY l hl
    have hx : x ∈ p.domain := PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
    apply RationalMap.mem_domain.mpr
    refine ⟨p, hx, RationalMap.eq_of_fromFunctionField_eq _ _ ?_⟩
    rw [RationalMap.fromFunctionField_toRationalMap, partial_fromFunctionField_eq p hx,
      PartialMap.fromSpecStalkOfMem_ofFromSpecStalk, hr]
    exact hlg
  let p := r.toPartialMap
  have hpdom : p.domain = ⊤ := hdomain
  let : IsIso p.domain.ι := by
    rw [hpdom]
    change IsIso C.topIso.hom
    infer_instance
  let f := inv p.domain.ι ≫ p.hom
  have hf : C.fromSpecStalk (genericPoint C) ≫ f = g := by
    have hη : genericPoint C ∈ p.domain := by rw [hpdom]; trivial
    have hi : C.fromSpecStalk (genericPoint C) ≫ inv p.domain.ι =
        p.domain.fromSpecStalkOfMem (genericPoint C) hη := by
      apply (cancel_mono p.domain.ι).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
        Scheme.Opens.fromSpecStalkOfMem_ι]
    change C.fromSpecStalk (genericPoint C) ≫ inv p.domain.ι ≫ p.hom = g
    rw [← Category.assoc, hi]
    change p.fromFunctionField = g
    rw [← RationalMap.fromFunctionField_toRationalMap, RationalMap.toRationalMap_toPartialMap, hr]
  refine ⟨f, hf, ?_⟩
  let : IsDominant (C.fromSpecStalk (genericPoint C)) := ⟨by
    have hden : Dense ({genericPoint C} : Set C) :=
      dense_iff_closure_eq.mpr (genericPoint_spec C)
    exact hden.mono (Set.singleton_subset_iff.mpr ⟨_, C.fromSpecStalk_closedPoint⟩)⟩
  apply ext_of_isDominant (C.fromSpecStalk (genericPoint C))
  rw [← Category.assoc, hf, hg]

end NumericalDimensionOneCurveAux

end OAI

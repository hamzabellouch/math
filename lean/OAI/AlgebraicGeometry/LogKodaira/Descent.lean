import Mathlib
import OAI.AlgebraicGeometry.LogKodaira.NonzeroFiber

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.PluriformDescent
open SmoothProjectiveVariety DifferentialBaseChange CanonicalAdjunction
open FiberChartSpecialization LogarithmicSpecialization

 
def absolutePluriformCoordinate {A : Type*} [CommRing A] [Algebra ℂ A]
    (n m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential ℂ A)) :
    Pluricanonical ℂ A n m ≃ₗ[A] A :=
  (PiTensorProduct.congr fun _ : Fin m => determinantCoordinate b).trans
    (PiTensorProduct.constantBaseRingEquiv (Fin m) A).toLinearEquiv

 

def BaseVanishesAt {Y : SmoothProjectiveVariety} (D : Y.ReducedSNCBoundary)
    (m : ℕ) (τ : Y.RationalPluriform m) (y : Y.ComplexPoint) : Prop :=
  ∃ (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1) (_hU : Nonempty U.1),
    U.1 ≤ D.complement ∧
    ∃ (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
          (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (t : Γ(Y.scheme, U.1)), t ≠ 0 ∧ D.ideal.ideal U = Ideal.span {t} ∧
      ∃ q : Pluricanonical ℂ Γ(Y.scheme, U.1) Y.dimension m,
        logarithmicPullback ℂ Γ(Y.scheme, U.1) Y.scheme.functionField
          Y.dimension m t q = τ ∧
        complexPointEvaluation y U.1 hy (absolutePluriformCoordinate Y.dimension m b q) = 0

 

def FiberVanishesAt {X Y : SmoothProjectiveVariety}
    {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (m : ℕ) (s : X.RationalPluriform m)
    (y : Y.ComplexPoint) (hy : y.point ∈ D.complement) : Prop :=
  ∀ (F : FiberModel f.toBoundaryFibration y)
    (U : Y.scheme.affineOpens), U.1 ≤ D.complement →
    ∀ (hyU : y.point ∈ U.1)
      (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
        (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (P : NumeratorChart f.toBoundaryFibration y F U
        (fiber_dimension_eq f y hy F) m s),
      P.value hyU b = 0

 

def SectionConstructionStatement : Prop :=
  ∀ (X Y : SmoothProjectiveVariety) (E : X.ReducedSNCBoundary)
    (D : Y.ReducedSNCBoundary) (f : StratumSmoothFibration X Y E D)
    (m : ℕ), 0 < m →
    ∀ s : X.RationalPluriform m, s ∈ E.sections m → s ≠ 0 →
      (0 : WithBot ℕ∞) ≤ D.kodaira ∧
      (D.kodaira = 0 → ∀ (y : Y.ComplexPoint) (hy : y.point ∈ D.complement),
        FiberVanishesAt f m s y hy →
        ∃ a : ℕ, 0 < a ∧ ∃ τ : Y.RationalPluriform a,
          τ ∈ D.sections a ∧ τ ≠ 0 ∧ BaseVanishesAt D a τ y)

end ReverseLogKodaira.PluriformDescent

 

open CategoryTheory Limits

namespace ReverseLogKodaira.FiberIdeal

 

theorem ker_inl_of_surjective
    {R A S C : CommRingCat} (f : R ⟶ A) (g : R ⟶ S)
    (i : A ⟶ C) (j : S ⟶ C) (hp : IsPushout f g i j)
    (hg : Function.Surjective g) :
    RingHom.ker i.hom = (RingHom.ker g.hom).map f.hom := by
  let J : Ideal A := (RingHom.ker g.hom).map f.hom
  let Q : CommRingCat := CommRingCat.of (A ⧸ J)
  let q : A ⟶ Q := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have hker : RingHom.ker g.hom ≤ RingHom.ker (q.hom.comp f.hom) := by
    intro x hx
    change Ideal.Quotient.mk J (f x) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_map_of_mem f.hom hx
  let b : S ⟶ Q := CommRingCat.ofHom
    (g.hom.liftOfSurjective hg ⟨q.hom.comp f.hom, hker⟩)
  have hw : f ≫ q = g ≫ b := by
    apply CommRingCat.hom_ext
    exact (RingHom.liftOfSurjective_comp g.hom hg
      ⟨q.hom.comp f.hom, hker⟩).symm
  let d : C ⟶ Q := hp.desc q b hw
  apply le_antisymm
  · intro x hx
    change i x = 0 at hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q x = 0
    have heq : d (i x) = q x :=
      congrArg (fun k : A ⟶ Q => k x) (hp.inl_desc q b hw)
    rw [← heq, hx, map_zero]
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change g x = 0 at hx
    change i (f x) = 0
    have hw' : i (f x) = j (g x) :=
      congrArg (fun k : R ⟶ C => k x) hp.w
    rw [hw', hx, map_zero]

end ReverseLogKodaira.FiberIdeal

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

theorem fiber_chart_kernel
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :
    RingHom.ker (chartToFunctionField F.inclusion V.1) =
      (RingHom.ker (complexPointEvaluation y U.1 hy)).map (f.hom.appLE U.1 V.1 e).hom := by
  have heval : Function.Surjective (complexPointEvaluation y U.1 hy) := by
    intro z
    exact ⟨Y.constants U.1 z, complexPointEvaluation_constants y U.1 hy z⟩
  have hk := FiberIdeal.ker_inl_of_surjective _ _ _ _
    (fiber_affine_chart_pushout f y F U hy V e).2 heval
  change RingHom.ker (F.inclusion.app V.1).hom =
    (RingHom.ker (complexPointEvaluation y U.1 hy)).map (f.hom.appLE U.1 V.1 e).hom at hk
  rw [← hk]
  ext a
  change F.variety.scheme.germToFunctionField (F.inclusion ⁻¹ᵁ V.1)
    (F.inclusion.app V.1 a) = 0 ↔ F.inclusion.app V.1 a = 0
  constructor
  · intro ha
    apply F.variety.scheme.germToFunctionField_injective (F.inclusion ⁻¹ᵁ V.1)
    simpa only [map_zero] using ha
  · intro ha
    rw [ha, map_zero]

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization

 

theorem original_frame_coefficient_mem_fiber_ideal
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hy : y.point ∈ U.1)
    (V : X.scheme.affineOpens) (e : V.1 ≤ f.hom ⁻¹ᵁ U.1)
    [Nonempty (F.inclusion ⁻¹ᵁ V.1)] :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    letI : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
    ∀ (hsm : Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1)),
      letI := hsm
      ∀ (m : ℕ)
      (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
        (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
      (c : Module.Basis (Fin F.variety.dimension) Γ(X.scheme, V.1)
        (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1)))
      (t : Γ(X.scheme, V.1)), E.ideal.ideal V = Ideal.span {t} →
      ∀ q : Pluricanonical ℂ Γ(X.scheme, V.1) (Y.dimension + F.variety.dimension) m,
        logarithmicNumerator f y F U hy V e hsm Y.dimension F.variety.dimension m b c t q = 0 →
        pluricanonicalCoordinate ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1)
          Y.dimension F.variety.dimension m b c q ∈
          (RingHom.ker (complexPointEvaluation y U.1 hy)).map (f.hom.appLE U.1 V.1 e).hom
 := by
  let : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    (f.hom.appLE U.1 V.1 e).hom.toAlgebra
  let : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
  intro hsm
  let := hsm
  intro m b c t ht q hq
  rw [← fiber_chart_kernel f y F U hy V e]
  change chartToFunctionField F.inclusion V.1
    (pluricanonicalCoordinate ℂ Γ(Y.scheme, U.1) Γ(X.scheme, V.1)
      Y.dimension F.variety.dimension m b c q) = 0
  by_contra hne
  exact (logarithmicNumerator_ne_zero_of_coefficient f y F U hy V e hsm Y.dimension m b c t
    (fiber_boundary_equation_ne_zero f y F V t ht) q hne) hq

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.PluriformDescent
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization
open FiberChartSpecialization

 

theorem original_coefficient_in_point_ideal_of_fiber_zero
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (m : ℕ) (s : X.RationalPluriform m)
    (y : Y.ComplexPoint) (hy : y.point ∈ D.complement)
    (hzero : FiberVanishesAt f m s y hy)
    (F : FiberModel f.toBoundaryFibration y)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement) (hyU : y.point ∈ U.1)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
    (P : NumeratorChart f.toBoundaryFibration y F U (fiber_dimension_eq f y hy F) m s) :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, P.V.1) :=
      (f.hom.appLE U.1 P.V.1 P.overOpen).hom.toAlgebra
    letI : IsScalarTower ℂ Γ(Y.scheme, U.1) Γ(X.scheme, P.V.1) :=
      IsScalarTower.of_algebraMap_eq fun a =>
        (appLE_constants f.hom f.over_base U.1 P.V.1 P.overOpen a).symm
    letI := P.formallySmooth
    pluricanonicalCoordinate ℂ Γ(Y.scheme, U.1) Γ(X.scheme, P.V.1)
      Y.dimension F.variety.dimension m b P.relativeBasis P.numerator ∈
      (RingHom.ker (complexPointEvaluation y U.1 hyU)).map
        (f.hom.appLE U.1 P.V.1 P.overOpen).hom := by
  let := P.fiberNonempty
  exact original_frame_coefficient_mem_fiber_ideal f.toBoundaryFibration y F U hyU
    P.V P.overOpen P.formallySmooth m b P.relativeBasis P.equation P.ideal_eq P.numerator
    (hzero F U hU hyU b P)

end ReverseLogKodaira.PluriformDescent

end

end OAI

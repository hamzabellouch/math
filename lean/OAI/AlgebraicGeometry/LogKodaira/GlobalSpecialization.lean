import Mathlib
import OAI.AlgebraicGeometry.LogKodaira.FiberCharts
import OAI.AlgebraicGeometry.LogKodaira.BoundaryPullback
import OAI.AlgebraicGeometry.LogKodaira.SmoothCharts
import OAI.AlgebraicGeometry.LogKodaira.LogLattice

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.DifferentialBaseChange

 
def degreeTransport (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    {n n' : ℕ} (h : n = n') (m : ℕ) :
    Pluricanonical R B n m ≃ₗ[B] Pluricanonical R B n' m := by
  subst n'
  exact LinearEquiv.refl B _

lemma logarithmicPullback_degreeTransport
    (R B K : Type*) [CommRing R] [CommRing B] [Field K]
    [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    {n n' : ℕ} (h : n = n') (m : ℕ) (t : B) (q : Pluricanonical R B n m) :
    LogarithmicSpecialization.logarithmicPullback R B K n' m t
      (degreeTransport R B h m q) = degreeTransport R K h m
        (LogarithmicSpecialization.logarithmicPullback R B K n m t q) := by
  subst n'
  rfl

end ReverseLogKodaira.DifferentialBaseChange

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

 

structure NumeratorChart
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (U : Y.scheme.affineOpens) (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) where
  V : X.scheme.affineOpens
  overOpen : V.1 ≤ f.hom ⁻¹ᵁ U.1
  nonempty : Nonempty V.1
  fiberNonempty : Nonempty (F.inclusion ⁻¹ᵁ V.1)
  formallySmooth :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 overOpen).hom.toAlgebra
    Algebra.FormallySmooth Γ(Y.scheme, U.1) Γ(X.scheme, V.1)
  relativeBasis :
    letI : Algebra Γ(Y.scheme, U.1) Γ(X.scheme, V.1) :=
      (f.hom.appLE U.1 V.1 overOpen).hom.toAlgebra
    Module.Basis (Fin F.variety.dimension) Γ(X.scheme, V.1)
      (KaehlerDifferential Γ(Y.scheme, U.1) Γ(X.scheme, V.1))
  equation : Γ(X.scheme, V.1)
  equation_ne_zero : equation ≠ 0
  ideal_eq : E.ideal.ideal V = Ideal.span {equation}
  numerator : Pluricanonical ℂ Γ(X.scheme, V.1) (Y.dimension + F.variety.dimension) m
  source_eq :
    letI := nonempty
    logarithmicPullback ℂ Γ(X.scheme, V.1) X.scheme.functionField
      (Y.dimension + F.variety.dimension) m equation numerator =
        degreeTransport ℂ X.scheme.functionField hdim m s

namespace NumeratorChart
variable {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
  {f : BoundaryFibration X Y E D} {y : Y.ComplexPoint} {F : FiberModel f y}
  {U : Y.scheme.affineOpens} {hdim : X.dimension = Y.dimension + F.variety.dimension}
  {m : ℕ} {s : X.RationalPluriform m}

def value (P : NumeratorChart f y F U hdim m s) (hy : y.point ∈ U.1)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1))) : F.variety.RationalPluriform m :=
  letI := P.fiberNonempty
  logarithmicNumerator f y F U hy P.V P.overOpen P.formallySmooth
    Y.dimension F.variety.dimension m b P.relativeBasis P.equation P.numerator

end NumeratorChart
end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

lemma fiber_point_image
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : BoundaryFibration X Y E D) (y : Y.ComplexPoint) (F : FiberModel f y)
    (z : F.variety.scheme) : f.hom (F.inclusion z) = y.point := by
  rw [← Scheme.Hom.comp_apply, F.square.w, Scheme.Hom.comp_apply]
  exact congrArg y.hom (Subsingleton.elim _ complexBasePoint)

lemma fiber_dimension_eq
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (y : Y.ComplexPoint)
    (hy : y.point ∈ D.complement) (F : FiberModel f.toBoundaryFibration y) :
    X.dimension = Y.dimension + F.variety.dimension := by
  have hrange : Set.range y.hom ⊆ D.complement := by
    rintro _ ⟨z, rfl⟩
    have hz : z = complexBasePoint := Subsingleton.elim _ _
    subst z
    exact hy
  obtain ⟨hle, hr⟩ := SmoothDimension.smooth_fiber_dimension X.structural Y.structural
    X.dimension Y.dimension f.hom f.over_base y.hom F.inclusion F.variety.structural
    F.square D.complement hrange
    (by simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using f.smooth)
  let := hr
  have he : X.dimension - Y.dimension = F.variety.dimension :=
    SmoothDimension.smooth_dimension_unique F.variety.scheme F.variety.structural _ _
  omega

lemma local_logarithmic_numerator
    {X : SmoothProjectiveVariety} (E : X.ReducedSNCBoundary)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (V : X.scheme.affineOpens) [Nonempty V.1]
    (t : Γ(X.scheme, V.1)) (ht : t ≠ 0) (hI : E.ideal.ideal V = Ideal.span {t}) :
    ∃ q : Pluricanonical ℂ Γ(X.scheme, V.1) X.dimension m,
      logarithmicPullback ℂ Γ(X.scheme, V.1) X.scheme.functionField X.dimension m t q = s := by
  have hmem := hs V inferInstance t ht hI
  change _ ∈ Submodule.span Γ(X.scheme, V.1) _ at hmem
  rw [← LocalCanonical.range_pluricanonicalPullback ℂ Γ(X.scheme, V.1)
    X.scheme.functionField X.dimension m] at hmem
  obtain ⟨q, hq⟩ := hmem
  refine ⟨q, ?_⟩
  change ((algebraMap Γ(X.scheme, V.1) X.scheme.functionField t)^m)⁻¹ •
    LocalCanonical.pluricanonicalPullback ℂ Γ(X.scheme, V.1)
      X.scheme.functionField X.dimension m q = s
  rw [hq, smul_smul, inv_mul_cancel₀, one_smul]
  apply pow_ne_zero m
  change X.scheme.germToFunctionField V.1 t ≠ 0
  simpa only [map_zero] using (X.scheme.germToFunctionField_injective V.1).ne ht

namespace NumeratorChart

lemma exists_near_fiber_point
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (y : Y.ComplexPoint) (hy : y.point ∈ U.1) (F : FiberModel f.toBoundaryFibration y)
    (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (O : X.scheme.Opens) (z : F.variety.scheme) (hz : F.inclusion z ∈ O) :
    ∃ P : NumeratorChart f.toBoundaryFibration y F U hdim m s,
      F.inclusion z ∈ P.V.1 ∧ P.V.1 ≤ O := by
  classical
  obtain ⟨V, hzV, hVO, e, hsm, t, ht, hI⟩ :=
    exists_relative_log_chart f U hU O (F.inclusion z) hz
      (by simpa only [fiber_point_image f.toBoundaryFibration y F z] using hy)
  let : Nonempty V.1 := ⟨⟨F.inclusion z, hzV⟩⟩
  let : Nonempty (F.inclusion ⁻¹ᵁ V.1) := ⟨⟨z, hzV⟩⟩
  let A := Γ(Y.scheme, U.1)
  let B := Γ(X.scheme, V.1)
  let : Algebra A B := (f.hom.appLE U.1 V.1 e).hom.toAlgebra
  have hsub : X.dimension - Y.dimension = F.variety.dimension := by omega
  let : Algebra.IsStandardSmoothOfRelativeDimension F.variety.dimension A B := by
    rw [← hsub]
    exact hsm.toAlgebra
  let : Algebra.IsStandardSmooth A B :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth F.variety.dimension
  have hr : Module.finrank B (KaehlerDifferential A B) = F.variety.dimension := by
    simp only [Module.finrank,
      Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential F.variety.dimension,
      Cardinal.toNat_natCast]
  let c := Module.finBasisOfFinrankEq B (KaehlerDifferential A B) hr
  obtain ⟨q, hq⟩ := local_logarithmic_numerator E m s hs V t ht hI
  refine ⟨⟨V, e, inferInstance, inferInstance, inferInstance, c, t, ht, hI,
    degreeTransport ℂ B hdim m q, ?_⟩, hzV, hVO⟩
  rw [logarithmicPullback_degreeTransport, hq]

end NumeratorChart
end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization.NumeratorChart
open SmoothProjectiveVariety DifferentialBaseChange

variable {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
  {f : BoundaryFibration X Y E D} {y : Y.ComplexPoint} {F : FiberModel f y}
  {U : Y.scheme.affineOpens} {hdim : X.dimension = Y.dimension + F.variety.dimension}
  {m : ℕ} {s : X.RationalPluriform m}

lemma value_eq_of_refinement (P Q : NumeratorChart f y F U hdim m s)
    (hV : Q.V.1 ≤ P.V.1) (hy : y.point ∈ U.1)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1))) : P.value hy b = Q.value hy b := by
  let := P.nonempty
  let := Q.nonempty
  let := P.fiberNonempty
  let := Q.fiberNonempty
  exact specialization_refinement f y F U hy P.V Q.V P.overOpen hV
    P.formallySmooth Q.formallySmooth Y.dimension F.variety.dimension m b
    P.relativeBasis Q.relativeBasis P.equation Q.equation
    (fiber_boundary_equation_ne_zero f y F P.V P.equation P.ideal_eq)
    (fiber_boundary_equation_ne_zero f y F Q.V Q.equation Q.ideal_eq)
    P.numerator Q.numerator (P.source_eq.trans Q.source_eq.symm)

end ReverseLogKodaira.FiberChartSpecialization.NumeratorChart

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

lemma NumeratorChart.value_eq
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (y : Y.ComplexPoint) (hy : y.point ∈ U.1) (F : FiberModel f.toBoundaryFibration y)
    (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
    (P Q : NumeratorChart f.toBoundaryFibration y F U hdim m s) :
    P.value hy b = Q.value hy b := by
  let z := genericPoint F.variety.scheme
  have hzP : F.inclusion z ∈ P.V.1 :=
    ((genericPoint_spec F.variety.scheme).mem_open_set_iff (F.inclusion ⁻¹ᵁ P.V.1).2).mpr
      (by simpa using P.fiberNonempty)
  have hzQ : F.inclusion z ∈ Q.V.1 :=
    ((genericPoint_spec F.variety.scheme).mem_open_set_iff (F.inclusion ⁻¹ᵁ Q.V.1).2).mpr
      (by simpa using Q.fiberNonempty)
  obtain ⟨R, _, hR⟩ := NumeratorChart.exists_near_fiber_point f U hU y hy F hdim m s hs
    (P.V.1 ⊓ Q.V.1) z ⟨hzP, hzQ⟩
  exact (P.value_eq_of_refinement R (fun x hx => (hR hx).1) hy b).trans
    (Q.value_eq_of_refinement R (fun x hx => (hR hx).2) hy b).symm

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

 

theorem exists_global_specialization
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (y : Y.ComplexPoint) (hy : y.point ∈ U.1) (F : FiberModel f.toBoundaryFibration y)
    (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1))) :
    ∃ σ : F.variety.RationalPluriform m, σ ∈ F.boundary.sections m ∧
      ∀ P : NumeratorChart f.toBoundaryFibration y F U hdim m s, P.value hy b = σ := by
  classical
  obtain ⟨P, _, _⟩ := NumeratorChart.exists_near_fiber_point f U hU y hy F hdim m s hs
    ⊤ (genericPoint F.variety.scheme) (by trivial)
  refine ⟨P.value hy b, ?_, fun Q => NumeratorChart.value_eq f U hU y hy F hdim m s hs b Q P⟩
  change F.boundary.IsLogPluriform m (P.value hy b)
  apply (F.boundary.isLogPluriform_local_iff m (P.value hy b)).mpr
  intro z
  obtain ⟨Q, hzQ, _⟩ := NumeratorChart.exists_near_fiber_point f U hU y hy F hdim m s hs
    ⊤ z (by trivial)
  let := Q.fiberNonempty
  let W : F.variety.scheme.affineOpens := ⟨F.inclusion ⁻¹ᵁ Q.V.1,
    (fiber_affine_chart_pushout f.toBoundaryFibration y F U hy Q.V Q.overOpen).1⟩
  let tW : Γ(F.variety.scheme, W.1) := F.inclusion.app Q.V.1 Q.equation
  have htK := fiber_boundary_equation_ne_zero f.toBoundaryFibration y F Q.V
    Q.equation Q.ideal_eq
  have htW : tW ≠ 0 := by
    intro ht
    apply htK
    change algebraMap Γ(F.variety.scheme, W.1) F.variety.scheme.functionField tW = 0
    rw [ht, map_zero]
  have hIW : F.boundary.ideal.ideal W = Ideal.span {tW} := by
    rw [F.boundary_pullback,
      IdealPullback.ideal_comap_appLE E.ideal F.inclusion Q.V W le_rfl,
      Q.ideal_eq, Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span {(F.inclusion.appLE Q.V.1 (F.inclusion ⁻¹ᵁ Q.V.1) le_rfl).hom
      Q.equation} = _
    rw [Scheme.Hom.appLE_eq_app]
  refine ⟨W, Q.fiberNonempty, hzQ, tW, htW, hIW, ?_⟩
  have hreg := local_specialization_regular f.toBoundaryFibration y F U hy Q.V Q.overOpen
    Q.formallySmooth Y.dimension m b Q.relativeBasis Q.equation htK Q.numerator
  change (algebraMap Γ(F.variety.scheme, W.1) F.variety.scheme.functionField tW)^m •
    Q.value hy b ∈ F.variety.regularPluriformLattice W m at hreg
  rw [NumeratorChart.value_eq f U hU y hy F hdim m s hs b Q P] at hreg
  exact hreg

end ReverseLogKodaira.FiberChartSpecialization

end

end OAI

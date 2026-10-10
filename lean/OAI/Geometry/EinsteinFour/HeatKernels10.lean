import OAI.Geometry.EinsteinFour.CurvatureTensors02
import OAI.Geometry.EinsteinFour.FiniteHodgeMultiplicity
import OAI.Geometry.EinsteinFour.FiniteHodgeTraceCancellation
import OAI.Geometry.EinsteinFour.FourHeatGaussianConvolution
import OAI.Geometry.EinsteinFour.FourHeatGaussianSquare
import OAI.Geometry.EinsteinFour.GeodesicGeometry04
import OAI.Geometry.EinsteinFour.GeodesicGeometry05
import OAI.Geometry.EinsteinFour.HodgeTheory08
import OAI.Geometry.EinsteinFour.HodgeTheory09
import OAI.Geometry.EinsteinFour.ScalarIntegrableSeries
import OAI.Geometry.EinsteinFour.ScalarRegularity07
import OAI.Geometry.EinsteinFour.WeylEstimates03
import Mathlib.Algebra.Module.LinearMap.Index
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI


section

/-! The integral intersection form descends to the actual de Rham
quotient and is nondegenerate there. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

local instance : AddCommGroup (smoothClosedTwoForms (o := o)) :=
  Submodule.addCommGroup _

def smoothClosedIntersection :
    smoothClosedTwoForms (o := o) →ₗ[ℝ] smoothClosedTwoForms (o := o) →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => twoFormIntersection u.val v.val
      map_add' := fun v w => twoFormIntersection_add_right u.val v.val w.val
      map_smul' := fun r v => twoFormIntersection_smul_right r u.val v.val }
  map_add' u v := by ext w; exact twoFormIntersection_add_left u.val v.val w.val
  map_smul' r u := by ext v; exact twoFormIntersection_smul_left r u.val v.val

theorem smoothClosedIntersection_exact_right (hRic : RicciThree g)
    (u v : smoothClosedTwoForms (o := o)) (hv : v ∈ smoothExactTwoForms) :
    smoothClosedIntersection u v = 0 := by
  change v.val ∈ LinearMap.range (smoothOneFormExteriorLinear (o := o)) at hv
  obtain ⟨a, ha⟩ := hv
  change twoFormIntersection u.val v.val = 0
  rw [twoFormIntersection_comm, ← ha]
  exact twoFormIntersection_exact_closed hRic a u.val u.property

theorem smoothClosedIntersection_exact_left (hRic : RicciThree g)
    (u v : smoothClosedTwoForms (o := o)) (hu : u ∈ smoothExactTwoForms) :
    smoothClosedIntersection u v = 0 := by
  have h := smoothClosedIntersection_exact_right hRic v u hu
  exact (twoFormIntersection_comm u.val v.val).trans h

theorem twoFormIntersection_sub_left (u v w : smoothTwoForms o) :
    twoFormIntersection (u - v) w = twoFormIntersection u w - twoFormIntersection v w := by
  change smoothTwoFormL2Inner (u - v) (smoothTwoFormHodge o w) = _
  exact smoothTwoFormL2Inner_sub u v _

def deRhamIntersection (hRic : RicciThree g) :
    TwoFormDeRhamCohomology (o := o) →ₗ[ℝ] TwoFormDeRhamCohomology (o := o) →ₗ[ℝ] ℝ :=
  (smoothHarmonicIntersection (o := o)).compl₁₂
    (smoothHarmonicDeRhamEquiv hRic).symm.toLinearMap
    (smoothHarmonicDeRhamEquiv hRic).symm.toLinearMap

theorem harmonicRepresentative_intersection (hRic : RicciThree g)
    (u v : smoothClosedTwoForms (o := o)) :
    twoFormIntersection
      ((smoothHarmonicDeRhamEquiv hRic).symm ((smoothExactTwoForms (o := o)).mkQ u)).val
      v.val = twoFormIntersection u.val v.val := by
  let h := (smoothHarmonicDeRhamEquiv hRic).symm ((smoothExactTwoForms (o := o)).mkQ u)
  have he : smoothHarmonicToDeRham h = (smoothExactTwoForms (o := o)).mkQ u :=
    (smoothHarmonicDeRhamEquiv hRic).apply_symm_apply _
  have hm := (Submodule.Quotient.eq (smoothExactTwoForms (o := o))).mp he
  change h.val - u.val ∈ LinearMap.range (smoothOneFormExteriorLinear (o := o)) at hm
  obtain ⟨a, ha⟩ := hm
  have hz := twoFormIntersection_exact_closed hRic a v.val v.property
  change twoFormIntersection (smoothOneFormExteriorLinear a) v.val = 0 at hz
  rw [ha, twoFormIntersection_sub_left] at hz
  exact sub_eq_zero.mp hz

theorem deRhamIntersection_representatives (hRic : RicciThree g)
    (u v : smoothClosedTwoForms (o := o)) :
    deRhamIntersection hRic ((smoothExactTwoForms (o := o)).mkQ u)
      ((smoothExactTwoForms (o := o)).mkQ v) = twoFormIntersection u.val v.val := by
  let h := (smoothHarmonicDeRhamEquiv hRic).symm ((smoothExactTwoForms (o := o)).mkQ u)
  let k := (smoothHarmonicDeRhamEquiv hRic).symm ((smoothExactTwoForms (o := o)).mkQ v)
  change twoFormIntersection h.val k.val = _
  have hv : twoFormIntersection k.val h.val = twoFormIntersection v.val h.val :=
    harmonicRepresentative_intersection hRic v (smoothHarmonicToClosed h)
  exact (twoFormIntersection_comm h.val k.val).trans (hv.trans
    ((twoFormIntersection_comm v.val h.val).trans
      (harmonicRepresentative_intersection hRic u v)))

theorem deRhamIntersection_comm (hRic : RicciThree g)
    (u v : TwoFormDeRhamCohomology (o := o)) :
    deRhamIntersection hRic u v = deRhamIntersection hRic v u :=
  twoFormIntersection_comm _ _

theorem deRhamIntersection_nondegenerate (hRic : RicciThree g)
    (u : TwoFormDeRhamCohomology (o := o))
    (hu : ∀ v, deRhamIntersection hRic u v = 0) : u = 0 := by
  let E := smoothHarmonicDeRhamEquiv (o := o) hRic
  have hz : E.symm u = 0 := by
    apply smoothHarmonicIntersection_nondegenerate hRic
    intro v
    have ht := hu (E v)
    change smoothHarmonicIntersection (E.symm u) (E.symm (E v)) = 0 at ht
    rwa [E.symm_apply_apply] at ht
  have h := congrArg E hz
  rwa [E.apply_symm_apply, map_zero] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The inertia of the actual harmonic intersection form. The positive
and negative indices are the dimensions of the Hodge summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance harmonicSignatureAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

def harmonicIntersectionQuadratic : QuadraticForm ℝ (smoothHarmonicTwoForms (o := o)) :=
  LinearMap.BilinMap.toQuadraticMap (smoothHarmonicIntersection (o := o))

theorem harmonicIntersection_positive_definite (hRic : RicciThree g) :
    ((harmonicIntersectionQuadratic (o := o)).restrict
      (smoothHarmonicPositive hRic)).PosDef := by
  intro u hu
  change 0 < twoFormIntersection u.val.val u.val.val
  rw [smoothHarmonicIntersection_positive hRic u]
  apply lt_of_le_of_ne (smoothTwoFormL2Inner_nonneg _)
  intro hz
  apply hu
  exact Subtype.ext (Subtype.ext (smoothTwoFormL2Inner_definite _ hz.symm))

theorem harmonicIntersection_negative_definite (hRic : RicciThree g) :
    ((-harmonicIntersectionQuadratic (o := o)).restrict
      (smoothHarmonicNegative hRic)).PosDef := by
  intro u hu
  change 0 < -twoFormIntersection u.val.val u.val.val
  rw [smoothHarmonicIntersection_negative hRic u, neg_neg]
  apply lt_of_le_of_ne (smoothTwoFormL2Inner_nonneg _)
  intro hz
  apply hu
  exact Subtype.ext (Subtype.ext (smoothTwoFormL2Inner_definite _ hz.symm))

theorem harmonicIntersection_sigPos (hRic : RicciThree g) :
    sigPos (harmonicIntersectionQuadratic (o := o)) =
      Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  have hlo := le_sigPos_of_posDef
    (harmonicIntersectionQuadratic (o := o)) (harmonicIntersection_positive_definite hRic)
  have hhi := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := harmonicIntersectionQuadratic (o := o))
    (V := smoothHarmonicNegative hRic) (fun u hu => by
      change twoFormIntersection u.val u.val ≤ 0
      rw [smoothHarmonicIntersection_negative hRic ⟨u, hu⟩]
      exact neg_nonpos.mpr (smoothTwoFormL2Inner_nonneg _))
  have hd := (smoothHarmonicSumEquiv (o := o) hRic).finrank_eq
  rw [Module.finrank_prod] at hd
  omega

theorem harmonicIntersection_sigNeg (hRic : RicciThree g) :
    sigNeg (harmonicIntersectionQuadratic (o := o)) =
      Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  have hlo := le_sigNeg_of_negDef
    (harmonicIntersectionQuadratic (o := o)) (harmonicIntersection_negative_definite hRic)
  have hhi := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (Q := -harmonicIntersectionQuadratic (o := o))
    (V := smoothHarmonicPositive hRic) (fun u hu => by
      change -twoFormIntersection u.val u.val ≤ 0
      rw [smoothHarmonicIntersection_positive hRic ⟨u, hu⟩]
      exact neg_nonpos.mpr (smoothTwoFormL2Inner_nonneg _))
  change sigNeg (harmonicIntersectionQuadratic (o := o)) + _ ≤ _ at hhi
  have hd := (smoothHarmonicSumEquiv (o := o) hRic).finrank_eq
  rw [Module.finrank_prod] at hd
  omega

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual exact and coexact smooth one-form eigensections and their
orthogonality. The coexact eigenspaces are finite images of the proved
two-form eigenspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothOneFormWrap : smoothCovariantFields M 1 →ₗ[ℝ] SmoothL2OneForm o where
  toFun u := ⟨u⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def smoothOneFormL2Linear : smoothCovariantFields M 1 →ₗ[ℝ] OneFormL2 o :=
  smoothOneFormToL2.toLinearMap.comp smoothOneFormWrap

theorem smoothOneFormL2Linear_injective : Function.Injective (smoothOneFormL2Linear (o := o)) := by
  intro u v h
  exact congrArg SmoothL2OneForm.toSmooth (smoothOneFormToL2_injective h)

theorem smoothOneFormL2Linear_inner (u v : smoothCovariantFields M 1) :
    inner ℝ (smoothOneFormL2Linear (o := o) u) (smoothOneFormL2Linear (o := o) v) =
      smoothOneFormL2Pairing (o := o) u v := smoothOneFormToL2_inner _ _

theorem smoothOneFormL2Pairing_smul_right (r : ℝ) (u v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) u (r • v) = r * smoothOneFormL2Pairing (o := o) u v := by
  rw [smoothOneFormL2Pairing_comm, smoothOneFormL2Pairing_smul,
    smoothOneFormL2Pairing_comm v u]

theorem oneForm_exact_coexact_orthogonal (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) (u : smoothTwoForms o) :
    inner ℝ (smoothOneFormL2Linear (o := o) (smoothScalarDifferential g f))
      (smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u)) = 0 := by
  rw [smoothOneFormL2Linear_inner, smoothScalarDifferential_pairing hRic]
  have hz := smoothTwoFormCodifferential_divergence hRic u
  have hpoint (x : M) : oneFormDivergence g (smoothTwoFormCodifferentialField u) x = 0 :=
    congrArg (fun a : SmoothScalar (M := M) => a.val x) hz
  simp only [hpoint, mul_zero, integral_zero, neg_zero]

theorem smoothOneForm_eigen_orthogonal (hRic : RicciThree g)
    (u v : smoothCovariantFields M 1) (κ l : ℝ)
    (hu : smoothOneFormHodgeLaplacian (o := o) u = κ • u)
    (hv : smoothOneFormHodgeLaplacian (o := o) v = l • v) (hne : κ ≠ l) :
    inner ℝ (smoothOneFormL2Linear (o := o) u) (smoothOneFormL2Linear (o := o) v) = 0 := by
  rw [smoothOneFormL2Linear_inner]
  have he := smoothOneFormHodgeLaplacian_selfAdjoint (o := o) hRic u v
  rw [hu, hv, smoothOneFormL2Pairing_smul, smoothOneFormL2Pairing_smul_right] at he
  exact (mul_eq_zero.mp (show (κ - l) * smoothOneFormL2Pairing (o := o) u v = 0 by
    nlinarith only [he])).resolve_left (sub_ne_zero.mpr hne)

def oneFormCodiffEigenMap (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :
    TwoFormSmoothEigenSpace hRic μ →ₗ[ℝ] OneFormL2 o :=
  smoothOneFormL2Linear.comp
    (smoothTwoFormCodifferentialLinear.comp (TwoFormSmoothEigenSpace hRic μ).subtype)

def OneFormCoexactSpectralSpace (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : Submodule ℝ (OneFormL2 o) :=
  (oneFormCodiffEigenMap hRic μ).range

instance oneFormCoexactSpectralFinite (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    FiniteDimensional ℝ (OneFormCoexactSpectralSpace hRic μ) := by
  let : FiniteDimensional ℝ (TwoFormSmoothEigenSpace hRic μ) := twoFormSmoothEigenFinite hRic μ
  exact Module.Finite.range (oneFormCodiffEigenMap hRic μ)

theorem oneFormCoexactSpectral_representation (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (v : OneFormCoexactSpectralSpace hRic μ) :
    ∃ u : smoothTwoForms o,
      smoothHodgeLaplacian hRic u = (μ.val⁻¹ - 1) • u ∧
      v.val = smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u) := by
  obtain ⟨u, hu⟩ := v.property
  exact ⟨u.val, Module.End.mem_eigenspace_iff.mp u.property, hu.symm⟩

theorem smoothCodiff_eigen (hRic : RicciThree g) (u : smoothTwoForms o) (κ : ℝ)
    (hu : smoothHodgeLaplacian hRic u = κ • u) :
    smoothOneFormHodgeLaplacian (o := o) (smoothTwoFormCodifferentialField u) =
      κ • smoothTwoFormCodifferentialField u := by
  rw [smoothOneFormHodgeLaplacian_codifferential hRic, hu]
  exact (smoothTwoFormCodifferentialLinear (o := o)).map_smul κ u

theorem oneFormCoexactSpectral_orthogonal (hRic : RicciThree g)
    (μ ν : TwoFormSpectralValue (o := o) hRic) (hμν : μ ≠ ν)
    (u : OneFormCoexactSpectralSpace hRic μ) (v : OneFormCoexactSpectralSpace hRic ν) :
    inner ℝ u.val v.val = 0 := by
  obtain ⟨a, ha, hua⟩ := oneFormCoexactSpectral_representation hRic μ u
  obtain ⟨b, hb, hvb⟩ := oneFormCoexactSpectral_representation hRic ν v
  rw [hua, hvb]
  apply smoothOneForm_eigen_orthogonal hRic _ _ _ _
    (smoothCodiff_eigen hRic a _ ha) (smoothCodiff_eigen hRic b _ hb)
  intro he
  apply hμν
  apply Subtype.ext
  apply inv_injective
  exact sub_left_injective he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth mean-zero solvability for minus the actual scalar Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def smoothScalarPositiveLaplacian (g : SmoothMetric M) :
    SmoothScalar (M := M) →ₗ[ℝ] SmoothScalar (M := M) :=
  -((smoothOneFormDivergence g).comp (smoothScalarDifferentialLinear g))

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]

theorem exists_smoothPositivePoisson (o : FrameOrientation g) (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) (hf : smoothScalarMean g o f = 0) :
    ∃ φ : SmoothScalar (M := M), smoothScalarPositiveLaplacian g φ = f := by
  obtain ⟨φ, hφ, hLap⟩ := actual_petersen_poisson g o hRic
    (fun x => -f.val x) f.property.neg
  refine ⟨⟨φ, hφ⟩, ?_⟩
  apply Subtype.ext
  funext x
  let F : SmoothScalar (M := M) := ⟨φ, hφ⟩
  let e := frameAt g x
  have he := hLap e
  change (∫ e, f.val e.base ∂canonicalFrameMeasure g o) = 0 at hf
  rw [integral_neg, hf, neg_zero, sub_zero] at he
  change -oneFormDivergence g (smoothScalarDifferential g F) x = f.val x
  change -oneFormDivergence g (smoothScalarDifferential g F) e.base = f.val e.base
  rw [oneFormDivergence_differential]
  exact neg_eq_iff_eq_neg.mpr he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every nonharmonic two-form eigenspace has vanishing Hodge trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormSmoothEigenDDelta (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :
    Module.End ℝ (TwoFormSmoothEigenSpace hRic μ) where
  toFun u := ⟨smoothTwoFormDDelta u.val, by
    apply Module.End.mem_eigenspace_iff.mpr
    change smoothHodgeLaplacian hRic (smoothTwoFormDDelta u.val) =
      (μ.val⁻¹ - 1) • smoothTwoFormDDelta u.val
    rw [smoothHodgeLaplacian_DDelta]
    exact smoothTwoFormDDelta_eigen_square hRic _ u.val
      (Module.End.mem_eigenspace_iff.mp u.property)⟩
  map_add' u v := Subtype.ext (smoothTwoFormDDelta_add u.val v.val)
  map_smul' r u := Subtype.ext (smoothTwoFormDDelta_smul r u.val)

def twoFormSmoothEigenHodge (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :
    Module.End ℝ (TwoFormSmoothEigenSpace hRic μ) where
  toFun u := ⟨smoothTwoFormHodge o u.val, by
    apply Module.End.mem_eigenspace_iff.mpr
    change smoothHodgeLaplacian hRic (smoothTwoFormHodge o u.val) =
      (μ.val⁻¹ - 1) • smoothTwoFormHodge o u.val
    have hu : smoothHodgeLaplacian hRic u.val = (μ.val⁻¹ - 1) • u.val :=
      Module.End.mem_eigenspace_iff.mp u.property
    rw [smoothHodgeLaplacian_hodge hRic, hu, map_smul]⟩
  map_add' u v := Subtype.ext (map_add (smoothTwoFormHodge o) u.val v.val)
  map_smul' r u := Subtype.ext (map_smul (smoothTwoFormHodge o) r u.val)

theorem twoFormSmoothEigenDDelta_square (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormSmoothEigenDDelta hRic μ * twoFormSmoothEigenDDelta hRic μ =
      (μ.val⁻¹ - 1) • twoFormSmoothEigenDDelta hRic μ := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact smoothTwoFormDDelta_eigen_square hRic _ u.val
    (Module.End.mem_eigenspace_iff.mp u.property)

theorem twoFormSmoothEigenDDelta_hodge_zero (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormSmoothEigenDDelta hRic μ * twoFormSmoothEigenHodge hRic μ *
      twoFormSmoothEigenDDelta hRic μ = 0 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact smoothTwoFormDDelta_hodge_DDelta hRic u.val

theorem twoFormSmoothEigenHodge_anticommutator (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormSmoothEigenHodge hRic μ * twoFormSmoothEigenDDelta hRic μ +
      twoFormSmoothEigenDDelta hRic μ * twoFormSmoothEigenHodge hRic μ =
        (μ.val⁻¹ - 1) • twoFormSmoothEigenHodge hRic μ := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  have he := congrArg (smoothTwoFormHodge o)
    ((smoothHodgeLaplacian_dDelta_hodge hRic u.val).symm.trans
      (Module.End.mem_eigenspace_iff.mp u.property))
  rw [map_add, smoothTwoFormHodge_involutive, map_smul] at he
  exact he

theorem twoFormSmoothEigenHodge_trace_zero (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (hμ : μ.val ≠ 1) :
    LinearMap.trace ℝ (TwoFormSmoothEigenSpace hRic μ) (twoFormSmoothEigenHodge hRic μ) = 0 := by
  apply finite_hodge_trace_cancel (V := TwoFormSmoothEigenSpace hRic μ)
    (twoFormSmoothEigenDDelta hRic μ)
    (twoFormSmoothEigenHodge hRic μ) (μ.val⁻¹ - 1)
  · simpa only [ne_eq, sub_eq_zero, inv_eq_one] using hμ
  · exact twoFormSmoothEigenDDelta_square hRic μ
  · exact twoFormSmoothEigenDDelta_hodge_zero hRic μ
  · exact twoFormSmoothEigenHodge_anticommutator hRic μ

end
end PositiveEinsteinFour.Geometry
end


section

/-! Absolute convergence of the actual positive-time spectral heat kernel.
Splitting the time in half reduces convergence to the proved diagonal bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatSection_pointwise_square_summable (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (x : M) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic =>
      ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val x‖ ^ 2) := by
  obtain ⟨C, _, hC⟩ := twoFormHeat_diagonal_bound (o := o) hRic t ht
  exact summable_of_sum_le (fun _ => sq_nonneg _) (fun s => hC s x)

def twoFormHeatKernelTerm (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x y : M) (i : TwoFormEigenIndex (o := o) hRic) : TwoFormFour →L[ℝ] TwoFormFour :=
  InnerProductSpace.rankOne ℝ
    ((twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x)
    ((twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val y)

theorem twoFormHeatKernelTerm_norm_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x y : M) : Summable (fun i : TwoFormEigenIndex (o := o) hRic =>
      ‖twoFormHeatKernelTerm hRic t ht x y i‖) := by
  have hx := twoFormHeatSection_pointwise_square_summable (o := o) hRic (t / 2) (half_pos ht) x
  have hy := twoFormHeatSection_pointwise_square_summable (o := o) hRic (t / 2) (half_pos ht) y
  apply (hx.add hy).of_norm_bounded
  intro i
  rw [norm_norm, twoFormHeatKernelTerm, InnerProductSpace.norm_rankOne]
  nlinarith [sq_nonneg
    (‖(twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x‖ -
      ‖(twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val y‖)]

theorem twoFormHeatKernelTerm_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x y : M) : Summable (twoFormHeatKernelTerm (o := o) hRic t ht x y) := by
  have := FiniteDimensional.complete ℝ (TwoFormFour →L[ℝ] TwoFormFour)
  exact (twoFormHeatKernelTerm_norm_summable (o := o) hRic t ht x y).of_norm

def twoFormHeatKernel (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (x y : M) :
    TwoFormFour →L[ℝ] TwoFormFour :=
  ∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatKernelTerm hRic t ht x y i

theorem twoFormHeatKernel_hasSum (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (x y : M) :
    HasSum (twoFormHeatKernelTerm (o := o) hRic t ht x y) (twoFormHeatKernel (o := o) hRic t ht x y) :=
  (twoFormHeatKernelTerm_summable hRic t ht x y).hasSum

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signature of the actual degree-two de Rham intersection form,
defined by its maximal positive and negative dimensions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance deRhamSignatureHarmonicAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

local instance deRhamSignatureClosedAddGroup : AddCommGroup (smoothClosedTwoForms (o := o)) :=
  Submodule.addCommGroup _

def deRhamIntersectionQuadratic (hRic : RicciThree g) :
    QuadraticForm ℝ (TwoFormDeRhamCohomology (o := o)) :=
  LinearMap.BilinMap.toQuadraticMap (deRhamIntersection hRic)

def harmonicDeRhamIntersectionIsometry (hRic : RicciThree g) :
    (harmonicIntersectionQuadratic (o := o)).IsometryEquiv
      (deRhamIntersectionQuadratic (o := o) hRic) where
  toLinearEquiv := smoothHarmonicDeRhamEquiv hRic
  map_app' u := by
    change smoothHarmonicIntersection
      ((smoothHarmonicDeRhamEquiv hRic).symm ((smoothHarmonicDeRhamEquiv hRic) u))
      ((smoothHarmonicDeRhamEquiv hRic).symm ((smoothHarmonicDeRhamEquiv hRic) u)) =
        smoothHarmonicIntersection u u
    rw [LinearEquiv.symm_apply_apply]

theorem deRhamIntersection_sigPos (hRic : RicciThree g) :
    sigPos (deRhamIntersectionQuadratic (o := o) hRic) =
      Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) := by
  have he : (harmonicIntersectionQuadratic (o := o)).Equivalent
      (deRhamIntersectionQuadratic hRic) := ⟨harmonicDeRhamIntersectionIsometry hRic⟩
  exact he.sigPos_eq.symm.trans (harmonicIntersection_sigPos hRic)

theorem deRhamIntersection_sigNeg (hRic : RicciThree g) :
    sigNeg (deRhamIntersectionQuadratic (o := o) hRic) =
      Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) := by
  have he : (harmonicIntersectionQuadratic (o := o)).Equivalent
      (deRhamIntersectionQuadratic hRic) := ⟨harmonicDeRhamIntersectionIsometry hRic⟩
  exact he.sigNeg_eq.symm.trans (harmonicIntersection_sigNeg hRic)

def deRhamSignature (hRic : RicciThree g) : ℤ :=
  (sigPos (deRhamIntersectionQuadratic (o := o) hRic) : ℤ) -
    (sigNeg (deRhamIntersectionQuadratic (o := o) hRic) : ℤ)

theorem deRhamSignature_hodge (hRic : RicciThree g) :
    deRhamSignature (o := o) hRic =
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℤ) -
        (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℤ) := by
  rw [deRhamSignature, deRhamIntersection_sigPos, deRhamIntersection_sigNeg]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual codifferential and Hodge star on each two-form eigenspace.
These identities give the degree-one multiplicities in the Euler heat trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothCodifferential_DDelta_eigen (hRic : RicciThree g)
    (u : smoothTwoForms o) (κ : ℝ) (hu : smoothHodgeLaplacian hRic u = κ • u) :
    smoothTwoFormCodifferentialField (smoothTwoFormDDelta u) =
      κ • smoothTwoFormCodifferentialField u := by
  have h := smoothCodiff_eigen hRic u κ hu
  rw [smoothOneFormHodgeLaplacian_apply] at h
  have hz : smoothScalarDifferential g
      (smoothOneFormDivergence g (smoothTwoFormCodifferentialField u)) = 0 := by
    rw [smoothTwoFormCodifferential_divergence hRic]
    exact (smoothScalarDifferentialLinear g).map_zero
  rw [hz, sub_zero] at h
  exact h

theorem twoFormEigenCodiff_DDelta (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    (oneFormCodiffEigenMap hRic μ).comp (twoFormSmoothEigenDDelta hRic μ) =
      (μ.val⁻¹ - 1) • oneFormCodiffEigenMap hRic μ := by
  apply LinearMap.ext
  intro u
  change smoothOneFormL2Linear (o := o)
    (smoothTwoFormCodifferentialField (smoothTwoFormDDelta u.val)) =
      (μ.val⁻¹ - 1) • smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u.val)
  rw [smoothCodifferential_DDelta_eigen hRic u.val _
    (Module.End.mem_eigenspace_iff.mp u.property), map_smul]

theorem twoFormEigenCodiff_hodge_DDelta (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    ((oneFormCodiffEigenMap hRic μ).comp (twoFormSmoothEigenHodge hRic μ)).comp
      (twoFormSmoothEigenDDelta hRic μ) = 0 := by
  apply LinearMap.ext
  intro u
  have hz := (smoothTwoForm_closed_iff_codifferential_hodge (smoothTwoFormDDelta u.val)).mp
    (smoothTwoFormDDelta_closed hRic u.val)
  change smoothOneFormL2Linear (o := o)
    (smoothTwoFormCodifferentialField (smoothTwoFormHodge o (smoothTwoFormDDelta u.val))) = 0
  rw [hz, map_zero]

theorem twoFormEigenHodge_square (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormSmoothEigenHodge hRic μ * twoFormSmoothEigenHodge hRic μ = 1 := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact smoothTwoFormHodge_involutive o u.val

theorem twoFormEigen_DDelta_hodge_split (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormSmoothEigenDDelta hRic μ +
      twoFormSmoothEigenHodge hRic μ * twoFormSmoothEigenDDelta hRic μ *
        twoFormSmoothEigenHodge hRic μ =
      (μ.val⁻¹ - 1) • (1 : Module.End ℝ (TwoFormSmoothEigenSpace hRic μ)) := by
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  exact (smoothHodgeLaplacian_dDelta_hodge hRic u.val).symm.trans
    (Module.End.mem_eigenspace_iff.mp u.property)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthonormal bases of the actual finite coexact one-form eigenspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev OneFormCoexactEigenIndex (hRic : RicciThree g) :=
  Σ μ : TwoFormSpectralValue (o := o) hRic,
    Fin (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ))

def oneFormCoexactEigenvector (hRic : RicciThree g) (i : OneFormCoexactEigenIndex (o := o) hRic) :
    OneFormL2 o := (stdOrthonormalBasis ℝ (OneFormCoexactSpectralSpace hRic i.1) i.2).val

theorem oneFormCoexactEigenvector_orthonormal (hRic : RicciThree g) :
    Orthonormal ℝ (oneFormCoexactEigenvector (o := o) hRic) := by
  have hO : OrthogonalFamily (E := OneFormL2 o) ℝ
      (fun μ : TwoFormSpectralValue (o := o) hRic => OneFormCoexactSpectralSpace (o := o) hRic μ)
      (fun μ => (OneFormCoexactSpectralSpace (o := o) hRic μ).subtypeₗᵢ) := by
    intro μ ν hμν u v
    exact oneFormCoexactSpectral_orthogonal hRic μ ν hμν u v
  exact hO.orthonormal_sigma_orthonormal
    (fun μ => (stdOrthonormalBasis ℝ (OneFormCoexactSpectralSpace hRic μ)).orthonormal)

theorem oneFormCoexact_mem_span (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (u : OneFormCoexactSpectralSpace hRic μ) :
    u.val ∈ Submodule.span ℝ (Set.range (oneFormCoexactEigenvector (o := o) hRic)) := by
  let b := stdOrthonormalBasis ℝ (OneFormCoexactSpectralSpace hRic μ)
  have he := congrArg (OneFormCoexactSpectralSpace hRic μ).subtype (b.sum_repr u)
  simp only [map_sum, map_smul] at he
  change (∑ j, (b.repr u) j • (b j : OneFormL2 o)) = u.val at he
  rw [← he]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨μ, j⟩, rfl⟩

theorem oneFormCoexactEigenvector_smooth (hRic : RicciThree g)
    (i : OneFormCoexactEigenIndex (o := o) hRic) :
    ∃ u : smoothTwoForms o,
      oneFormCoexactEigenvector hRic i =
        smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u) ∧
      smoothOneFormHodgeLaplacian (o := o) (smoothTwoFormCodifferentialField u) =
        (i.1.val⁻¹ - 1) • smoothTwoFormCodifferentialField u := by
  obtain ⟨u, hu, he⟩ := oneFormCoexactSpectral_representation hRic i.1
    (stdOrthonormalBasis ℝ (OneFormCoexactSpectralSpace hRic i.1) i.2)
  exact ⟨u, he, smoothCodiff_eigen hRic u _ hu⟩

theorem oneFormCoexactEigenvector_rate_pos (hRic : RicciThree g)
    (i : OneFormCoexactEigenIndex (o := o) hRic) : 0 < i.1.val⁻¹ - 1 := by
  have hn : 0 ≤ i.1.val⁻¹ - 1 := sub_nonneg.mpr
    ((one_le_inv₀ (twoFormSpectralValue_bounds hRic i.1).1).mpr
      (twoFormSpectralValue_bounds hRic i.1).2)
  by_contra hp
  have hz : i.1.val⁻¹ - 1 = 0 := le_antisymm (le_of_not_gt hp) hn
  obtain ⟨u, he, hu⟩ := oneFormCoexactEigenvector_smooth hRic i
  rw [hz, zero_smul] at hu
  have hu0 := smoothOneFormHodgeLaplacian_eq_zero hRic _ hu
  have he0 : oneFormCoexactEigenvector hRic i = 0 := by rw [he, hu0, map_zero]
  have hnorm := (oneFormCoexactEigenvector_orthonormal hRic).1 i
  rw [he0, norm_zero] at hnorm
  exact zero_ne_one hnorm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normalized gradients of the positive scalar modes form an actual
orthonormal family of exact one-form eigenvectors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

local instance (g : SmoothMetric M) : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarEigen_differential_inner (i j : ScalarBaseEigenIndex g o d) :
    inner ℝ (smoothOneFormL2Linear (o := o)
      (smoothScalarDifferential g (scalarBaseEigenfunction g o d i)))
      (smoothOneFormL2Linear (o := o)
        (smoothScalarDifferential g (scalarBaseEigenfunction g o d j))) =
      scalarBaseHeatRate g o d j *
        inner ℝ (scalarBaseEigenvector g o d i) (scalarBaseEigenvector g o d j) := by
  rw [smoothOneFormL2Linear_inner, smoothScalarDifferential_dirichlet d,
    smoothScalarDirichlet_laplacian_pairing,
    ← smoothScalarLaplacian_valueL2, scalarBaseEigenfunction_laplacian,
    map_smul, real_inner_smul_right]
  have hinner : inner ℝ
      (smoothScalarValueL2 g (canonicalFrameMeasure g o) (scalarBaseEigenfunction g o d i))
      (smoothScalarValueL2 g (canonicalFrameMeasure g o) (scalarBaseEigenfunction g o d j)) =
      inner ℝ (scalarBaseEigenvector g o d i) (scalarBaseEigenvector g o d j) := by
    rw [scalarBaseEigenfunction_L2, scalarBaseEigenfunction_L2]
    rw [← scalarBasePullback_smooth g o (scalarBaseEigenfunction g o d i),
      ← scalarBasePullback_smooth g o (scalarBaseEigenfunction g o d j)]
    exact (scalarBasePullback g o).inner_map_map _ _
  rw [hinner]
  ring

theorem scalarEigen_differential_zero (i : ScalarBaseEigenIndex g o d)
    (hi : scalarBaseHeatRate g o d i = 0) :
    smoothOneFormL2Linear (o := o)
      (smoothScalarDifferential g (scalarBaseEigenfunction g o d i)) = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [scalarEigen_differential_inner, hi, zero_mul]

abbrev OneFormExactEigenIndex := {i : ScalarBaseEigenIndex g o d // 0 < scalarBaseHeatRate g o d i}

def oneFormExactEigenvector (i : OneFormExactEigenIndex g o d) : OneFormL2 o :=
  (Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ •
    smoothOneFormL2Linear (o := o)
      (smoothScalarDifferential g (scalarBaseEigenfunction g o d i.val))

theorem oneFormExactEigenvector_orthonormal : Orthonormal ℝ (oneFormExactEigenvector g o d) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  simp only [oneFormExactEigenvector, real_inner_smul_left, real_inner_smul_right,
    scalarEigen_differential_inner,
    orthonormal_iff_ite.mp (scalarBaseEigenvector_orthonormal g o d)]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hs : (Real.sqrt (scalarBaseHeatRate g o d i.val)) ^ 2 =
        scalarBaseHeatRate g o d i.val := Real.sq_sqrt i.property.le
    have hn : Real.sqrt (scalarBaseHeatRate g o d i.val) ≠ 0 :=
      (Real.sqrt_pos.mpr i.property).ne'
    field_simp
    nlinarith only [hs]
  · have hval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    simp only [hij, hval, ite_false, mul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Isometric frame-coordinate realization of the actual one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

def smoothOneFormEuclideanValue (u : smoothCovariantFields M 1) : C(FrameBundle g, FourSpace) where
  toFun e := WithLp.toLp 2 (fun i : Fin 4 => covariantFieldFramed g u.val e ![i])
  continuous_toFun := (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i =>
    (continuous_apply ![i]).comp u.property.continuous_framed))

def smoothOneFormFrameLinear : SmoothL2OneForm o →ₗ[ℝ] Lp FourSpace 2 (canonicalFrameMeasure g o) where
  toFun u := ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothOneFormEuclideanValue (g := g) u.toSmooth)
  map_add' u v := by
    have he : smoothOneFormEuclideanValue (g := g) (u + v).toSmooth =
        smoothOneFormEuclideanValue (g := g) u.toSmooth + smoothOneFormEuclideanValue (g := g) v.toSmooth := by
      ext e i
      exact congrFun (covariantFieldFramed_add (g := g) u.toSmooth.val v.toSmooth.val e) ![i]
    change ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ _ = _
    rw [he, map_add]
  map_smul' r u := by
    have he : smoothOneFormEuclideanValue (g := g) (r • u).toSmooth =
        r • smoothOneFormEuclideanValue (g := g) u.toSmooth := by
      ext e i
      exact congrFun (covariantFieldFramed_smul (g := g) r u.toSmooth.val e) ![i]
    change ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ _ = _
    rw [he, map_smul]
    rfl

theorem smoothOneFormFrameLinear_norm (u : SmoothL2OneForm o) :
    ‖smoothOneFormFrameLinear u‖ = ‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← real_inner_self_eq_norm_sq]
  have he := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
    (smoothOneFormEuclideanValue (g := g) u.toSmooth)
  change (∫ e, inner ℝ ((smoothOneFormFrameLinear u : Lp FourSpace 2 (canonicalFrameMeasure g o)) e)
      ((smoothOneFormFrameLinear u : Lp FourSpace 2 (canonicalFrameMeasure g o)) e)
      ∂canonicalFrameMeasure g o) = smoothOneFormL2Pairing u.toSmooth u.toSmooth
  unfold smoothOneFormL2Pairing
  apply integral_congr_ae
  filter_upwards [he] with e he
  change (smoothOneFormFrameLinear u : FrameBundle g → FourSpace) e = _ at he
  rw [he]
  simp only [PiLp.inner_apply, smoothOneFormEuclideanValue, ContinuousMap.coe_mk,
    Real.inner_apply]

def smoothOneFormFrameL2 : SmoothL2OneForm o →L[ℝ] Lp FourSpace 2 (canonicalFrameMeasure g o) :=
  smoothOneFormFrameLinear.mkContinuous 1 (fun u => by rw [one_mul, smoothOneFormFrameLinear_norm])

def oneFormFrameL2 : OneFormL2 o →L[ℝ] Lp FourSpace 2 (canonicalFrameMeasure g o) :=
  (smoothOneFormFrameL2 (o := o)).fromCompletion

theorem oneFormFrameL2_smooth (u : smoothCovariantFields M 1) :
    oneFormFrameL2 (smoothOneFormL2Linear (o := o) u) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothOneFormEuclideanValue (g := g) u) :=
  ContinuousLinearMap.fromCompletion_apply_coe _ (⟨u⟩ : SmoothL2OneForm o)

theorem oneFormFrameL2_norm (u : OneFormL2 o) : ‖oneFormFrameL2 u‖ = ‖u‖ := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (oneFormFrameL2.continuous.norm) continuous_norm) ?_
  intro v
  change ‖oneFormFrameL2 (smoothOneFormToL2 v)‖ = ‖smoothOneFormToL2 v‖
  rw [smoothOneFormToL2.norm_map]
  have hv := ContinuousLinearMap.fromCompletion_apply_coe (smoothOneFormFrameL2 (o := o)) v
  change oneFormFrameL2 (smoothOneFormToL2 v) = smoothOneFormFrameLinear v at hv
  rw [hv, smoothOneFormFrameLinear_norm]

theorem oneFormFrameL2_injective : Function.Injective (oneFormFrameL2 (o := o)) := by
  intro u v h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← oneFormFrameL2_norm, map_sub, h, sub_self, norm_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual infinite spectral kernel has the expected integrated
diagonal trace. Absolute convergence justifies both exchanges. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

def twoFormFiberTrace : (TwoFormFour →L[ℝ] TwoFormFour) →L[ℝ] ℝ :=
  ((LinearMap.trace ℝ TwoFormFour).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

theorem twoFormFiberTrace_apply (A : TwoFormFour →L[ℝ] TwoFormFour) :
    twoFormFiberTrace A = LinearMap.trace ℝ TwoFormFour A.toLinearMap := rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

instance twoFormEigenIndexCountable (hRic : RicciThree g) :
    Countable (TwoFormEigenIndex (o := o) hRic) := by
  apply Set.countable_univ_iff.mp
  have h := (twoFormHeat_weight_summable (o := o) hRic 1 zero_lt_one).countable_support
  convert h using 1
  ext i
  simp only [Set.mem_univ, Function.mem_support, twoFormHeatWeight, ne_eq, Real.exp_ne_zero,
    not_false_eq_true]

theorem twoFormHeatKernel_diagonal_trace (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x : M) :
    twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x) =
      ∑' i : TwoFormEigenIndex (o := o) hRic,
        ‖(twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x‖ ^ 2 := by
  have h := (twoFormHeatKernel_hasSum (o := o) hRic t ht x x).mapL twoFormFiberTrace
  simpa only [twoFormFiberTrace_apply, twoFormHeatKernelTerm, InnerProductSpace.trace_rankOne,
    real_inner_self_eq_norm_sq] using h.tsum_eq.symm

theorem twoFormHeatWeight_half_sq (hRic : RicciThree g) (t : ℝ≥0)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormHeatWeight hRic (t / 2) μ ^ 2 = twoFormHeatWeight hRic t μ := by
  simp only [twoFormHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

theorem twoFormHeatKernel_trace_integral (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x) ∂normalizedVolume g) =
      ∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1 := by
  have := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let F := fun (i : TwoFormEigenIndex (o := o) hRic) (x : M) =>
    ‖(twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x‖ ^ 2
  have hFi (i : TwoFormEigenIndex (o := o) hRic) : Integrable (F i) (normalizedVolume g) :=
    ((smoothTwoForm_norm_continuous _).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFsum : Summable (fun i => ∫ x, ‖F i x‖ ∂normalizedVolume g) := by
    have h := twoFormHeat_weight_square_summable (o := o) hRic (t / 2) (half_pos ht)
    apply h.congr
    intro i
    simp only [F, Real.norm_eq_abs, abs_sq]
    exact (twoFormHeatSection_eigen_integral hRic (t / 2) (half_pos ht) i).symm
  simp_rw [twoFormHeatKernel_diagonal_trace]
  change (∫ x, ∑' i, F i x ∂normalizedVolume g) = _
  rw [← integral_tsum_of_summable_integral_norm hFi hFsum]
  apply tsum_congr
  intro i
  exact (twoFormHeatSection_eigen_integral hRic (t / 2) (half_pos ht) i).trans
    (twoFormHeatWeight_half_sq hRic t i.1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer of Hodge trace cancellation to the actual L2 eigenspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormEigenspaceHodge (hRic : RicciThree g) (μ : ℝ) :
    Module.End ℝ (Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap μ) where
  toFun f := ⟨twoFormL2Hodge f.val, twoFormResolvent_eigenspace_hodge hRic μ f.val f.property⟩
  map_add' f h := Subtype.ext (map_add twoFormL2Hodge f.val h.val)
  map_smul' r f := Subtype.ext (map_smul twoFormL2Hodge r f.val)

theorem twoFormSmoothEigenEquiv_hodge (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (u : TwoFormSmoothEigenSpace hRic μ) :
    twoFormSmoothEigenEquiv hRic μ (twoFormSmoothEigenHodge hRic μ u) =
      twoFormEigenspaceHodge hRic μ.val (twoFormSmoothEigenEquiv hRic μ u) := by
  apply Subtype.ext
  exact (twoFormL2Hodge_smooth (u.val : SmoothL2TwoForm o)).symm

theorem twoFormEigenspaceHodge_conj (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    (twoFormSmoothEigenEquiv hRic μ).conj (twoFormSmoothEigenHodge hRic μ) =
      twoFormEigenspaceHodge hRic μ.val := by
  apply LinearMap.ext
  intro f
  obtain ⟨u, rfl⟩ := (twoFormSmoothEigenEquiv hRic μ).surjective f
  simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact twoFormSmoothEigenEquiv_hodge hRic μ u

theorem twoFormEigenspaceHodge_trace_zero (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (hμ : μ.val ≠ 1) :
    LinearMap.trace ℝ (TwoFormSpectralSpace hRic μ) (twoFormEigenspaceHodge hRic μ.val) = 0 := by
  rw [← twoFormEigenspaceHodge_conj]
  exact (LinearMap.trace_conj' (R := ℝ) (M := TwoFormSmoothEigenSpace hRic μ)
    (N := TwoFormSpectralSpace hRic μ) (twoFormSmoothEigenHodge hRic μ)
    (twoFormSmoothEigenEquiv hRic μ)).trans (twoFormSmoothEigenHodge_trace_zero hRic μ hμ)

theorem twoFormEigenspaceHodge_trace_basis (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    LinearMap.trace ℝ (TwoFormSpectralSpace hRic μ) (twoFormEigenspaceHodge hRic μ.val) =
      ∑ j : Fin (Module.finrank ℝ (TwoFormSpectralSpace hRic μ)),
        inner ℝ (twoFormEigenvector hRic ⟨μ,j⟩) (twoFormL2Hodge (twoFormEigenvector hRic ⟨μ,j⟩)) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TwoFormSpectralSpace hRic μ))]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The trace on the harmonic eigenspace is the difference of the two
actual harmonic Hodge dimensions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance harmonicTraceAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

theorem smoothHarmonicHodge_trace (hRic : RicciThree g) :
    LinearMap.trace ℝ (smoothHarmonicTwoForms (o := o)) (smoothHarmonicHodge hRic) =
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) -
        (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℝ) := by
  let E := smoothHarmonicSumEquiv (o := o) hRic
  let D : Module.End ℝ (smoothHarmonicPositive (o := o) hRic ×
      smoothHarmonicNegative (o := o) hRic) :=
    LinearMap.prodMap LinearMap.id (-LinearMap.id)
  have hcomm (u) : E (D u) = smoothHarmonicHodge hRic (E u) := by
    change u.1.val + -u.2.val = smoothHarmonicHodge hRic (u.1.val + u.2.val)
    rw [map_add, smoothHarmonicPositive_star, smoothHarmonicNegative_star]
  have he : E.conj D = smoothHarmonicHodge hRic := by
    apply LinearMap.ext
    intro w
    obtain ⟨u, rfl⟩ := E.surjective w
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact hcomm u
  rw [← he, LinearMap.trace_conj']
  change LinearMap.trace ℝ _ (LinearMap.prodMap LinearMap.id (-LinearMap.id)) = _
  rw [LinearMap.trace_prodMap']
  have hn := (LinearMap.trace ℝ (smoothHarmonicNegative (o := o) hRic)).map_neg
    (LinearMap.id : Module.End ℝ (smoothHarmonicNegative (o := o) hRic))
  rw [hn, LinearMap.trace_id, LinearMap.trace_id]
  rfl

theorem smoothHarmonicResolventEquiv_val (hRic : RicciThree g)
    (u : smoothHarmonicTwoForms (o := o)) :
    (smoothHarmonicResolventEquiv hRic u).val =
      smoothTwoFormToL2 (u.val : SmoothL2TwoForm o) := by
  change twoFormH1ToL2 (smoothTwoFormToH1 (u.val : SmoothH1TwoForm o)) = _
  exact twoFormH1ToL2_smooth (u.val : SmoothH1TwoForm o)

theorem smoothHarmonicResolventEquiv_hodge (hRic : RicciThree g)
    (u : smoothHarmonicTwoForms (o := o)) :
    smoothHarmonicResolventEquiv hRic (smoothHarmonicHodge hRic u) =
      twoFormEigenspaceHodge hRic 1 (smoothHarmonicResolventEquiv hRic u) := by
  apply Subtype.ext
  rw [smoothHarmonicResolventEquiv_val]
  change smoothTwoFormToL2 (smoothL2Hodge (u.val : SmoothL2TwoForm o)) =
    twoFormL2Hodge (smoothHarmonicResolventEquiv hRic u).val
  rw [smoothHarmonicResolventEquiv_val]
  exact (twoFormL2Hodge_smooth (u.val : SmoothL2TwoForm o)).symm

theorem twoFormHarmonicEigenspace_trace (hRic : RicciThree g) :
    LinearMap.trace ℝ (Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1)
      (twoFormEigenspaceHodge hRic 1) =
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) -
        (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℝ) := by
  have he : (smoothHarmonicResolventEquiv (o := o) hRic).conj (smoothHarmonicHodge hRic) =
      twoFormEigenspaceHodge hRic 1 := by
    apply LinearMap.ext
    intro f
    obtain ⟨u, rfl⟩ := (smoothHarmonicResolventEquiv hRic).surjective f
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    exact smoothHarmonicResolventEquiv_hodge hRic u
  rw [← he, LinearMap.trace_conj']
  exact smoothHarmonicHodge_trace hRic

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimensions entering the Euler and signature indices of the
actual scalar/one-form/two-form Hodge complex. Identification of these
indices with curvature integrals is a separate local index calculation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance hodgeIndexZeroAddGroup : AddCommGroup (ZeroFormDeRhamCohomology g) :=
  Submodule.addCommGroup _

local instance hodgeIndexClosedAddGroup : AddCommGroup (smoothClosedTwoForms (o := o)) :=
  Submodule.addCommGroup _

def hodgeComplexEuler (g : SmoothMetric M) (o : FrameOrientation g) : ℤ :=
  (Module.finrank ℝ (ZeroFormDeRhamCohomology g) : ℤ) -
    (Module.finrank ℝ (OneFormDeRhamCohomology (o := o)) : ℤ) +
    (Module.finrank ℝ (TwoFormDeRhamCohomology (o := o)) : ℤ) -
    (Module.finrank ℝ (HodgeDualOneCohomology (o := o)) : ℤ) +
    (Module.finrank ℝ (DivergenceCokernel g) : ℤ)

theorem hodgeComplexEuler_hodge (hRic : RicciThree g) :
    hodgeComplexEuler g o = 2 +
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℤ) +
      (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℤ) := by
  rw [hodgeComplexEuler, zeroFormDeRhamCohomology_finrank (o := o) hRic,
    oneFormDeRhamCohomology_finrank hRic, twoFormDeRhamCohomology_hodge_dimension hRic,
    hodgeDualOneCohomology_finrank hRic, divergenceCokernel_finrank o hRic]
  push_cast
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normalized exterior derivatives of the coexact one-form modes.
They give actual orthonormal two-form lifts, not arbitrary spectral preimages. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

def oneFormCoexactEigensection (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothCovariantFields M 1 :=
  smoothTwoFormCodifferentialField (oneFormCoexactEigenvector_smooth hRic i).choose

theorem oneFormCoexactEigensection_L2 (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothOneFormL2Linear (o := o) (oneFormCoexactEigensection hRic i) =
      oneFormCoexactEigenvector hRic i :=
  (oneFormCoexactEigenvector_smooth hRic i).choose_spec.1.symm

theorem oneFormCoexactEigensection_eigen (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothOneFormHodgeLaplacian (o := o) (oneFormCoexactEigensection hRic i) =
      (i.1.val⁻¹ - 1) • oneFormCoexactEigensection hRic i :=
  (oneFormCoexactEigenvector_smooth hRic i).choose_spec.2

theorem oneFormCoexactEigensection_divergence (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothOneFormDivergence g (oneFormCoexactEigensection hRic i) = 0 :=
  smoothTwoFormCodifferential_divergence hRic _

theorem oneFormCoexactEigensection_codiff_exterior
    (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothTwoFormCodifferentialField (smoothOneFormExterior (o := o) (oneFormCoexactEigensection hRic i)) =
      (i.1.val⁻¹ - 1) • oneFormCoexactEigensection hRic i := by
  have he := oneFormCoexactEigensection_eigen hRic i
  rw [smoothOneFormHodgeLaplacian_apply, oneFormCoexactEigensection_divergence hRic,
    show smoothScalarDifferential g 0 = 0 from (smoothScalarDifferentialLinear g).map_zero,
    sub_zero] at he
  exact he

theorem oneFormCoexact_exterior_inner (i j : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothTwoFormL2Inner
      (smoothOneFormExterior (o := o) (oneFormCoexactEigensection hRic i))
      (smoothOneFormExterior (o := o) (oneFormCoexactEigensection hRic j)) =
        (j.1.val⁻¹ - 1) * inner ℝ (oneFormCoexactEigenvector hRic i) (oneFormCoexactEigenvector hRic j) := by
  rw [smoothTwoFormL2Inner_comm, ← smoothTwoFormCodifferential_pairing hRic,
    oneFormCoexactEigensection_codiff_exterior hRic,
    smoothOneFormL2Pairing_smul]
  rw [← smoothOneFormL2Linear_inner, oneFormCoexactEigensection_L2,
    oneFormCoexactEigensection_L2, real_inner_comm]

def oneFormCoexactLift (i : OneFormCoexactEigenIndex (o := o) hRic) : smoothTwoForms o :=
  (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ •
    smoothOneFormExterior (o := o) (oneFormCoexactEigensection hRic i)

def oneFormCoexactLiftL2 (i : OneFormCoexactEigenIndex (o := o) hRic) : TwoFormL2 o :=
  smoothTwoFormToL2 (oneFormCoexactLift hRic i : SmoothL2TwoForm o)

theorem oneFormCoexactLift_orthonormal : Orthonormal ℝ (oneFormCoexactLiftL2 (o := o) hRic) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  change inner ℝ (smoothTwoFormToL2 _ ) (smoothTwoFormToL2 _) = _
  have hp := smoothTwoFormToL2_inner (oneFormCoexactLift hRic i : SmoothL2TwoForm o)
    (oneFormCoexactLift hRic j : SmoothL2TwoForm o)
  change _ = smoothTwoFormL2Inner (oneFormCoexactLift hRic i) (oneFormCoexactLift hRic j) at hp
  rw [hp]
  change smoothTwoFormL2Inner ((Real.sqrt (i.1.val⁻¹ - 1))⁻¹ • _)
    ((Real.sqrt (j.1.val⁻¹ - 1))⁻¹ • _) = _
  rw [smoothTwoFormL2Inner_smul, smoothTwoFormL2Inner_comm,
    smoothTwoFormL2Inner_smul, smoothTwoFormL2Inner_comm, oneFormCoexact_exterior_inner hRic]
  rw [orthonormal_iff_ite.mp (oneFormCoexactEigenvector_orthonormal hRic)]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hs := Real.sq_sqrt (oneFormCoexactEigenvector_rate_pos hRic i).le
    calc
      _ = ((Real.sqrt (i.1.val⁻¹ - 1)) ^ 2)⁻¹ * (i.1.val⁻¹ - 1) := by ring
      _ = 1 := by rw [hs, inv_mul_cancel₀ (oneFormCoexactEigenvector_rate_pos hRic i).ne']
  · simp only [hij, ite_false, mul_zero]

theorem oneFormCoexactLift_codifferential (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField (oneFormCoexactLift hRic i)) =
      Real.sqrt (i.1.val⁻¹ - 1) • oneFormCoexactEigenvector hRic i := by
  rw [oneFormCoexactLift, smoothTwoFormCodifferentialField_smul,
    oneFormCoexactEigensection_codiff_exterior hRic, map_smul, map_smul,
    oneFormCoexactEigensection_L2, smul_smul]
  congr 1
  have hs := Real.sq_sqrt (oneFormCoexactEigenvector_rate_pos hRic i).le
  have hn : Real.sqrt (i.1.val⁻¹ - 1) ≠ 0 :=
    (Real.sqrt_pos.mpr (oneFormCoexactEigenvector_rate_pos hRic i)).ne'
  calc
    _ = (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ * (Real.sqrt (i.1.val⁻¹ - 1)) ^ 2 := by rw [hs]
    _ = _ := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

theorem oneFormCoexactLift_eigen (i : OneFormCoexactEigenIndex (o := o) hRic) :
    smoothHodgeLaplacian hRic (oneFormCoexactLift hRic i) =
      (i.1.val⁻¹ - 1) • oneFormCoexactLift hRic i := by
  rw [oneFormCoexactLift, smoothHodgeLaplacian_smul, smoothHodgeLaplacian_exterior hRic,
    oneFormCoexactEigensection_eigen hRic]
  change _ • smoothOneFormExteriorLinear (_ • _) = _
  rw [map_smul]
  exact smul_comm _ _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Each nonzero two-form Hodge eigenspace consists of two copies of its
actual coexact one-form image. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_nonzero_coexact_multiplicity (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (hμ : μ.val ≠ 1) :
    Module.finrank ℝ (TwoFormSpectralSpace hRic μ) =
      2 * Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) := by
  have hκ : μ.val⁻¹ - 1 ≠ 0 := by
    simpa only [ne_eq, sub_eq_zero, inv_eq_one] using hμ
  have hS (u : TwoFormSmoothEigenSpace hRic μ) :
      twoFormSmoothEigenHodge hRic μ (twoFormSmoothEigenHodge hRic μ u) = u :=
    congrArg (fun T : Module.End ℝ (TwoFormSmoothEigenSpace hRic μ) => T u)
      (twoFormEigenHodge_square hRic μ)
  have hCA (u : TwoFormSmoothEigenSpace hRic μ) :
      oneFormCodiffEigenMap hRic μ (twoFormSmoothEigenDDelta hRic μ u) =
        (μ.val⁻¹ - 1) • oneFormCodiffEigenMap hRic μ u :=
    congrArg (fun T : TwoFormSmoothEigenSpace hRic μ →ₗ[ℝ] OneFormL2 o => T u)
      (twoFormEigenCodiff_DDelta hRic μ)
  have hCSA (u : TwoFormSmoothEigenSpace hRic μ) :
      oneFormCodiffEigenMap hRic μ
        (twoFormSmoothEigenHodge hRic μ (twoFormSmoothEigenDDelta hRic μ u)) = 0 :=
    congrArg (fun T : TwoFormSmoothEigenSpace hRic μ →ₗ[ℝ] OneFormL2 o => T u)
      (twoFormEigenCodiff_hodge_DDelta hRic μ)
  have hker (u : TwoFormSmoothEigenSpace hRic μ) (hu : oneFormCodiffEigenMap hRic μ u = 0) :
      twoFormSmoothEigenDDelta hRic μ u = 0 := by
    change smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u.val) = 0 at hu
    have hz : smoothTwoFormCodifferentialField u.val = 0 :=
      smoothOneFormL2Linear_injective (hu.trans (map_zero smoothOneFormL2Linear).symm)
    apply Subtype.ext
    change smoothOneFormExterior (o := o) (smoothTwoFormCodifferentialField u.val) = 0
    rw [hz]
    exact smoothOneFormExteriorLinear.map_zero
  have hs (u : TwoFormSmoothEigenSpace hRic μ) :
      twoFormSmoothEigenDDelta hRic μ u +
        twoFormSmoothEigenHodge hRic μ
          (twoFormSmoothEigenDDelta hRic μ (twoFormSmoothEigenHodge hRic μ u)) =
      (μ.val⁻¹ - 1) • u :=
    congrArg (fun T : Module.End ℝ (TwoFormSmoothEigenSpace hRic μ) => T u)
      (twoFormEigen_DDelta_hodge_split hRic μ)
  have hd := finite_hodge_multiplicity (V := TwoFormSmoothEigenSpace hRic μ)
    (W := OneFormL2 o) (oneFormCodiffEigenMap hRic μ)
    (twoFormSmoothEigenDDelta hRic μ) (twoFormSmoothEigenHodge hRic μ)
    (μ.val⁻¹ - 1) hκ hS hCA hCSA hker hs
  exact (twoFormSmoothEigenEquiv hRic μ).finrank_eq.symm.trans hd

theorem oneFormCoexact_harmonic_eq_bot (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (hμ : μ.val = 1) :
    OneFormCoexactSpectralSpace hRic μ = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  obtain ⟨u, hu, he⟩ := oneFormCoexactSpectral_representation hRic μ ⟨v, hv⟩
  have hδ := smoothCodiff_eigen hRic u (μ.val⁻¹ - 1) hu
  rw [hμ, inv_one, sub_self, zero_smul] at hδ
  have hz := smoothOneFormHodgeLaplacian_eq_zero (o := o) hRic _ hδ
  exact he.trans ((congrArg (smoothOneFormL2Linear (o := o)) hz).trans
    (map_zero smoothOneFormL2Linear))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Banach space obtained by uniformly completing genuine smooth one-forms.
Frame norms descend to the base, so its L2 realization remains injective. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance : IsProbabilityMeasure (canonicalFrameMeasure g o) := inferInstance
local instance : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def smoothOneFormContinuousLinear : smoothCovariantFields M 1 →ₗ[ℝ] C(FrameBundle g, FourSpace) where
  toFun := smoothOneFormEuclideanValue
  map_add' u v := by
    ext e i
    exact congrFun (covariantFieldFramed_add (g := g) u.val v.val e) ![i]
  map_smul' r u := by
    ext e i
    exact congrFun (covariantFieldFramed_smul (g := g) r u.val e) ![i]

def oneFormContinuousSubspace (g : SmoothMetric M) : Submodule ℝ C(FrameBundle g, FourSpace) :=
  (smoothOneFormContinuousLinear (g := g)).range.topologicalClosure

abbrev OneFormC0 (g : SmoothMetric M) := ↥(oneFormContinuousSubspace g)

instance oneFormC0_complete : CompleteSpace (OneFormC0 g) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothOneFormEuclideanValue_norm_base (u : smoothCovariantFields M 1) (e f : FrameBundle g)
    (hef : e.base = f.base) : ‖smoothOneFormEuclideanValue (g := g) u e‖ = ‖smoothOneFormEuclideanValue (g := g) u f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin 4, covariantFieldFramed g u.val e ![i] ^ 2) =
    ∑ i : Fin 4, covariantFieldFramed g u.val f ![i] ^ 2
  rw [← oneForm_squareNorm, ← oneForm_squareNorm,
    ← covariantFieldNormSq_eq_frame u.val e, ← covariantFieldNormSq_eq_frame u.val f, hef]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem oneFormC0_norm_base (u : OneFormC0 g) (e f : FrameBundle g) (hef : e.base = f.base) :
    ‖u.val e‖ = ‖u.val f‖ := by
  have hc : IsClosed {F : C(FrameBundle g, FourSpace) | ‖F e‖ = ‖F f‖} :=
    isClosed_eq ((continuous_eval_const e).norm) ((continuous_eval_const f).norm)
  apply hc.closure_subset_iff.mpr _ u.property
  rintro _ ⟨v, rfl⟩
  exact smoothOneFormEuclideanValue_norm_base v e f hef

def oneFormC0BaseNorm (u : OneFormC0 g) (x : M) : ℝ := ‖u.val (frameAt g x)‖

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem oneFormC0BaseNorm_frame (u : OneFormC0 g) (e : FrameBundle g) :
    oneFormC0BaseNorm u e.base = ‖u.val e‖ :=
  oneFormC0_norm_base u (frameAt g e.base) e rfl

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem oneFormC0BaseNorm_continuous (u : OneFormC0 g) : Continuous (oneFormC0BaseNorm u) := by
  have hq := Topology.IsQuotientMap.of_surjective_continuous
    (frameBase_surjective g) (continuous_frameBase g)
  apply hq.continuous_iff.mpr
  change Continuous (fun e : FrameBundle g => oneFormC0BaseNorm u e.base)
  simp_rw [oneFormC0BaseNorm_frame]
  exact u.val.continuous.norm

def oneFormC0ToFrameLp : OneFormC0 g →L[ℝ] Lp FourSpace 2 (canonicalFrameMeasure g o) :=
  (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ).comp (oneFormContinuousSubspace g).subtypeL

theorem oneFormC0ToFrameLp_norm_sq (u : OneFormC0 g) :
    ‖oneFormC0ToFrameLp (o := o) u‖ ^ 2 =
      ∫ x, oneFormC0BaseNorm u x ^ 2 ∂normalizedVolume g := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have he := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) u.val
  calc
    _ = ∫ e, ‖u.val e‖ ^ 2 ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [he] with e he
      change (oneFormC0ToFrameLp (o := o) u : FrameBundle g → FourSpace) e = _ at he
      rw [he, real_inner_self_eq_norm_sq]
    _ = ∫ e, oneFormC0BaseNorm u e.base ^ 2 ∂canonicalFrameMeasure g o := by
      simp only [oneFormC0BaseNorm_frame]
    _ = _ := canonicalFrameMeasure_integral_base g o _
      (((oneFormC0BaseNorm_continuous u).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

theorem oneFormC0ToFrameLp_injective : Function.Injective (oneFormC0ToFrameLp (g := g) (o := o)) := by
  suffices hz : ∀ u : OneFormC0 g, oneFormC0ToFrameLp (o := o) u = 0 → u = 0 by
    intro u v h
    exact sub_eq_zero.mp (hz (u - v) ((map_sub (oneFormC0ToFrameLp (o := o)) u v).trans (sub_eq_zero.mpr h)))
  intro u hu
  have hi : (∫ x, oneFormC0BaseNorm u x ^ 2 ∂normalizedVolume g) = 0 := by
    rw [← oneFormC0ToFrameLp_norm_sq (o := o), hu, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hc := (oneFormC0BaseNorm_continuous u).pow 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (oneFormC0BaseNorm u x))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hi
  let := normalizedVolume_isOpenPosMeasure g
  have he : (fun x => oneFormC0BaseNorm u x ^ 2) = fun _ => 0 :=
    Measure.eq_of_ae_eq hae hc continuous_const
  apply Subtype.ext
  apply ContinuousMap.ext
  intro e
  apply norm_eq_zero.mp
  have hb := congrFun he e.base
  rw [oneFormC0BaseNorm_frame] at hb
  exact (sq_eq_zero_iff).mp hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! A complete orthonormal one-form eigenfamily, obtained from the actual
scalar and two-form spectra and the proved geometric Hodge decomposition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

abbrev OneFormEigenIndex := OneFormExactEigenIndex g o d ⊕ OneFormCoexactEigenIndex (o := o) hRic

def oneFormEigenvector : OneFormEigenIndex hRic d → OneFormL2 o :=
  Sum.elim (oneFormExactEigenvector g o d) (oneFormCoexactEigenvector hRic)

omit [PreconnectedSpace M] in
theorem oneForm_exact_coexact_eigen_orthogonal
    (i : OneFormExactEigenIndex g o d) (j : OneFormCoexactEigenIndex (o := o) hRic) :
    inner ℝ (oneFormExactEigenvector g o d i) (oneFormCoexactEigenvector hRic j) = 0 := by
  obtain ⟨u, hu, _⟩ := oneFormCoexactEigenvector_smooth hRic j
  rw [hu]
  change inner ℝ ((Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ • _)
    (smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u)) = 0
  rw [real_inner_smul_left, oneForm_exact_coexact_orthogonal hRic, mul_zero]

omit [PreconnectedSpace M] in
theorem oneFormEigenvector_orthonormal : Orthonormal ℝ (oneFormEigenvector hRic d) := by
  constructor
  · intro i
    cases i with
    | inl i => exact (oneFormExactEigenvector_orthonormal g o d).1 i
    | inr i => exact (oneFormCoexactEigenvector_orthonormal hRic).1 i
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        exact (oneFormExactEigenvector_orthonormal g o d).2
          (fun h => hij (congrArg Sum.inl h))
      | inr j => exact oneForm_exact_coexact_eigen_orthogonal hRic d i j
    | inr i =>
      cases j with
      | inl j =>
        rw [real_inner_comm]
        exact oneForm_exact_coexact_eigen_orthogonal hRic d j i
      | inr j =>
        exact (oneFormCoexactEigenvector_orthonormal hRic).2
          (fun h => hij (congrArg Sum.inr h))

theorem oneFormEigenvector_total :
    (Submodule.span ℝ (range (oneFormEigenvector hRic d))).topologicalClosure = ⊤ := by
  let K := Submodule.span ℝ (range (oneFormEigenvector hRic d))
  have hco : Submodule.span ℝ (range (oneFormCoexactEigenvector (o := o) hRic)) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Sum.inr i, rfl⟩
  have hsub : Submodule.span ℝ (range (oneFormDerivedFamily hRic d)) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    cases i with
    | inl i =>
      change smoothOneFormL2Linear (o := o)
        (smoothScalarDifferential g (scalarBaseEigenfunction g o d i)) ∈ K
      by_cases hi : 0 < scalarBaseHeatRate g o d i
      · have hs : Real.sqrt (scalarBaseHeatRate g o d i) ≠ 0 := (Real.sqrt_pos.mpr hi).ne'
        have he : Real.sqrt (scalarBaseHeatRate g o d i) •
            oneFormExactEigenvector g o d ⟨i, hi⟩ =
            smoothOneFormL2Linear (o := o)
              (smoothScalarDifferential g (scalarBaseEigenfunction g o d i)) :=
          smul_inv_smul₀ hs _
        rw [← he]
        exact K.smul_mem _ (Submodule.subset_span ⟨Sum.inl ⟨i, hi⟩, rfl⟩)
      · have hz : scalarBaseHeatRate g o d i = 0 :=
          le_antisymm (le_of_not_gt hi) (scalarBaseHeatRate_nonneg g o d i)
        rw [scalarEigen_differential_zero g o d i hz]
        exact K.zero_mem
    | inr i =>
      let u : TwoFormSmoothEigenSpace hRic i.1 := ⟨twoFormEigenform hRic i,
        Module.End.mem_eigenspace_iff.mpr (twoFormEigenform_laplacian hRic i)⟩
      have hu : smoothOneFormL2Linear (o := o)
          (smoothTwoFormCodifferentialField (twoFormEigenform hRic i)) ∈
          OneFormCoexactSpectralSpace hRic i.1 := ⟨u, rfl⟩
      exact hco (oneFormCoexact_mem_span hRic i.1 ⟨_, hu⟩)
  apply top_unique
  rw [← oneFormDerivedFamily_total hRic d]
  exact Submodule.topologicalClosure_mono hsub

def oneFormEigenbasis : HilbertBasis (OneFormEigenIndex hRic d) ℝ (OneFormL2 o) :=
  HilbertBasis.mk (oneFormEigenvector_orthonormal hRic d) (oneFormEigenvector_total hRic d).ge

end
end PositiveEinsteinFour.Geometry
end


section

/-! The convergent kernel is the spectral kernel formed from the actual
normalized smooth eigenforms, with the original heat weights. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatSection_eigen (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormHeatSection hRic t ht (twoFormEigenvector hRic i) =
      twoFormHeatWeight hRic t i.1 • twoFormEigenSection hRic i := by
  have he : smoothTwoFormToL2
        (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i) : SmoothL2TwoForm o) =
      smoothTwoFormToL2
        (twoFormHeatWeight hRic t i.1 • twoFormEigenSection hRic i : SmoothL2TwoForm o) := by
    calc
      _ = twoFormHeat hRic t (twoFormEigenvector hRic i) := twoFormHeatSection_L2 hRic t ht _
      _ = twoFormHeatWeight hRic t i.1 • twoFormEigenvector hRic i := twoFormHeat_eigenvector hRic t i
      _ = _ := ((smoothTwoFormToL2.map_smul (twoFormHeatWeight hRic t i.1)
        (twoFormEigenSection hRic i : SmoothL2TwoForm o)).trans
          (congrArg (twoFormHeatWeight hRic t i.1 • ·) (twoFormEigenSection_L2 hRic i))).symm
  exact smoothTwoFormToL2_injective he

theorem twoFormHeatKernelTerm_eigen (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x y : M) (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormHeatKernelTerm hRic t ht x y i = twoFormHeatWeight hRic t i.1 •
      InnerProductSpace.rankOne ℝ ((twoFormEigenSection hRic i).val x)
        ((twoFormEigenSection hRic i).val y) := by
  have hx := congrArg (fun w : smoothTwoForms o => w.val x)
    (twoFormHeatSection_eigen hRic (t / 2) (half_pos ht) i)
  have hy := congrArg (fun w : smoothTwoForms o => w.val y)
    (twoFormHeatSection_eigen hRic (t / 2) (half_pos ht) i)
  change _ = twoFormHeatWeight hRic (t / 2) i.1 • (twoFormEigenSection hRic i).val x at hx
  change _ = twoFormHeatWeight hRic (t / 2) i.1 • (twoFormEigenSection hRic i).val y at hy
  rw [twoFormHeatKernelTerm, hx, hy]
  apply ContinuousLinearMap.ext
  intro v
  simp only [InnerProductSpace.rankOne_apply, smul_apply,
    real_inner_smul_left, smul_smul]
  congr 1
  rw [mul_right_comm, ← pow_two, twoFormHeatWeight_half_sq]

theorem twoFormHeatKernel_eigen_hasSum (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (x y : M) :
    HasSum (fun i : TwoFormEigenIndex (o := o) hRic => twoFormHeatWeight hRic t i.1 •
      InnerProductSpace.rankOne ℝ ((twoFormEigenSection hRic i).val x)
        ((twoFormEigenSection hRic i).val y)) (twoFormHeatKernel (o := o) hRic t ht x y) := by
  have he : (fun i : TwoFormEigenIndex (o := o) hRic => twoFormHeatWeight hRic t i.1 •
      InnerProductSpace.rankOne ℝ ((twoFormEigenSection hRic i).val x)
        ((twoFormEigenSection hRic i).val y)) = twoFormHeatKernelTerm hRic t ht x y :=
    funext (fun i => (twoFormHeatKernelTerm_eigen hRic t ht x y i).symm)
  rw [he]
  exact twoFormHeatKernel_hasSum (o := o) hRic t ht x y

end
end PositiveEinsteinFour.Geometry
end


section

/-! Gaussian composition estimates for the actual six-dimensional
two-form endomorphisms used in local heat kernels. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory

noncomputable section

local notation "V" => TwoFormFour →L[ℝ] TwoFormFour

theorem fourHeatTwoForm_composition_bound (t s A B : ℝ) (ht : 0 < t) (hA : 0 ≤ A)
    (x : FourSpace) (F G : FourSpace → V)
    (hF : ∀ z, ‖F z‖ ≤ A * fourHeatGaussian t (x - z))
    (hG : ∀ z, ‖G z‖ ≤ B * fourHeatGaussian s z) (z : FourSpace) :
    ‖(F z).comp (G z)‖ ≤ (A * B) *
      (fourHeatGaussian t (x - z) * fourHeatGaussian s z) := by
  calc
    _ ≤ ‖F z‖ * ‖G z‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (A * fourHeatGaussian t (x - z)) * (B * fourHeatGaussian s z) :=
      mul_le_mul (hF z) (hG z) (norm_nonneg _)
        (mul_nonneg hA (fourHeatGaussian_pos t ht _).le)
    _ = _ := by ring

theorem fourHeatTwoForm_composition_integrable (t s A B : ℝ)
    (ht : 0 < t) (hs : 0 < s) (hA : 0 ≤ A)
    (x : FourSpace) (F G : FourSpace → V) (hFc : Continuous F) (hGc : Continuous G)
    (hF : ∀ z, ‖F z‖ ≤ A * fourHeatGaussian t (x - z))
    (hG : ∀ z, ‖G z‖ ≤ B * fourHeatGaussian s z) :
    Integrable (fun z => (F z).comp (G z)) := by
  have hm := (fourHeatGaussian_product_integrable t s ht hs x).const_mul (A * B)
  exact hm.mono' (hFc.clm_comp hGc).aestronglyMeasurable
    (Filter.Eventually.of_forall (fourHeatTwoForm_composition_bound t s A B ht hA x F G hF hG))

theorem fourHeatTwoForm_composition_integral_bound (t s A B : ℝ)
    (ht : 0 < t) (hs : 0 < s) (hA : 0 ≤ A)
    (x : FourSpace) (F G : FourSpace → V)
    (hF : ∀ z, ‖F z‖ ≤ A * fourHeatGaussian t (x - z))
    (hG : ∀ z, ‖G z‖ ≤ B * fourHeatGaussian s z) :
    ‖∫ z : FourSpace, (F z).comp (G z)‖ ≤ (A * B) * fourHeatGaussian (t + s) x := by
  have := FiniteDimensional.complete ℝ V
  calc
    _ ≤ ∫ z : FourSpace, (A * B) *
        (fourHeatGaussian t (x - z) * fourHeatGaussian s z) :=
      norm_integral_le_of_norm_le
        ((fourHeatGaussian_product_integrable t s ht hs x).const_mul (A * B))
        (Filter.Eventually.of_forall (fourHeatTwoForm_composition_bound t s A B ht hA x F G hF hG))
    _ = _ := by rw [integral_const_mul, fourHeatGaussian_convolution t s ht hs x]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual four-dimensional differential complex, with the upper
degrees written in metric Hodge-dual coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def hodgeComplexD2 : smoothTwoForms o →ₗ[ℝ] smoothCovariantFields M 1 :=
  (smoothTwoFormCodifferentialLinear (o := o)).comp (smoothTwoFormHodge o)

theorem hodgeComplexD2_kernel :
    (hodgeComplexD2 (o := o)).ker = smoothClosedTwoForms (o := o) := by
  ext u
  exact (smoothTwoForm_closed_iff_codifferential_hodge u).symm

theorem hodgeComplexD2_range :
    LinearMap.range (hodgeComplexD2 (o := o)) =
      LinearMap.range (smoothTwoFormCodifferentialLinear (o := o)) := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨smoothTwoFormHodge o u, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨smoothTwoFormHodge o u, ?_⟩
    change smoothTwoFormCodifferentialField (smoothTwoFormHodge o (smoothTwoFormHodge o u)) = _
    rw [smoothTwoFormHodge_involutive]
    rfl

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem hodgeComplex_D1_D0 :
    (smoothOneFormExteriorLinear (o := o)).comp (smoothScalarDifferentialLinear g) = 0 := by
  ext f : 1
  exact smoothScalarDifferential_closed f

theorem hodgeComplex_D2_D1 (hRic : RicciThree g) :
    (hodgeComplexD2 (o := o)).comp smoothOneFormExteriorLinear = 0 := by
  ext u : 1
  exact (smoothTwoForm_closed_iff_codifferential_hodge _).mp
    (smoothOneFormExterior_closed hRic u)

theorem hodgeComplex_D3_D2 (hRic : RicciThree g) :
    (smoothOneFormDivergence g).comp (hodgeComplexD2 (o := o)) = 0 := by
  ext u : 1
  exact smoothTwoFormCodifferential_divergence hRic (smoothTwoFormHodge o u)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The adjoint of the actual isometric frame realization reconstructs one-form
L2 sections from continuous frame data. -/

namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}
local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem oneFormFrameL2_inner (u v : OneFormL2 o) :
    inner ℝ (oneFormFrameL2 u) (oneFormFrameL2 v) = inner ℝ u v := by
  have h := norm_add_sq_real (oneFormFrameL2 u) (oneFormFrameL2 v)
  rw [← map_add, oneFormFrameL2_norm, oneFormFrameL2_norm, oneFormFrameL2_norm] at h
  nlinarith [norm_add_sq_real u v]

def oneFormFromFrameL2 : Lp FourSpace 2 (canonicalFrameMeasure g o) →L[ℝ] OneFormL2 o :=
  (oneFormFrameL2 (o := o)).adjoint

theorem oneFormFromFrameL2_pairing (F : Lp FourSpace 2 (canonicalFrameMeasure g o))
    (u : OneFormL2 o) :
    inner ℝ (oneFormFromFrameL2 F) u = inner ℝ F (oneFormFrameL2 u) :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

theorem oneFormFromFrameL2_left_inverse (u : OneFormL2 o) :
    oneFormFromFrameL2 (oneFormFrameL2 u) = u := by
  apply ext_inner_right ℝ
  intro v
  rw [oneFormFromFrameL2_pairing, oneFormFrameL2_inner]

def oneFormFromContinuous : C(FrameBundle g, FourSpace) →L[ℝ] OneFormL2 o :=
  (oneFormFromFrameL2 (o := o)).comp (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ)

theorem oneFormFromContinuous_pairing (F : C(FrameBundle g, FourSpace))
    (u : smoothCovariantFields M 1) :
    inner ℝ (oneFormFromContinuous (o := o) F) (smoothOneFormL2Linear u) =
      ∫ e, inner ℝ (F e) (smoothOneFormEuclideanValue (g := g) u e)
        ∂canonicalFrameMeasure g o := by
  change inner ℝ (oneFormFromFrameL2 (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F))
    (smoothOneFormL2Linear u) = _
  rw [oneFormFromFrameL2_pairing, oneFormFrameL2_smooth, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
      (smoothOneFormEuclideanValue (g := g) u)] with e hF hu
  rw [hF, hu]

theorem oneFormFromContinuous_smooth (u : smoothCovariantFields M 1) :
    oneFormFromContinuous (smoothOneFormEuclideanValue (g := g) u) =
      smoothOneFormL2Linear (o := o) u := by
  change oneFormFromFrameL2 (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ _) = _
  rw [← oneFormFrameL2_smooth, oneFormFromFrameL2_left_inverse]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every vector in the completed one-form basis is an actual smooth
geometric eigenform, with a strictly positive Laplace eigenvalue. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormHeatRate : OneFormEigenIndex hRic d → ℝ
  | .inl i => scalarBaseHeatRate g o d i.val
  | .inr i => i.1.val⁻¹ - 1

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormHeatRate_pos (i : OneFormEigenIndex hRic d) : 0 < oneFormHeatRate hRic d i := by
  cases i with
  | inl i => exact i.property
  | inr i => exact oneFormCoexactEigenvector_rate_pos hRic i

omit [PreconnectedSpace M] in
theorem oneFormEigenvector_smooth (i : OneFormEigenIndex hRic d) :
    ∃ u : smoothCovariantFields M 1,
      oneFormEigenvector hRic d i = smoothOneFormL2Linear (o := o) u ∧
      smoothOneFormHodgeLaplacian (o := o) u = oneFormHeatRate hRic d i • u := by
  cases i with
  | inl i =>
    let c := (Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹
    let u := smoothScalarDifferential g (scalarBaseEigenfunction g o d i.val)
    refine ⟨c • u, (smoothOneFormL2Linear.map_smul c u).symm, ?_⟩
    change smoothOneFormHodgeLaplacian (o := o) (c • u) = scalarBaseHeatRate g o d i.val • (c • u)
    rw [map_smul, scalarEigen_differential_is_oneFormEigen]
    exact smul_comm _ _ _
  | inr i =>
    obtain ⟨u, hu, hL⟩ := oneFormCoexactEigenvector_smooth hRic i
    exact ⟨smoothTwoFormCodifferentialField u, hu, hL⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded spectral lifts from actual one-forms to their scalar and
closed two-form potentials. The lifts preserve the spectral parameter. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff lp

noncomputable section

private def modeSynthesis {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (v : ι → H) (hv : Orthonormal ℝ v) : ℓ²(ι, ℝ) →ₗᵢ[ℝ] H :=
  hv.orthogonalFamily.linearIsometry

private theorem modeSynthesis_single {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (v : ι → H) (hv : Orthonormal ℝ v) (i : ι) :
    modeSynthesis v hv (lp.single 2 i (1 : ℝ)) = v i := by
  classical
  change hv.orthogonalFamily.linearIsometry (lp.single 2 i (1 : ℝ)) = _
  rw [OrthogonalFamily.linearIsometry_apply_single, LinearIsometry.toSpanSingleton_apply, one_smul]

private theorem modeAnalysis_coordinate {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (v : ι → H) (hv : Orthonormal ℝ v) (u : H) (i : ι) :
    ((modeSynthesis v hv).toContinuousLinearMap.adjoint u) i = inner ℝ (v i) u := by
  classical
  calc
    _ = inner ℝ (lp.single 2 i (1 : ℝ)) ((modeSynthesis v hv).toContinuousLinearMap.adjoint u) := by
      simp only [lp.inner_single_left, Real.inner_apply, one_mul]
    _ = inner ℝ (modeSynthesis v hv (lp.single 2 i (1 : ℝ))) u :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = _ := by rw [modeSynthesis_single]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

def oneFormCoexactSynthesis : ℓ²(OneFormCoexactEigenIndex (o := o) hRic, ℝ) →ₗᵢ[ℝ] OneFormL2 o :=
  modeSynthesis _ (oneFormCoexactEigenvector_orthonormal hRic)

def oneFormLiftSynthesis : ℓ²(OneFormCoexactEigenIndex (o := o) hRic, ℝ) →ₗᵢ[ℝ] TwoFormL2 o :=
  modeSynthesis _ (oneFormCoexactLift_orthonormal hRic)

def oneFormCoexactSpectralLift : OneFormL2 o →L[ℝ] TwoFormL2 o :=
  (oneFormLiftSynthesis hRic).toContinuousLinearMap.comp
    (oneFormCoexactSynthesis hRic).toContinuousLinearMap.adjoint

theorem oneFormCoexactSpectralLift_eigen (i : OneFormCoexactEigenIndex (o := o) hRic) :
    oneFormCoexactSpectralLift hRic (oneFormCoexactEigenvector hRic i) = oneFormCoexactLiftL2 hRic i := by
  classical
  have hi := modeSynthesis_single _ (oneFormCoexactEigenvector_orthonormal hRic) i
  change oneFormCoexactSynthesis hRic (lp.single 2 i (1 : ℝ)) = _ at hi
  change oneFormLiftSynthesis hRic
    ((oneFormCoexactSynthesis hRic).toContinuousLinearMap.adjoint _) = _
  rw [← hi]
  have ha := congrArg (fun A : ℓ²(OneFormCoexactEigenIndex (o := o) hRic, ℝ) →L[ℝ]
      ℓ²(OneFormCoexactEigenIndex (o := o) hRic, ℝ) => A (lp.single 2 i (1 : ℝ)))
    (oneFormCoexactSynthesis hRic).adjoint_comp_self
  change (oneFormCoexactSynthesis hRic).toContinuousLinearMap.adjoint
    (oneFormCoexactSynthesis hRic (lp.single 2 i (1 : ℝ))) = lp.single 2 i (1 : ℝ) at ha
  rw [ha]
  exact modeSynthesis_single _ (oneFormCoexactLift_orthonormal hRic) i

variable [SecondCountableTopology M]
variable (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormCoexactSpectralLift_exact (i : OneFormExactEigenIndex g o d) :
    oneFormCoexactSpectralLift hRic (oneFormExactEigenvector g o d i) = 0 := by
  have hz : (oneFormCoexactSynthesis (o := o) hRic).toContinuousLinearMap.adjoint
      (oneFormExactEigenvector g o d i) = 0 := by
    apply lp.ext
    funext j
    rw [show (oneFormCoexactSynthesis (o := o) hRic).toContinuousLinearMap.adjoint =
      (modeSynthesis _ (oneFormCoexactEigenvector_orthonormal hRic)).toContinuousLinearMap.adjoint from rfl,
      modeAnalysis_coordinate]
    change _ = 0
    obtain ⟨u, hu, _⟩ := oneFormCoexactEigenvector_smooth (o := o) hRic j
    rw [hu, oneFormExactEigenvector, real_inner_smul_right, real_inner_comm]
    rw [oneForm_exact_coexact_orthogonal hRic, mul_zero]
  change oneFormLiftSynthesis hRic _ = _
  exact (congrArg (oneFormLiftSynthesis hRic) hz).trans (map_zero _)

def oneFormExactSynthesis : ℓ²(OneFormExactEigenIndex g o d, ℝ) →ₗᵢ[ℝ] OneFormL2 o :=
  modeSynthesis _ (oneFormExactEigenvector_orthonormal g o d)

def scalarPositiveSynthesis : ℓ²(OneFormExactEigenIndex g o d, ℝ) →ₗᵢ[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  modeSynthesis (fun i => scalarBaseEigenvector g o d i.val)
    ((scalarBaseEigenvector_orthonormal g o d).comp (fun i : OneFormExactEigenIndex g o d => i.val) Subtype.val_injective)

def oneFormExactSpectralLift : OneFormL2 o →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (scalarPositiveSynthesis d).toContinuousLinearMap.comp
    (oneFormExactSynthesis d).toContinuousLinearMap.adjoint

theorem oneFormExactSpectralLift_eigen (i : OneFormExactEigenIndex g o d) :
    oneFormExactSpectralLift d (oneFormExactEigenvector g o d i) = scalarBaseEigenvector g o d i.val := by
  classical
  have hi := modeSynthesis_single _ (oneFormExactEigenvector_orthonormal g o d) i
  change oneFormExactSynthesis d (lp.single 2 i (1 : ℝ)) = _ at hi
  change scalarPositiveSynthesis d
    ((oneFormExactSynthesis d).toContinuousLinearMap.adjoint _) = _
  rw [← hi]
  have ha := congrArg (fun A : ℓ²(OneFormExactEigenIndex g o d, ℝ) →L[ℝ]
      ℓ²(OneFormExactEigenIndex g o d, ℝ) => A (lp.single 2 i (1 : ℝ)))
    (oneFormExactSynthesis d).adjoint_comp_self
  change (oneFormExactSynthesis d).toContinuousLinearMap.adjoint
    (oneFormExactSynthesis d (lp.single 2 i (1 : ℝ))) = lp.single 2 i (1 : ℝ) at ha
  rw [ha]
  exact modeSynthesis_single _ ((scalarBaseEigenvector_orthonormal g o d).comp (fun i : OneFormExactEigenIndex g o d => i.val) Subtype.val_injective) i

theorem oneFormExactSpectralLift_coexact (i : OneFormCoexactEigenIndex (o := o) hRic) :
    oneFormExactSpectralLift d (oneFormCoexactEigenvector hRic i) = 0 := by
  have hz : (oneFormExactSynthesis d).toContinuousLinearMap.adjoint (oneFormCoexactEigenvector hRic i) = 0 := by
    apply lp.ext
    funext j
    rw [show (oneFormExactSynthesis d).toContinuousLinearMap.adjoint =
      (modeSynthesis _ (oneFormExactEigenvector_orthonormal g o d)).toContinuousLinearMap.adjoint from rfl,
      modeAnalysis_coordinate]
    change _ = 0
    obtain ⟨u, hu, _⟩ := oneFormCoexactEigenvector_smooth (o := o) hRic i
    rw [hu, oneFormExactEigenvector, real_inner_smul_left,
      oneForm_exact_coexact_orthogonal hRic, mul_zero]
  change scalarPositiveSynthesis d _ = _
  exact (congrArg (scalarPositiveSynthesis d) hz).trans (map_zero _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded spectral multipliers on the actual one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormSpectralEquiv := (oneFormEigenbasis hRic d).repr


def oneFormSpectralMultiplier
    (a : OneFormEigenIndex hRic d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) : OneFormL2 o →L[ℝ] OneFormL2 o :=
  (oneFormSpectralEquiv hRic d).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lp.mapCLM 2
      (fun μ => a μ • ContinuousLinearMap.id ℝ (ℝ))
      hC (fun μ => by
        calc
          ‖a μ • ContinuousLinearMap.id ℝ (ℝ)‖ ≤ |a μ| := by
            apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
            intro v
            change ‖a μ • v‖ ≤ |a μ| * ‖v‖
            rw [norm_smul, Real.norm_eq_abs]
          _ ≤ C := ha μ)).comp
      (oneFormSpectralEquiv hRic d).toContinuousLinearEquiv.toContinuousLinearMap)

theorem oneFormSpectralMultiplier_coordinate
    (a : OneFormEigenIndex hRic d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f : OneFormL2 o) (μ : OneFormEigenIndex hRic d) :
    (oneFormSpectralEquiv hRic d (oneFormSpectralMultiplier hRic d a C hC ha f)) μ =
      a μ • (oneFormSpectralEquiv hRic d f) μ := by
  change ((oneFormSpectralEquiv hRic d)
    ((oneFormSpectralEquiv hRic d).symm _)) μ = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem oneFormSpectralMultiplier_norm
    (a : OneFormEigenIndex hRic d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f : OneFormL2 o) :
    ‖oneFormSpectralMultiplier hRic d a C hC ha f‖ ≤ C * ‖f‖ := by
  rw [← (oneFormSpectralEquiv hRic d).norm_map (oneFormSpectralMultiplier hRic d a C hC ha f),
    ← (oneFormSpectralEquiv hRic d).norm_map f]
  calc
    _ ≤ ‖C • oneFormSpectralEquiv hRic d f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro μ
      rw [oneFormSpectralMultiplier_coordinate, norm_smul, Real.norm_eq_abs]
      change |a μ| * ‖(oneFormSpectralEquiv hRic d f) μ‖ ≤
        ‖C • (oneFormSpectralEquiv hRic d f) μ‖
      change |a μ| * |(oneFormSpectralEquiv hRic d f) μ| ≤
        |C * (oneFormSpectralEquiv hRic d f) μ|
      rw [abs_mul, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha μ) (abs_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

theorem oneFormSpectralMultiplier_inner
    (a : OneFormEigenIndex hRic d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f h : OneFormL2 o) :
    inner ℝ (oneFormSpectralMultiplier hRic d a C hC ha f) h =
      ∑' μ, a μ * inner ℝ ((oneFormSpectralEquiv hRic d f) μ)
        ((oneFormSpectralEquiv hRic d h) μ) := by
  rw [← (oneFormSpectralEquiv hRic d).inner_map_map, lp.inner_eq_tsum]
  apply tsum_congr
  intro μ
  rw [oneFormSpectralMultiplier_coordinate, real_inner_smul_left]

theorem oneFormSpectralMultiplier_selfAdjoint
    (a : OneFormEigenIndex hRic d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f h : OneFormL2 o) :
    inner ℝ (oneFormSpectralMultiplier hRic d a C hC ha f) h =
      inner ℝ f (oneFormSpectralMultiplier hRic d a C hC ha h) := by
  calc
    _ = ∑' μ, a μ * inner ℝ ((oneFormSpectralEquiv hRic d f) μ)
        ((oneFormSpectralEquiv hRic d h) μ) := oneFormSpectralMultiplier_inner hRic d a C hC ha f h
    _ = ∑' μ, a μ * inner ℝ ((oneFormSpectralEquiv hRic d h) μ)
        ((oneFormSpectralEquiv hRic d f) μ) := by
      apply tsum_congr
      intro μ
      rw [real_inner_comm]
    _ = inner ℝ (oneFormSpectralMultiplier hRic d a C hC ha h) f :=
      (oneFormSpectralMultiplier_inner hRic d a C hC ha h f).symm
    _ = _ := real_inner_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact H1 realizations of smooth two-form heat outputs and coexact lifts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

theorem twoFormHeatLift_smooth (t : ℝ≥0) (ht : 0 < t) (f : TwoFormL2 o)
    (u : smoothTwoForms o) (hu : twoFormHeat hRic t f = smoothTwoFormToL2 (u : SmoothL2TwoForm o)) :
    twoFormHeatLift hRic t ht f = smoothTwoFormToH1 (u : SmoothH1TwoForm o) := by
  apply twoFormH1ToL2_injective hRic
  rw [twoFormHeatLift_value]
  exact hu.trans (twoFormH1ToL2_smooth (u : SmoothH1TwoForm o)).symm

theorem twoFormHeat_coexactLift (t : ℝ≥0) (i : OneFormCoexactEigenIndex (o := o) hRic) :
    twoFormHeat hRic t (oneFormCoexactLiftL2 hRic i) =
      twoFormHeatWeight hRic t i.1 • oneFormCoexactLiftL2 hRic i := by
  apply twoFormHeat_eigenvalue hRic t i.1
  apply Module.End.mem_eigenspace_iff.mpr
  apply smoothTwoForm_resolvent_eigen hRic i.1.val (i.1.val⁻¹ - 1) _ (oneFormCoexactLift hRic i)
    (oneFormCoexactLift_eigen hRic i)
  have hn := (twoFormSpectralValue_bounds hRic i.1).1.ne'
  simp only [sub_add_cancel, mul_inv_cancel₀ hn]

theorem twoFormHeatLift_coexactLift (t : ℝ≥0) (ht : 0 < t)
    (i : OneFormCoexactEigenIndex (o := o) hRic) :
    twoFormHeatLift hRic t ht (oneFormCoexactLiftL2 hRic i) =
      twoFormHeatWeight hRic t i.1 • smoothTwoFormToH1 (oneFormCoexactLift hRic i : SmoothH1TwoForm o) := by
  apply twoFormH1ToL2_injective hRic
  rw [twoFormHeatLift_value, map_smul]
  exact (twoFormHeat_coexactLift hRic t i).trans
    (congrArg (twoFormHeatWeight hRic t i.1 • ·)
      (twoFormH1ToL2_smooth (oneFormCoexactLift hRic i : SmoothH1TwoForm o)).symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar spectral pairing of the actual heat operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigenbasis_apply (hRic : RicciThree g)
    (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormEigenbasis hRic i = twoFormEigenvector hRic i := by
  simp only [twoFormEigenbasis, HilbertBasis.coe_mk]

theorem twoFormHeat_pairing_hasSum (hRic : RicciThree g) (t : ℝ≥0)
    (f h : TwoFormL2 o) :
    HasSum (fun i : TwoFormEigenIndex (o := o) hRic =>
      twoFormHeatWeight hRic t i.1 * inner ℝ f (twoFormEigenvector hRic i) *
        inner ℝ (twoFormEigenvector hRic i) h)
      (inner ℝ (twoFormHeat hRic t f) h) := by
  have hs := (twoFormEigenbasis hRic).hasSum_inner_mul_inner (twoFormHeat hRic t f) h
  have he : (fun i : TwoFormEigenIndex (o := o) hRic =>
      inner ℝ (twoFormHeat hRic t f) (twoFormEigenbasis hRic i) *
        inner ℝ (twoFormEigenbasis hRic i) h) =
      (fun i => twoFormHeatWeight hRic t i.1 * inner ℝ f (twoFormEigenvector hRic i) *
        inner ℝ (twoFormEigenvector hRic i) h) := by
    funext i
    rw [twoFormEigenbasis_apply, twoFormHeat_selfAdjoint, twoFormHeat_eigenvector,
      real_inner_smul_right]
  rwa [he] at hs

theorem twoFormHeat_pairing_tsum (hRic : RicciThree g) (t : ℝ≥0)
    (f h : TwoFormL2 o) :
    inner ℝ (twoFormHeat hRic t f) h =
      ∑' i : TwoFormEigenIndex (o := o) hRic,
        twoFormHeatWeight hRic t i.1 * inner ℝ f (twoFormEigenvector hRic i) *
          inner ℝ (twoFormEigenvector hRic i) h :=
  (twoFormHeat_pairing_hasSum hRic t f h).tsum_eq.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A third-order Gaussian remainder has vanishing diagonal in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology

noncomputable section

local notation "V" => TwoFormFour →L[ℝ] TwoFormFour

theorem fourHeatGaussian_diagonal_power (m : ℕ) (t : ℝ) (ht : 0 < t) :
    t ^ (m + 2) * fourHeatGaussian t 0 = t ^ m / (16 * Real.pi ^ 2) := by
  simp only [fourHeatGaussian, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, Real.exp_zero, mul_one, pow_add]
  field_simp [Real.pi_ne_zero]
  ring

theorem fourHeat_diagonal_remainder_tendsto (m : ℕ) (E : ℝ → V) (C T : ℝ)
    (hT : 0 < T) (hE : ∀ t ∈ Ioo 0 T,
      ‖E t‖ ≤ C * t ^ (m + 3) * fourHeatGaussian t 0) :
    Tendsto E (𝓝[>] 0) (𝓝 0) := by
  have hlim : Tendsto (fun t : ℝ => C * (t ^ (m + 1) / (16 * Real.pi ^ 2)))
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => C * (t ^ (m + 1) / (16 * Real.pi ^ 2))) := by
      fun_prop
    simpa only [pow_succ, zero_mul, zero_div, mul_zero] using
      hc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply squeeze_zero_norm' _ hlim
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < T :=
    (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with t ht htT
  calc
    ‖E t‖ ≤ C * t ^ (m + 3) * fourHeatGaussian t 0 := hE t ⟨ht, htT⟩
    _ = C * (t ^ (m + 1) / (16 * Real.pi ^ 2)) := by
      rw [mul_assoc, show m + 3 = (m + 1) + 2 by omega,
        fourHeatGaussian_diagonal_power (m + 1) t ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Time integration of the polynomial bounds in the local heat correction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set

noncomputable section

local notation "V" => TwoFormFour →L[ℝ] TwoFormFour

theorem fourHeatTimePolynomial_bound (F : ℝ → V) (t : ℝ) (ht : 0 < t)
    (n : ℕ) (C : ℝ) (hF : ∀ s ∈ Ioo 0 t, ‖F s‖ ≤ C * s ^ n) :
    ‖∫ s : ℝ in 0..t, F s‖ ≤ C * t ^ (n + 1) / (n + 1) := by
  have := FiniteDimensional.complete ℝ V
  have hb : ∀ᵐ s : ℝ, s ∈ Ioc 0 t → ‖F s‖ ≤ C * s ^ n := by
    filter_upwards [Measure.ae_ne volume t] with s hs hst
    exact hF s ⟨hst.1, lt_of_le_of_ne hst.2 hs⟩
  have hi : IntervalIntegrable (fun s : ℝ => C * s ^ n) volume 0 t :=
    (continuous_const.mul (continuous_id.pow n)).intervalIntegrable _ _
  calc
    _ ≤ ∫ s : ℝ in 0..t, C * s ^ n :=
      intervalIntegral.norm_integral_le_of_norm_le ht.le hb hi
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_pow]
      simp only [pow_succ]
      ring

theorem fourHeatTimePolynomial_integrable (F : ℝ → V) (t : ℝ) (ht : 0 < t)
    (n : ℕ) (C : ℝ)
    (hm : AEStronglyMeasurable F (volume.restrict (Ioo 0 t)))
    (hF : ∀ s ∈ Ioo 0 t, ‖F s‖ ≤ C * s ^ n) :
    IntervalIntegrable F volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
  change Integrable F (volume.restrict (Ioc 0 t))
  rw [← restrict_Ioo_eq_restrict_Ioc]
  have hi : IntegrableOn (fun s : ℝ => C * s ^ n) (Ioo 0 t) :=
    ((continuous_const.mul (continuous_id.pow n)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  exact hi.mono' hm ((ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall hF))

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact finite-regularity normal-frame amplitude determines an
actual element of the global one-form L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem heatNormalOneCoordinates_continuousOn (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hP : ContDiffOn ℝ 2 D.point C.source)
    (hD : C.source ⊆ ball 0 D.radius) (a : FourSpace → FourSpace)
    (ha : ContDiff ℝ 2 a) : ContinuousOn (heatNormalOneCoordinates D a) C.source := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_pi.mpr
  intro v
  exact (heatNormalOneCoordinates_regular D a x (hD hx)
    (hP.contDiffAt (C.open_source.mem_nhds hx)) ha.contDiffAt v).continuousAt

def heatNormalOneAmplitude (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : C(FrameBundle g, FourSpace) :=
  ⟨fun f => WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i]),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (continuous_apply ![i]).comp
      (heatNormalOneFrameLift_continuous g c C _ hCt
        (heatNormalOneCoordinates_continuousOn D C hP hD a ha)
        (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneCoordinates_support D a))
        ((heatNormalOneCoordinates_support D a).trans hs))))⟩

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalOneAmplitudeL2 (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : OneFormL2 o :=
  oneFormFromContinuous (heatNormalOneAmplitude D C hCt hP hD a ha hc hs)

theorem heatNormalOneAmplitudeL2_pairing (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : smoothCovariantFields M 1) :
    inner ℝ (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothOneFormL2Linear v) =
      ∫ f, inner ℝ (heatNormalOneAmplitude D C hCt hP hD a ha hc hs f)
        (smoothOneFormEuclideanValue (g := g) v f) ∂canonicalFrameMeasure g o :=
  oneFormFromContinuous_pairing _ v

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact continuous one-form chart data and their genuine smooth realizations. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] {g : SmoothMetric M}

def heatOneChart (g : SmoothMetric M) (c : M)
    (F : FourSpace → CovariantCoordinates 1) (hF : ContinuousOn F (chartAt FourSpace c).target)
    (hc : HasCompactSupport F) (hs : tsupport F ⊆ (chartAt FourSpace c).target) :
    C(FrameBundle g, FourSpace) :=
  ⟨fun f => WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i]),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (continuous_apply ![i]).comp
      (heatNormalOneFrameLift_continuous g c (chartAt FourSpace c).symm F
        (fun _ h => h) hF hc hs)))⟩

theorem heatOneChart_smooth
    (c : M) (F : FourSpace → CovariantCoordinates 1)
    (hF : ContDiffOn ℝ ∞ F (chartAt FourSpace c).target)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) :
    heatOneChart g c F hF.continuousOn
      (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt) =
      smoothOneFormEuclideanValue (g := g) (oneFormChartTest g c F hF hK hKt hFs) := by
  apply ContinuousMap.ext
  intro f
  apply WithLp.ofLp_injective 2
  funext i
  by_cases hf : f.base ∈ (chartAt FourSpace c).source
  · change heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i] =
      covariantFieldFramed g (oneFormChartTest g c F hF hK hKt hFs).val f ![i]
    rw [heatNormalOneFrameLift, ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hf)]
    rw [heat_covariantField_chart g _ c f hf,
      oneFormChartTest_coordinates c F hF hK hKt hFs _ ((chartAt FourSpace c).map_source hf)]
    rfl
  · have hz := oneFormChartTest_zero_off (g := g) c F hF hK hKt hFs f.base (by
      rintro ⟨z, hz, hzf⟩
      exact hf (hzf ▸ (chartAt FourSpace c).map_target (hKt hz)))
    change heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i] =
      covariantFieldFramed g (oneFormChartTest g c F hF hK hKt hFs).val f ![i]
    rw [heatNormalOneFrameLift, ite_eq_right (show f.base ∉ (chartAt FourSpace c).symm.target from hf)]
    rw [covariantFieldFramed, covariantFieldCoordinates_center, hz, frameTensor_zero_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual even/odd Hodge–Dirac maps in four dimensions, expressed
using the scalar, one-form and two-form bundles already constructed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev HodgeEvenSections (o : FrameOrientation g) :=
  SmoothScalar (M := M) × smoothTwoForms o × SmoothScalar (M := M)

abbrev HodgeOddSections (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] :=
  smoothCovariantFields M 1 × smoothCovariantFields M 1

def smoothHodgeDiracEven : HodgeEvenSections o →ₗ[ℝ] HodgeOddSections M :=
  let f : HodgeEvenSections o →ₗ[ℝ] SmoothScalar (M := M) := LinearMap.fst ℝ _ _
  let a : HodgeEvenSections o →ₗ[ℝ] smoothTwoForms o :=
    (LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ _ _)
  let b : HodgeEvenSections o →ₗ[ℝ] SmoothScalar (M := M) :=
    (LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)
  (((smoothScalarDifferentialLinear g).comp f) +
    ((smoothTwoFormCodifferentialLinear (o := o)).comp a)).prod
      (((hodgeComplexD2 (o := o)).comp a) - ((smoothScalarDifferentialLinear g).comp b))

def smoothHodgeDiracOdd : HodgeOddSections M →ₗ[ℝ] HodgeEvenSections o :=
  let u : HodgeOddSections M →ₗ[ℝ] smoothCovariantFields M 1 := LinearMap.fst ℝ _ _
  let v : HodgeOddSections M →ₗ[ℝ] smoothCovariantFields M 1 := LinearMap.snd ℝ _ _
  (-((smoothOneFormDivergence g).comp u)).prod
    ((((smoothOneFormExteriorLinear (o := o)).comp u) +
      ((smoothTwoFormHodge o).comp ((smoothOneFormExteriorLinear (o := o)).comp v))).prod
        ((smoothOneFormDivergence g).comp v))

theorem smoothHodgeDiracEven_apply (f b : SmoothScalar (M := M)) (a : smoothTwoForms o) :
    smoothHodgeDiracEven (f, a, b) =
      (smoothScalarDifferential g f + smoothTwoFormCodifferentialField a,
        smoothTwoFormCodifferentialField (smoothTwoFormHodge o a) - smoothScalarDifferential g b) :=
  rfl

theorem smoothHodgeDiracOdd_apply (u v : smoothCovariantFields M 1) :
    smoothHodgeDiracOdd (o := o) (u, v) =
      (-smoothOneFormDivergence g u,
        smoothOneFormExterior u + smoothTwoFormHodge o (smoothOneFormExterior v),
        smoothOneFormDivergence g v) := rfl

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem smoothHodgeDirac_square_even (hRic : RicciThree g)
    (f b : SmoothScalar (M := M)) (a : smoothTwoForms o) :
    smoothHodgeDiracOdd (smoothHodgeDiracEven (o := o) (f, a, b)) =
      (-smoothOneFormDivergence g (smoothScalarDifferential g f),
        smoothHodgeLaplacian hRic a,
        -smoothOneFormDivergence g (smoothScalarDifferential g b)) := by
  rw [smoothHodgeDiracEven_apply, smoothHodgeDiracOdd_apply]
  apply Prod.ext
  · rw [map_add, smoothTwoFormCodifferential_divergence hRic, add_zero]
  · apply Prod.ext
    · change smoothOneFormExteriorLinear (smoothScalarDifferential g f +
          smoothTwoFormCodifferentialField a) +
        smoothTwoFormHodge o (smoothOneFormExteriorLinear
          (smoothTwoFormCodifferentialField (smoothTwoFormHodge o a) -
            smoothScalarDifferential g b)) = _
      rw [map_add, map_sub]
      change smoothOneFormExterior (smoothScalarDifferential g f) + smoothTwoFormDDelta a +
        smoothTwoFormHodge o (smoothTwoFormDDelta (smoothTwoFormHodge o a) -
          smoothOneFormExterior (smoothScalarDifferential g b)) = _
      rw [smoothScalarDifferential_closed, smoothScalarDifferential_closed,
        zero_add, sub_zero]
      exact (smoothHodgeLaplacian_dDelta_hodge hRic a).symm
    · rw [map_sub, smoothTwoFormCodifferential_divergence hRic, zero_sub]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form reconstruction is contractive in the continuous norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}
local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem oneFormFromFrameL2_norm_le (F : Lp FourSpace 2 (canonicalFrameMeasure g o)) :
    ‖oneFormFromFrameL2 F‖ ≤ ‖F‖ := by
  let w := oneFormFromFrameL2 F
  have hi := abs_real_inner_le_norm F (oneFormFrameL2 w)
  rw [oneFormFrameL2_norm] at hi
  have he : ‖w‖ ^ 2 = inner ℝ F (oneFormFrameL2 w) := by
    rw [← real_inner_self_eq_norm_sq]
    exact oneFormFromFrameL2_pairing F w
  by_cases hw : ‖w‖ = 0
  · change ‖w‖ ≤ ‖F‖
    rw [hw]
    exact norm_nonneg _
  · have hp := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    change ‖w‖ ≤ ‖F‖
    nlinarith [le_abs_self (inner ℝ F (oneFormFrameL2 w))]

theorem oneFormFromContinuous_norm_le (F : C(FrameBundle g, FourSpace)) :
    ‖oneFormFromContinuous (o := o) F‖ ≤ ‖F‖ := by
  apply (oneFormFromFrameL2_norm_le _).trans
  have hnorm : ‖(ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ :
      C(FrameBundle g, FourSpace) →L[ℝ] Lp FourSpace 2 (canonicalFrameMeasure g o))‖ ≤ 1 := by
    simpa [measureUnivNNReal] using
      ContinuousMap.toLp_norm_le (𝕜 := ℝ) (E := FourSpace) (p := 2) (canonicalFrameMeasure g o)
  exact (ContinuousLinearMap.le_opNorm _ F).trans
    ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg F)).trans_eq (one_mul _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form heat semigroup, defined from the complete smooth
Hodge eigenbasis. Positivity of the spectrum comes from positive Ricci curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormHeatRate_nonneg (i : OneFormEigenIndex hRic d) :
    0 ≤ oneFormHeatRate hRic d i := (oneFormHeatRate_pos hRic d i).le

def oneFormHeatWeight (t : ℝ≥0)
    (μ : OneFormEigenIndex hRic d) : ℝ :=
  Real.exp (-(t : ℝ) * oneFormHeatRate hRic d μ)

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormHeatWeight_bound (t : ℝ≥0)
    (μ : OneFormEigenIndex hRic d) : |oneFormHeatWeight hRic d t μ| ≤ 1 := by
  rw [oneFormHeatWeight, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg)
    (oneFormHeatRate_nonneg hRic d μ)

def oneFormHeat (t : ℝ≥0) : OneFormL2 o →L[ℝ] OneFormL2 o :=
  oneFormSpectralMultiplier hRic d (oneFormHeatWeight hRic d t) 1 zero_le_one
    (oneFormHeatWeight_bound hRic d t)

theorem oneFormHeat_coordinate (t : ℝ≥0) (f : OneFormL2 o)
    (μ : OneFormEigenIndex hRic d) :
    (oneFormSpectralEquiv hRic d (oneFormHeat hRic d t f)) μ =
      oneFormHeatWeight hRic d t μ • (oneFormSpectralEquiv hRic d f) μ :=
  oneFormSpectralMultiplier_coordinate hRic d _ _ _ _ f μ

theorem oneFormHeat_zero (f : OneFormL2 o) :
    oneFormHeat hRic d 0 f = f := by
  apply (oneFormSpectralEquiv hRic d).injective
  apply lp.ext
  funext μ
  rw [oneFormHeat_coordinate]
  simp only [oneFormHeatWeight, NNReal.coe_zero, neg_zero, zero_mul, Real.exp_zero, one_smul]

theorem oneFormHeat_add (t s : ℝ≥0) (f : OneFormL2 o) :
    oneFormHeat hRic d (t + s) f = oneFormHeat hRic d t (oneFormHeat hRic d s f) := by
  apply (oneFormSpectralEquiv hRic d).injective
  apply lp.ext
  funext μ
  rw [oneFormHeat_coordinate, oneFormHeat_coordinate, oneFormHeat_coordinate, smul_smul]
  congr 1
  simp only [oneFormHeatWeight, NNReal.coe_add]
  rw [← Real.exp_add]
  congr 1
  ring

theorem oneFormHeat_contraction (t : ℝ≥0) (f : OneFormL2 o) :
    ‖oneFormHeat hRic d t f‖ ≤ ‖f‖ := by
  simpa only [oneFormHeat, one_mul] using oneFormSpectralMultiplier_norm hRic d
    (oneFormHeatWeight hRic d t) 1 zero_le_one (oneFormHeatWeight_bound hRic d t) f

theorem oneFormHeat_selfAdjoint (t : ℝ≥0) (f h : OneFormL2 o) :
    inner ℝ (oneFormHeat hRic d t f) h = inner ℝ f (oneFormHeat hRic d t h) :=
  oneFormSpectralMultiplier_selfAdjoint hRic d _ _ _ _ f h

theorem oneFormHeat_nonneg (t : ℝ≥0) (f : OneFormL2 o) :
    0 ≤ inner ℝ (oneFormHeat hRic d t f) f := by
  rw [oneFormHeat, oneFormSpectralMultiplier_inner]
  exact tsum_nonneg fun μ => mul_nonneg (Real.exp_pos _).le (real_inner_self_nonneg (x := _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Dominated spectral convergence for the actual one-form heat space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormSpectralMultiplier_sub_norm_sq
    (a b : OneFormEigenIndex hRic d → ℝ)
    (ha : ∀ μ, |a μ| ≤ 1) (hb : ∀ μ, |b μ| ≤ 1) (f : OneFormL2 o) :
    ‖oneFormSpectralMultiplier hRic d a 1 zero_le_one ha f -
      oneFormSpectralMultiplier hRic d b 1 zero_le_one hb f‖ ^ 2 =
      ∑' μ, (a μ - b μ) ^ 2 * ‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (oneFormSpectralEquiv hRic d).inner_map_map,
    map_sub, lp.inner_eq_tsum]
  apply tsum_congr
  intro μ
  change inner ℝ
    ((oneFormSpectralEquiv hRic d (oneFormSpectralMultiplier hRic d a 1 zero_le_one ha f)) μ -
      (oneFormSpectralEquiv hRic d (oneFormSpectralMultiplier hRic d b 1 zero_le_one hb f)) μ)
    ((oneFormSpectralEquiv hRic d (oneFormSpectralMultiplier hRic d a 1 zero_le_one ha f)) μ -
      (oneFormSpectralEquiv hRic d (oneFormSpectralMultiplier hRic d b 1 zero_le_one hb f)) μ) = _
  rw [oneFormSpectralMultiplier_coordinate, oneFormSpectralMultiplier_coordinate,
    ← sub_smul, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem oneFormSpectralMultiplier_tendsto {α : Type*} {l : Filter α}
    (a : α → OneFormEigenIndex hRic d → ℝ)
    (b : OneFormEigenIndex hRic d → ℝ)
    (ha : ∀ x μ, |a x μ| ≤ 1) (hb : ∀ μ, |b μ| ≤ 1)
    (hab : ∀ μ, Tendsto (fun x => a x μ) l (𝓝 (b μ))) (f : OneFormL2 o) :
    Tendsto (fun x => oneFormSpectralMultiplier hRic d (a x) 1 zero_le_one (ha x) f) l
      (𝓝 (oneFormSpectralMultiplier hRic d b 1 zero_le_one hb f)) := by
  have hsum : Summable (fun μ : OneFormEigenIndex hRic d =>
      4 * ‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2) := by
    have hs := lp.summable_inner (𝕜 := ℝ)
      (oneFormSpectralEquiv hRic d f) (oneFormSpectralEquiv hRic d f)
    simp only [real_inner_self_eq_norm_sq] at hs
    exact hs.mul_left 4
  have hbound (x : α) (μ : OneFormEigenIndex hRic d) :
      ‖(a x μ - b μ) ^ 2 * ‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2‖ ≤
        4 * ‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2 := by
    have hdiff : |a x μ - b μ| ≤ 2 :=
      (abs_sub (a x μ) (b μ)).trans (by linarith only [ha x μ, hb μ])
    have hsq : (a x μ - b μ) ^ 2 ≤ 4 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hdiff)
        (add_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (abs_nonneg (a x μ - b μ)))
      nlinarith only [hprod, sq_abs (a x μ - b μ)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hpoint (μ : OneFormEigenIndex hRic d) :
      Tendsto (fun x => (a x μ - b μ) ^ 2 * ‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2)
        l (𝓝 (0 : ℝ)) := by
    convert (((hab μ).sub_const (b μ)).pow 2).mul_const
      (‖(oneFormSpectralEquiv hRic d f) μ‖ ^ 2) using 1
    simp
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint
    (Eventually.of_forall hbound)
  simp only [tsum_zero] at ht
  have hn : Tendsto (fun x => ‖oneFormSpectralMultiplier hRic d (a x) 1 zero_le_one (ha x) f -
      oneFormSpectralMultiplier hRic d b 1 zero_le_one hb f‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    simpa only [oneFormSpectralMultiplier_sub_norm_sq] using ht
  have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hs using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · exact congrArg nhds Real.sqrt_zero.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! An absolute integral bound for eigenform pairings, used to justify
the actual kernel's double-integral action. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigenSection_pairing_integral_norm_bound (hRic : RicciThree g)
    (i : TwoFormEigenIndex (o := o) hRic) (u : smoothTwoForms o) :
    (∫ x, ‖inner ℝ ((twoFormEigenSection hRic i).val x) (u.val x)‖
      ∂normalizedVolume g) ≤ (1 + ‖smoothTwoFormToL2 (u : SmoothL2TwoForm o)‖ ^ 2) / 2 := by
  have := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  have he : Integrable (fun x => ‖(twoFormEigenSection hRic i).val x‖ ^ 2)
      (normalizedVolume g) :=
    ((smoothTwoForm_norm_continuous _).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hu : Integrable (fun x => ‖u.val x‖ ^ 2) (normalizedVolume g) :=
    ((smoothTwoForm_norm_continuous _).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x, (‖(twoFormEigenSection hRic i).val x‖ ^ 2 + ‖u.val x‖ ^ 2) / 2
        ∂normalizedVolume g := by
      apply integral_mono (smoothTwoForm_pairing_integrable _ _).norm ((he.add hu).div_const 2)
      intro x
      change ‖inner ℝ ((twoFormEigenSection hRic i).val x) (u.val x)‖ ≤
        (‖(twoFormEigenSection hRic i).val x‖ ^ 2 + ‖u.val x‖ ^ 2) / 2
      have hi := norm_inner_le_norm (𝕜 := ℝ) ((twoFormEigenSection hRic i).val x) (u.val x)
      have hs := sq_nonneg (‖(twoFormEigenSection hRic i).val x‖ - ‖u.val x‖)
      nlinarith
    _ = _ := by
      rw [integral_div, integral_add he hu, twoFormEigenSection_integral_norm]
      exact congrArg (fun a : ℝ => (1 + a) / 2)
        (smoothTwoFormToL2_norm_sq (u : SmoothL2TwoForm o)).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 spectral heat column with one frame and component fixed.
Square summability follows from the proved positive-time diagonal estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Manifold _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatFrameCoefficient (hRic : RicciThree g) (t : ℝ≥0)
    (e : FrameBundle g) (l : Fin 6) (i : TwoFormEigenIndex (o := o) hRic) : ℝ :=
  twoFormHeatWeight hRic t i.1 * twoFormFrameValue o (twoFormEigenSection hRic i).val e l

theorem twoFormHeatFrameCoefficient_eq (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 6) (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormHeatFrameCoefficient hRic t e l i =
      twoFormFrameValue o (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val e l := by
  have h := congrArg (fun v : smoothTwoForms o => twoFormFrameValue o v.val e l)
    (twoFormHeatSection_eigen hRic t ht i)
  change _ = twoFormFrameValue o
    (twoFormHeatWeight hRic t i.1 • (twoFormEigenSection hRic i).val) e l at h
  rw [twoFormFrameValue_smul] at h
  exact h.symm

theorem twoFormHeatFrameCoefficient_mem (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 6) : Memℓp (twoFormHeatFrameCoefficient (o := o) hRic t e l) 2 := by
  have hs := twoFormHeatSection_pointwise_square_summable (o := o) hRic t ht e.base
  have hn : Memℓp (fun i : TwoFormEigenIndex (o := o) hRic =>
      ‖(twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val e.base‖) 2 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, norm_norm] using hs
  apply hn.mono
  intro i
  rw [twoFormHeatFrameCoefficient_eq hRic t ht]
  exact (PiLp.norm_apply_le _ l).trans_eq
    (twoFormFrameValue_norm o (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val e)

def twoFormHeatFrameColumn (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 6) : TwoFormL2 o :=
  (twoFormEigenbasis hRic).repr.symm
    ⟨twoFormHeatFrameCoefficient hRic t e l, twoFormHeatFrameCoefficient_mem hRic t ht e l⟩

theorem twoFormHeatFrameColumn_eigen (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 6) (i : TwoFormEigenIndex (o := o) hRic) :
    inner ℝ (twoFormHeatFrameColumn hRic t ht e l) (twoFormEigenvector hRic i) =
      twoFormHeatFrameCoefficient hRic t e l i := by
  rw [real_inner_comm, ← twoFormEigenbasis_apply hRic i,
    ← HilbertBasis.repr_apply_apply, twoFormHeatFrameColumn,
    LinearIsometryEquiv.apply_symm_apply]

theorem twoForm_eq_of_eigen_pairing (hRic : RicciThree g) (v w : TwoFormL2 o)
    (h : ∀ i : TwoFormEigenIndex (o := o) hRic,
      inner ℝ v (twoFormEigenvector hRic i) = inner ℝ w (twoFormEigenvector hRic i)) : v = w := by
  apply (twoFormEigenbasis hRic).repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, twoFormEigenbasis_apply]
  exact (real_inner_comm _ _).trans ((h i).trans (real_inner_comm _ _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! One Volterra step gives the factorial gain for Gaussian-dominated
two-form kernel corrections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set

noncomputable section

local notation "V" => TwoFormFour →L[ℝ] TwoFormFour

theorem fourHeatVolterra_step_bound (n : ℕ) (A t : ℝ) (hA : 0 ≤ A) (ht : 0 < t)
    (x : FourSpace) (F G : ℝ → FourSpace → V)
    (hF : ∀ s ∈ Ioo 0 t, ∀ z,
      ‖F s z‖ ≤ A * fourHeatGaussian (t - s) (x - z))
    (hG : ∀ s ∈ Ioo 0 t, ∀ z,
      ‖G s z‖ ≤ (A ^ (n + 1) * s ^ n / (n.factorial : ℝ)) * fourHeatGaussian s z) :
    ‖∫ s : ℝ in 0..t, ∫ z : FourSpace, (F s z).comp (G s z)‖ ≤
      (A ^ (n + 2) * t ^ (n + 1) / ((n + 1).factorial : ℝ)) * fourHeatGaussian t x := by
  have := FiniteDimensional.complete ℝ V
  have hstep (s : ℝ) (hs : s ∈ Ioo 0 t) :
      ‖∫ z : FourSpace, (F s z).comp (G s z)‖ ≤
        (A ^ (n + 2) / (n.factorial : ℝ) * fourHeatGaussian t x) * s ^ n := by
    have h := fourHeatTwoForm_composition_integral_bound (t - s) s A
      (A ^ (n + 1) * s ^ n / (n.factorial : ℝ)) (sub_pos.mpr hs.2) hs.1 hA x
      (F s) (G s) (hF s hs) (hG s hs)
    rw [sub_add_cancel] at h
    calc
      _ ≤ _ := h
      _ = _ := by rw [pow_succ A (n + 1)]; ring
  have h := fourHeatTimePolynomial_bound
    (fun s => ∫ z : FourSpace, (F s z).comp (G s z)) t ht n
    (A ^ (n + 2) / (n.factorial : ℝ) * fourHeatGaussian t x) hstep
  calc
    _ ≤ _ := h
    _ = _ := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Additivity of the actual normal amplitude realization, needed to
retain cancellation in the heat residual before estimating its norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCoordinates_add (a b : FourSpace → FourSpace) :
    heatNormalOneCoordinates D (a + b) =
      heatNormalOneCoordinates D a + heatNormalOneCoordinates D b := by
  funext x v
  change frameTensor (D.point x).2⁻¹ (fun q => (a x + b x) (q 0)) v = _
  have he : (fun q : Fin 1 → Fin 4 => (a x + b x) (q 0)) =
      (fun q => a x (q 0)) + (fun q => b x (q 0)) := rfl
  rw [he, frameTensor_add]
  rfl

omit [T3Space M] [CompactSpace M] in
theorem heatNormalOneFrameLift_add (C : OpenPartialHomeomorph FourSpace M)
    (T U : FourSpace → CovariantCoordinates 1) :
    heatNormalOneFrameLift g c C (T + U) =
      heatNormalOneFrameLift g c C T + heatNormalOneFrameLift g c C U := by
  classical
  funext f v
  by_cases hf : f.base ∈ C.target
  · simp only [heatNormalOneFrameLift, ite_eq_left hf, Pi.add_apply, frameTensor_add]
  · simp only [heatNormalOneFrameLift, ite_eq_right hf, Pi.add_apply, Pi.zero_apply, add_zero]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem heatNormalOneAmplitudeL2_add
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a b : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ C.source) (hsb : tsupport b ⊆ C.source) :
    heatNormalOneAmplitudeL2 D C hCt hP hD (a + b) (ha.add hb) (hca.add hcb)
      ((tsupport_add a b).trans (union_subset hsa hsb)) =
      heatNormalOneAmplitudeL2 D C hCt hP hD a ha hca hsa +
        heatNormalOneAmplitudeL2 D C hCt hP hD b hb hcb hsb := by
  have hT : heatNormalOneAmplitude D C hCt hP hD (a + b) (ha.add hb) (hca.add hcb)
      ((tsupport_add a b).trans (union_subset hsa hsb)) =
      heatNormalOneAmplitude D C hCt hP hD a ha hca hsa +
        heatNormalOneAmplitude D C hCt hP hD b hb hcb hsb := by
    ext f v
    change heatNormalOneFrameLift g c C (heatNormalOneCoordinates D (a + b)) f ![v] = _
    rw [heatNormalOneCoordinates_add, heatNormalOneFrameLift_add]
    rfl
  change oneFormFromContinuous _ = oneFormFromContinuous _ + oneFormFromContinuous _
  rw [hT, map_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Jointly continuous compact normal amplitudes give continuous curves
in the global one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatNormalOneAmplitudeL2_continuous_family
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (A : ℝ → FourSpace → FourSpace) (ha : ∀ t, ContDiff ℝ 2 (A t))
    (hc : ∀ t, HasCompactSupport (A t)) (hs : ∀ t, tsupport (A t) ⊆ C.source)
    (hA : ContinuousOn (fun z : ℝ × FourSpace => A z.1 z.2) (Ioi 0 ×ˢ C.source))
    (K : Set FourSpace) (hK : IsCompact K) (hKC : K ⊆ C.source)
    (hsK : ∀ t > 0, tsupport (A t) ⊆ K) :
    ContinuousOn (fun t => heatNormalOneAmplitudeL2 D C hCt hP hD (A t) (ha t) (hc t) (hs t)) (Ioi 0) := by
  have hcoord := heatNormalOneCoordinates_joint_continuous C hP hD A hA
  have hframe := heatNormalOneFrameLift_joint_continuous (g := g) C hCt
    (fun t => heatNormalOneCoordinates D (A t)) hcoord K hK hKC
    (fun t ht => (heatNormalOneCoordinates_support D (A t)).trans (hsK t ht))
  have hTF : ContinuousOn (fun z : ℝ × FrameBundle g =>
      (WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D (A z.1)) z.2 ![i])
        : FourSpace)) (Ioi 0 ×ˢ univ) :=
    by
    apply (PiLp.continuous_toLp 2 _).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply ![i]).comp_continuousOn hframe
  have hcurve : ContinuousOn (fun t => heatNormalOneAmplitude D C hCt hP hD
      (A t) (ha t) (hc t) (hs t)) (Ioi 0) :=
    ContinuousMap.continuousOn_of_continuousOn_uncurry _ hTF
  exact oneFormFromContinuous.continuous.comp_continuousOn hcurve

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal one-form lift preserves the actual orthonormal fiber norm. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneAmplitude_norm_sq
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (f : FrameBundle g) (hf : f.base ∈ C.target) :
    ‖heatNormalOneAmplitude D C hCt hP hD a ha hc hs f‖ ^ 2 =
      ‖a (C.symm f.base)‖ ^ 2 := by
  let x := C.symm f.base
  have hx : x ∈ C.source := C.map_target hf
  have hxb := hD hx
  have hbase : (D.point x).1 = chartAt FourSpace c f.base := by
    rw [D.exponential x hxb, ← hE hx, C.right_inv hf]
  have hF := frameChartMatrix_normalizes g c f (hCt hf)
  rw [← hbase] at hF
  have hi : (D.point x).2⁻¹ * (D.point x).2 = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (heatNormalFrame_matrix_nondegenerate D hxb))
  have hback : frameTensor (D.point x).2 (heatNormalOneCoordinates D a x) =
      fun v => a x (v 0) := by
    unfold heatNormalOneCoordinates
    rw [← frameTensor_mul, hi, frameTensor_one]
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i] ^ 2) = _
  rw [← oneForm_squareNorm, heatNormalOneFrameLift, ite_eq_left hf]
  change frameTensorPairing
    (frameTensor (frameChartMatrix g c f) (frameTensor (D.point x).2⁻¹ (fun v => a x (v 0))))
    (frameTensor (frameChartMatrix g c f) (heatNormalOneCoordinates D a x)) = _
  rw [heat_normal_one_pairing _ _ _ (D.orthonormal x hxb) hF, hback]
  change frameTensorSquareNorm (fun v => a x (v 0)) = _
  rw [oneForm_squareNorm, EuclideanSpace.real_norm_sq_eq]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pairing compact normal one-form amplitudes with actual smooth sections. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heat_oneTensor_inner (T U : CovariantCoordinates 1) :
    inner ℝ (WithLp.toLp 2 (fun i => T ![i]) : FourSpace) (WithLp.toLp 2 (fun i => U ![i])) =
      frameTensorPairing T U := by
  unfold frameTensorPairing
  rw [sum_tensor_indices_cons]
  simp only [Fintype.sum_unique, PiLp.inner_apply, Real.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg₂ (· * ·)
  · apply congrArg T
    ext j
    fin_cases j
    rfl
  · apply congrArg U
    ext j
    fin_cases j
    rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

def heatNormalOneValue (c : M) (P : FourSpace → CoordinateFrameSpace)
    (v : smoothCovariantFields M 1) (x : FourSpace) : FourSpace :=
  WithLp.toLp 2 (heatNormalOneFormValue c P v x)

theorem heatNormalOneLift_pairing (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (v : smoothCovariantFields M 1) (f : FrameBundle g) :
    inner ℝ (WithLp.toLp 2
      (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i]) : FourSpace)
      (smoothOneFormEuclideanValue (g := g) v f) =
    heatNormalScalarLift C (fun x => inner ℝ (a x) (heatNormalOneValue c D.point v x)) f.base := by
  classical
  change inner ℝ (WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i]) : FourSpace)
    (WithLp.toLp 2 (fun i => covariantFieldFramed g v.val f ![i])) = _
  rw [heat_oneTensor_inner]
  by_cases hf : f.base ∈ C.target
  · let x := C.symm f.base
    have hx : x ∈ C.source := C.map_target hf
    have hxb := hD hx
    have hbase : (D.point x).1 = chartAt FourSpace c f.base := by
      rw [D.exponential x hxb, ← hE hx, C.right_inv hf]
    have hF := frameChartMatrix_normalizes g c f (hCt hf)
    rw [← hbase] at hF
    rw [heatNormalOneFrameLift, ite_eq_left hf, heatNormalScalarLift_on_target C _ hf,
      heatNormalOneCoordinates, heat_covariantField_chart g v.val c f (hCt hf)]
    change frameTensorPairing
      (frameTensor (frameChartMatrix g c f) (frameTensor (D.point x).2⁻¹ (fun v => a x (v 0))))
      (frameTensor (frameChartMatrix g c f) (covariantFieldCoordinates v.val c (chartAt FourSpace c f.base))) = _
    rw [← hbase, heat_normal_one_pairing _ _ _ (D.orthonormal x hxb) hF]
    have h := heat_oneTensor_inner (fun q => a x (q 0))
      (frameTensor (D.point x).2 (covariantFieldCoordinates v.val c (D.point x).1))
    exact h.symm
  · rw [heatNormalOneFrameLift, ite_eq_right hf, heatNormalScalarLift, ite_eq_right hf]
    simp only [frameTensorPairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual local scalar normal parametrix through order three, with
its exact residual. This is a finite construction, not an assumed expansion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def heatNormalParametrix (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (t : ℝ) (x : FourSpace) : ℝ :=
  fourHeatGaussian t x * fourHeatPolynomial (fun i : Fin 4 => heatNormalCoefficient g o e i) t x

theorem heatNormalParametrix_residual (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ),
      deriv (fun s => heatNormalParametrix g o e s x) t +
        fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
          (heatNormalParametrix g o e t) x =
      fourHeatGaussian t x * t ^ 3 *
        fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
          (heatNormalCoefficient g o e 3) x := by
  obtain ⟨r, hr, hT⟩ := heatNormalCoefficient_transport g o hRic e he
  refine ⟨r, hr, ?_⟩
  intro x hx t ht
  obtain ⟨hE, h0, hnext⟩ := hT x hx
  have hreg (i : Fin 4) : ContDiff ℝ 2 (heatNormalCoefficient g o e i) :=
    (heatNormalCoefficient_contDiff g o e i (by omega)).of_le (by norm_num)
  apply fourHeatPolynomial_gaussian_residual _ _ _ _ hreg t ht x hE h0
  · simpa using hnext 0 (by omega)
  · convert hnext 1 (by omega) using 1 <;> norm_num
  · convert hnext 2 (by omega) using 1 <;> norm_num

theorem heatNormalParametrix_diagonal_residual_tendsto (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    Tendsto (fun t : ℝ => deriv (fun s => heatNormalParametrix g o e s 0) t +
      fourHeatLocalOperator (heatNormalMetric g o e 0)⁻¹ (heatNormalDrift g o e 0) 0
        (heatNormalParametrix g o e t) 0) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨r, hr, hR⟩ := heatNormalParametrix_residual g o hRic e he
  let C := fourHeatLocalOperator (heatNormalMetric g o e 0)⁻¹ (heatNormalDrift g o e 0) 0
    (heatNormalCoefficient g o e 3) 0
  have hlim : Tendsto (fun t : ℝ => t / (16 * Real.pi ^ 2) * C) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t / (16 * Real.pi ^ 2) * C) := by fun_prop
    simpa using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [hR 0 (by simpa using hr) t ht]
  change t / (16 * Real.pi ^ 2) * C = fourHeatGaussian t 0 * t ^ 3 * C
  rw [mul_comm (fourHeatGaussian t 0) (t ^ 3),
    show (3 : ℕ) = 1 + 2 from rfl, fourHeatGaussian_diagonal_power 1 t ht, pow_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform control of compact chart tensors in the frame-bundle norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourSpace_norm_le_sum (v : Fin 4 → ℝ) :
    ‖(WithLp.toLp 2 v : FourSpace)‖ ≤ ∑ i, |v i| := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun i => |v i|) (fun _ _ => abs_nonneg _)
  simp only [sq_abs] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mp
  simpa only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using hs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M}

local instance heatOneChartBoundCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatOneChart_bound (c : M) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (F : FourSpace → CovariantCoordinates 1)
      (hF : ContinuousOn F (chartAt FourSpace c).target) (hFs : tsupport F ⊆ K)
      (r : ℝ), 0 ≤ r → (∀ z a, |F z a| ≤ r) →
      ‖heatOneChart g c F hF
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt)‖ ≤ B * r := by
  let L : Set (FrameBundle g) := (fun f => f.base) ⁻¹' ((chartAt FourSpace c).symm '' K)
  have hLc : IsCompact L :=
    ((hK.image_of_continuousOn ((chartAt FourSpace c).continuousOn_symm.mono hKt)).isClosed.preimage
      (continuous_frameBase g)).isCompact
  have hLs (f : FrameBundle g) (hf : f ∈ L) : f.base ∈ (chartAt FourSpace c).source := by
    obtain ⟨z, hz, he⟩ := hf
    change (chartAt FourSpace c).symm z = f.base at he
    rw [← he]
    exact (chartAt FourSpace c).map_target (hKt hz)
  have hcont : ContinuousOn (fun f : FrameBundle g => tensorTransportWeight 1 (frameChartMatrix g c f)) L := by
    intro f hf
    exact ((tensorTransportWeight_continuous 1).continuousAt.comp
      (continuousAt_pi.mpr (fun i => continuousAt_pi.mpr (fun j =>
        frameChartMatrix_continuousAt g c f (hLs f hf) i j)))).continuousWithinAt
  obtain ⟨b, hb⟩ := (hLc.image_of_continuousOn hcont).isBounded.exists_norm_le
  let B := (Fintype.card (Fin 4) : ℝ) * max b 0
  refine ⟨B, mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _), ?_⟩
  intro F hF hFs r hr hFr
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)) hr)).mpr
  intro f
  by_cases hf : f ∈ L
  · have hw : tensorTransportWeight 1 (frameChartMatrix g c f) ≤ max b 0 :=
      (le_abs_self _).trans ((hb _ ⟨f, hf, rfl⟩).trans (le_max_left _ _))
    change ‖(WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i]) : FourSpace)‖ ≤ _
    rw [heatNormalOneFrameLift, ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hLs f hf)]
    refine (fourSpace_norm_le_sum _).trans ?_
    calc
      _ ≤ ∑ _a : Fin 4, tensorTransportWeight 1 (frameChartMatrix g c f) * r :=
        Finset.sum_le_sum (fun a _ => frameTensor_abs_le_weight _ _ r hr (hFr _) ![a])
      _ = (Fintype.card (Fin 4) : ℝ) * tensorTransportWeight 1 (frameChartMatrix g c f) * r := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
      _ ≤ B * r := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)) hr
  · have hz : heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f = 0 := by
      apply not_ne_iff.mp
      intro hn
      obtain ⟨z, hz, he⟩ := heatNormalOneFrameLift_support g c (chartAt FourSpace c).symm F hn
      exact hf ⟨z, hFs hz, he⟩
    change ‖(WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i]) : FourSpace)‖ ≤ _
    simp only [hz, Pi.zero_apply]
    change ‖(0 : FourSpace)‖ ≤ _
    rw [norm_zero]
    simpa using mul_nonneg (mul_nonneg (Nat.cast_nonneg (Fintype.card (Fin 4))) (le_max_right b 0)) hr

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two actual parity-changing Hodge–Dirac operators are formal
adjoints for the intrinsic L2 pairings. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneFormL2Pairing_differential (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) (u : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (smoothScalarDifferential g f) u =
      -(∫ e, f.val e.base * oneFormDivergence g u e.base ∂canonicalFrameMeasure g o) := by
  unfold smoothOneFormL2Pairing
  simp_rw [smoothScalarDifferential_framed]
  exact scalar_oneForm_adjoint hRic f u

theorem smoothOneFormL2Pairing_codifferential (hRic : RicciThree g)
    (a : smoothTwoForms o) (u : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (smoothTwoFormCodifferentialField a) u =
      smoothTwoFormL2Inner a (smoothOneFormExterior u) := by
  rw [smoothOneFormL2Pairing_comm]
  unfold smoothOneFormL2Pairing
  simp_rw [smoothTwoFormCodifferentialField_component]
  exact (smoothOneFormExterior_adjoint hRic u a).symm.trans (smoothTwoFormL2Inner_comm _ _)

def smoothHodgeEvenPairing (x y : HodgeEvenSections o) : ℝ :=
  (∫ e, x.1.val e.base * y.1.val e.base ∂canonicalFrameMeasure g o) +
    smoothTwoFormL2Inner x.2.1 y.2.1 +
    ∫ e, x.2.2.val e.base * y.2.2.val e.base ∂canonicalFrameMeasure g o

def smoothHodgeOddPairing (x y : HodgeOddSections M) : ℝ :=
  smoothOneFormL2Pairing (o := o) x.1 y.1 + smoothOneFormL2Pairing (o := o) x.2 y.2

theorem smoothHodgeDirac_adjoint (hRic : RicciThree g)
    (x : HodgeEvenSections o) (y : HodgeOddSections M) :
    smoothHodgeOddPairing (o := o) (smoothHodgeDiracEven x) y =
      smoothHodgeEvenPairing x (smoothHodgeDiracOdd y) := by
  obtain ⟨f, a, b⟩ := x
  obtain ⟨u, v⟩ := y
  rw [smoothHodgeDiracEven_apply, smoothHodgeDiracOdd_apply]
  change smoothOneFormL2Pairing (o := o)
      (smoothScalarDifferential g f + smoothTwoFormCodifferentialField a) u +
    smoothOneFormL2Pairing (o := o)
      (smoothTwoFormCodifferentialField (smoothTwoFormHodge o a) - smoothScalarDifferential g b) v =
    (∫ e, f.val e.base * (-smoothOneFormDivergence g u).val e.base ∂canonicalFrameMeasure g o) +
      smoothTwoFormL2Inner a (smoothOneFormExterior u + smoothTwoFormHodge o (smoothOneFormExterior v)) +
      ∫ e, b.val e.base * (smoothOneFormDivergence g v).val e.base ∂canonicalFrameMeasure g o
  rw [smoothOneFormL2Pairing_add, smoothOneFormL2Pairing_sub,
    smoothOneFormL2Pairing_differential hRic, smoothOneFormL2Pairing_differential hRic,
    smoothOneFormL2Pairing_codifferential hRic, smoothOneFormL2Pairing_codifferential hRic,
    smoothTwoFormL2Inner_hodge_left, smoothTwoFormL2Inner_add_right]
  change (-(∫ e, f.val e.base * oneFormDivergence g u e.base ∂canonicalFrameMeasure g o) +
      smoothTwoFormL2Inner a (smoothOneFormExterior u)) +
    (smoothTwoFormL2Inner a (smoothTwoFormHodge o (smoothOneFormExterior v)) -
      -(∫ e, b.val e.base * oneFormDivergence g v e.base ∂canonicalFrameMeasure g o)) =
    (∫ e, f.val e.base * -oneFormDivergence g u e.base ∂canonicalFrameMeasure g o) +
      (smoothTwoFormL2Inner a (smoothOneFormExterior u) +
        smoothTwoFormL2Inner a (smoothTwoFormHodge o (smoothOneFormExterior v))) +
      ∫ e, b.val e.base * oneFormDivergence g v e.base ∂canonicalFrameMeasure g o
  simp only [mul_neg, integral_neg]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The kernels of the actual even/odd Hodge–Dirac maps. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHodgeDiracOdd_kernel (hRic : RicciThree g)
    (u v : smoothCovariantFields M 1) (h : smoothHodgeDiracOdd (o := o) (u, v) = 0) :
    u = 0 ∧ v = 0 := by
  have hu := congrArg Prod.fst h
  have hv := congrArg (fun a => a.2.2) h
  have hm := congrArg (fun a => a.2.1) h
  change -smoothOneFormDivergence g u = 0 at hu
  change smoothOneFormDivergence g v = 0 at hv
  change smoothOneFormExterior u + smoothTwoFormHodge o (smoothOneFormExterior v) = 0 at hm
  have hperp := smoothOneForm_coexact_orthogonal_closed hRic v
    (smoothOneFormExterior (o := o) u) (smoothOneFormExterior_closed hRic u)
  have he := congrArg (fun a => smoothTwoFormL2Inner a (smoothOneFormExterior (o := o) u)) hm
  rw [smoothTwoFormL2Inner_add, hperp, add_zero] at he
  have hdu : smoothOneFormExterior (o := o) u = 0 :=
    smoothTwoFormL2Inner_definite _ (he.trans (by simp [smoothTwoFormL2Inner]))
  rw [hdu, zero_add] at hm
  have hdv : smoothOneFormExterior (o := o) v = 0 := by
    have ht := congrArg (smoothTwoFormHodge o) hm
    rwa [smoothTwoFormHodge_involutive, map_zero] at ht
  have htrace (w : smoothCovariantFields M 1) (hw : smoothOneFormDivergence g w = 0)
      (e : FrameBundle g) :
      (∑ i, covariantFieldFramed g (covariantFieldDerivative g w.val) e ![i,i]) = 0 := by
    rw [← oneFormDivergence_eq_frame]
    exact congrArg (fun f : SmoothScalar (M := M) => f.val e.base) hw
  exact ⟨oneForm_harmonic_eq_zero hRic u hdu (htrace u (neg_eq_zero.mp hu)),
    oneForm_harmonic_eq_zero hRic v hdv (htrace v hv)⟩

variable [PreconnectedSpace M]

theorem smoothHodgeDiracEven_kernel (hRic : RicciThree g)
    (f b : SmoothScalar (M := M)) (a : smoothTwoForms o)
    (h : smoothHodgeDiracEven (o := o) (f, a, b) = 0) :
    (∃ r : ℝ, f = smoothScalarConst r) ∧ a ∈ smoothHarmonicTwoForms ∧
      (∃ s : ℝ, b = smoothScalarConst s) := by
  have hs := congrArg (smoothHodgeDiracOdd (o := o)) h
  rw [smoothHodgeDirac_square_even hRic, map_zero] at hs
  have hf := congrArg Prod.fst hs
  have ha := congrArg (fun z => z.2.1) hs
  have hb := congrArg (fun z => z.2.2) hs
  change -smoothOneFormDivergence g (smoothScalarDifferential g f) = 0 at hf
  change smoothHodgeLaplacian hRic a = 0 at ha
  change -smoothOneFormDivergence g (smoothScalarDifferential g b) = 0 at hb
  have scalarConst (F : SmoothScalar (M := M))
      (hF : -smoothOneFormDivergence g (smoothScalarDifferential g F) = 0) :
      ∃ r : ℝ, F = smoothScalarConst r := by
    have hd := neg_eq_zero.mp hF
    have hl (e : FrameBundle g) : scalarLaplacian g F.val e = 0 := by
      rw [← oneFormDivergence_differential]
      exact congrArg (fun f : SmoothScalar (M := M) => f.val e.base) hd
    obtain ⟨r, hr⟩ := scalarLaplacian_kernel_constants g o hRic F.property hl
    exact ⟨r, Subtype.ext (funext hr)⟩
  exact ⟨scalarConst f hf, (smoothHodgeLaplacian_eq_zero_iff hRic a).mp ha, scalarConst b hb⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The computed symbol is the actual scalar-multiplication commutator
of the smooth Hodge–Dirac operator in every positive orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothOneFormFiber (g : SmoothMetric M) (e : FrameBundle g)
    (u : smoothCovariantFields M 1) : FourSpace :=
  WithLp.toLp 2 (fun i => covariantFieldFramed g u.val e ![i])

theorem smoothOneFormFiber_add (e : FrameBundle g) (u v : smoothCovariantFields M 1) :
    smoothOneFormFiber g e (u + v) = smoothOneFormFiber g e u + smoothOneFormFiber g e v := by
  ext i
  change covariantFieldFramed g (u.val + v.val) e ![i] = _
  rw [covariantFieldFramed_add]
  rfl

theorem smoothOneFormFiber_sub (e : FrameBundle g) (u v : smoothCovariantFields M 1) :
    smoothOneFormFiber g e (u - v) = smoothOneFormFiber g e u - smoothOneFormFiber g e v := by
  ext i
  simp only [smoothOneFormFiber, covariantFieldFramed_eq, Submodule.coe_sub]
  exact frameTensor_sub e.frame.matrix (u.val e.base) (v.val e.base) ![i]

theorem smoothOneFormFiber_differential (e : FrameBundle g) (f : SmoothScalar (M := M)) :
    smoothOneFormFiber g e (smoothScalarDifferential g f) = scalarDifferentialFiber g f e := by
  ext i
  exact smoothScalarDifferential_framed f e i

def twoFormCodifferentialFiber (e : FrameBundle g) (u : smoothTwoForms o) : FourSpace :=
  WithLp.toLp 2 (fun i => smoothTwoFormCodifferential u e i)

theorem smoothOneFormFiber_codifferential (e : FrameBundle g) (u : smoothTwoForms o) :
    smoothOneFormFiber g e (smoothTwoFormCodifferentialField u) = twoFormCodifferentialFiber e u := by
  ext i
  exact smoothTwoFormCodifferentialField_component u e i

def hodgeEvenFrameValue (e : FrameBundle g) (x : HodgeEvenSections o) : HodgeEvenFiber :=
  (x.1.val e.base, twoFormFrameValue o x.2.1.val e, x.2.2.val e.base)

def hodgeOddFrameValue (e : FrameBundle g) (x : HodgeOddSections M) : HodgeOddFiber :=
  (smoothOneFormFiber g e x.1, smoothOneFormFiber g e x.2)

def hodgeEvenProduct (ρ : SmoothScalar (M := M)) (x : HodgeEvenSections o) :
    HodgeEvenSections o :=
  (smoothScalarProduct ρ x.1, smoothTwoFormProduct ρ x.2.1, smoothScalarProduct ρ x.2.2)

theorem smoothHodgeDiracEven_frame (e : FrameBundle g)
    (f b : SmoothScalar (M := M)) (a : smoothTwoForms o) :
    hodgeOddFrameValue e (smoothHodgeDiracEven (f, a, b)) =
      (scalarDifferentialFiber g f e + twoFormCodifferentialFiber e a,
        twoFormCodifferentialFiber e (smoothTwoFormHodge o a) - scalarDifferentialFiber g b e) := by
  rw [smoothHodgeDiracEven_apply]
  exact Prod.ext
    ((smoothOneFormFiber_add e _ _).trans (by
      rw [smoothOneFormFiber_differential, smoothOneFormFiber_codifferential]))
    ((smoothOneFormFiber_sub e _ _).trans (by
      rw [smoothOneFormFiber_codifferential, smoothOneFormFiber_differential]))

theorem smoothTwoFormHodge_product (ρ : SmoothScalar (M := M)) (a : smoothTwoForms o) :
    smoothTwoFormHodge o (smoothTwoFormProduct ρ a) =
      smoothTwoFormProduct ρ (smoothTwoFormHodge o a) := by
  apply Subtype.ext
  funext x
  exact twoFormHodge.map_smul (ρ.val x) (a.val x)

variable [T2Space M] [CompactSpace M]

theorem scalarDifferentialFiber_product (ρ f : SmoothScalar (M := M)) (e : FrameBundle g) :
    scalarDifferentialFiber g (smoothScalarProduct ρ f) e =
      ρ.val e.base • scalarDifferentialFiber g f e + f.val e.base • scalarDifferentialFiber g ρ e := by
  ext i
  change scalarGradient g (smoothScalarProduct ρ f).val e i = _
  rw [scalarGradient_smoothScalarProduct]
  change _ = ρ.val e.base * scalarGradient g f.val e i + f.val e.base * scalarGradient g ρ.val e i
  ring

theorem twoFormCodifferentialFiber_product (ρ : SmoothScalar (M := M))
    (a : smoothTwoForms o) (e : FrameBundle g) :
    twoFormCodifferentialFiber e (smoothTwoFormProduct ρ a) =
      ρ.val e.base • twoFormCodifferentialFiber e a +
        twoFormCodifferentialSymbol (scalarDifferentialFiber g ρ e) (twoFormFrameValue o a.val e) := by
  ext i
  exact twoFormCodifferential_product ρ a e i

theorem smoothHodgeDiracEven_principalSymbol (ρ : SmoothScalar (M := M))
    (x : HodgeEvenSections o) (e : FrameBundle g) (he : e ∈ o.positive) :
    hodgeOddFrameValue e (smoothHodgeDiracEven (hodgeEvenProduct ρ x)) =
      ρ.val e.base • hodgeOddFrameValue e (smoothHodgeDiracEven x) +
        hodgeDiracEvenSymbol (scalarDifferentialFiber g ρ e) (hodgeEvenFrameValue e x) := by
  obtain ⟨f, a, b⟩ := x
  change hodgeOddFrameValue e (smoothHodgeDiracEven
    (smoothScalarProduct ρ f, smoothTwoFormProduct ρ a, smoothScalarProduct ρ b)) = _
  rw [smoothHodgeDiracEven_frame, smoothHodgeDiracEven_frame,
    smoothTwoFormHodge_product, scalarDifferentialFiber_product,
    scalarDifferentialFiber_product, twoFormCodifferentialFiber_product,
    twoFormCodifferentialFiber_product]
  change _ = _ + hodgeDiracEvenSymbol (scalarDifferentialFiber g ρ e)
    (f.val e.base, twoFormFrameValue o a.val e, b.val e.base)
  rw [hodgeDiracEvenSymbol_apply]
  have hs : twoFormFrameValue o (smoothTwoFormHodge o a).val e =
      twoFormHodge (twoFormFrameValue o a.val e) :=
    twoFormFrameValue_hodge o a.val e he
  rw [hs]
  apply Prod.ext
  · change _ = ρ.val e.base • (scalarDifferentialFiber g f e + twoFormCodifferentialFiber e a) +
      (f.val e.base • scalarDifferentialFiber g ρ e +
        twoFormCodifferentialSymbol (scalarDifferentialFiber g ρ e) (twoFormFrameValue o a.val e))
    module
  · change _ = ρ.val e.base • (twoFormCodifferentialFiber e (smoothTwoFormHodge o a) -
      scalarDifferentialFiber g b e) +
      (twoFormCodifferentialSymbol (scalarDifferentialFiber g ρ e)
        (twoFormHodge (twoFormFrameValue o a.val e)) - b.val e.base • scalarDifferentialFiber g ρ e)
    module

end
end PositiveEinsteinFour.Geometry
end


section

/-! The real signature involution and its anticommutation with the
actual Hodge–Dirac differential operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def signatureEvenGrading : HodgeEvenSections o →ₗ[ℝ] HodgeEvenSections o :=
  let f : HodgeEvenSections o →ₗ[ℝ] SmoothScalar (M := M) := LinearMap.fst ℝ _ _
  let a : HodgeEvenSections o →ₗ[ℝ] smoothTwoForms o :=
    (LinearMap.fst ℝ _ _).comp (LinearMap.snd ℝ _ _)
  let b : HodgeEvenSections o →ₗ[ℝ] SmoothScalar (M := M) :=
    (LinearMap.snd ℝ _ _).comp (LinearMap.snd ℝ _ _)
  (-b).prod (((smoothTwoFormHodge o).comp a).prod (-f))

def signatureOddGrading : HodgeOddSections M →ₗ[ℝ] HodgeOddSections M :=
  (-LinearMap.snd ℝ _ _).prod (-LinearMap.fst ℝ _ _)

theorem signatureEvenGrading_apply (f b : SmoothScalar (M := M)) (a : smoothTwoForms o) :
    signatureEvenGrading (f, a, b) = (-b, smoothTwoFormHodge o a, -f) := rfl

omit [IsManifold I4 ∞ M] in
theorem signatureOddGrading_apply (u v : smoothCovariantFields M 1) :
    signatureOddGrading (u, v) = (-v, -u) := rfl

theorem signatureEvenGrading_involutive : Function.Involutive (signatureEvenGrading (o := o)) := by
  rintro ⟨f, a, b⟩
  simp only [signatureEvenGrading_apply, neg_neg]
  rw [smoothTwoFormHodge_involutive o a]

omit [IsManifold I4 ∞ M] in
theorem signatureOddGrading_involutive : Function.Involutive (signatureOddGrading (M := M)) := by
  rintro ⟨u, v⟩
  simp only [signatureOddGrading_apply, neg_neg]

theorem smoothHodgeDiracEven_signature (x : HodgeEvenSections o) :
    smoothHodgeDiracEven (signatureEvenGrading x) =
      -signatureOddGrading (smoothHodgeDiracEven x) := by
  obtain ⟨f, a, b⟩ := x
  rw [signatureEvenGrading_apply, smoothHodgeDiracEven_apply,
    smoothHodgeDiracEven_apply, signatureOddGrading_apply]
  apply Prod.ext
  · change smoothScalarDifferentialLinear g (-b) +
        smoothTwoFormCodifferentialField (smoothTwoFormHodge o a) = _
    rw [map_neg]
    change -smoothScalarDifferential g b + smoothTwoFormCodifferentialField (smoothTwoFormHodge o a) =
      -(-(smoothTwoFormCodifferentialField (smoothTwoFormHodge o a) - smoothScalarDifferential g b))
    abel
  · rw [smoothTwoFormHodge_involutive]
    change smoothTwoFormCodifferentialField a - smoothScalarDifferentialLinear g (-f) = _
    rw [map_neg]
    change smoothTwoFormCodifferentialField a - -smoothScalarDifferential g f =
      -(-(smoothScalarDifferential g f + smoothTwoFormCodifferentialField a))
    abel

theorem smoothHodgeDiracOdd_signature (y : HodgeOddSections M) :
    smoothHodgeDiracOdd (o := o) (signatureOddGrading y) =
      -signatureEvenGrading (smoothHodgeDiracOdd (o := o) y) := by
  obtain ⟨u, v⟩ := y
  rw [signatureOddGrading_apply, smoothHodgeDiracOdd_apply,
    smoothHodgeDiracOdd_apply, signatureEvenGrading_apply]
  apply Prod.ext
  · change -smoothOneFormDivergence g (-v) = -(-smoothOneFormDivergence g v)
    rw [map_neg]
  · apply Prod.ext
    · change smoothOneFormExteriorLinear (-v) +
        smoothTwoFormHodge o (smoothOneFormExteriorLinear (-u)) = _
      rw [map_neg, map_neg, map_neg, map_add, smoothTwoFormHodge_involutive]
      change -smoothOneFormExterior v + -smoothTwoFormHodge o (smoothOneFormExterior u) =
        -(smoothTwoFormHodge o (smoothOneFormExterior u) + smoothOneFormExterior v)
      abel
    · change smoothOneFormDivergence g (-u) = -(-(-smoothOneFormDivergence g u))
      rw [map_neg, neg_neg]

abbrev HodgeSections (o : FrameOrientation g) := HodgeEvenSections o × HodgeOddSections M

def smoothHodgeDirac : HodgeSections o →ₗ[ℝ] HodgeSections o :=
  ((smoothHodgeDiracOdd (o := o)).comp (LinearMap.snd ℝ _ _)).prod
    ((smoothHodgeDiracEven (o := o)).comp (LinearMap.fst ℝ _ _))

def signatureGrading : HodgeSections o →ₗ[ℝ] HodgeSections o :=
  ((signatureEvenGrading (o := o)).comp (LinearMap.fst ℝ _ _)).prod
    ((signatureOddGrading (M := M)).comp (LinearMap.snd ℝ _ _))

theorem signatureGrading_involutive : Function.Involutive (signatureGrading (o := o)) := by
  intro x
  exact Prod.ext (signatureEvenGrading_involutive x.1) (signatureOddGrading_involutive x.2)

theorem smoothHodgeDirac_signature (x : HodgeSections o) :
    smoothHodgeDirac (signatureGrading x) = -signatureGrading (smoothHodgeDirac x) := by
  exact Prod.ext (smoothHodgeDiracOdd_signature x.2) (smoothHodgeDiracEven_signature x.1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong continuity, eigenmode evolution and decay of the actual
degree-one heat semigroup. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormHeat_eigenvector (t : ℝ≥0) (i : OneFormEigenIndex hRic d) :
    oneFormHeat hRic d t (oneFormEigenvector hRic d i) =
      oneFormHeatWeight hRic d t i • oneFormEigenvector hRic d i := by
  classical
  apply (oneFormSpectralEquiv hRic d).injective
  apply lp.ext
  funext j
  rw [oneFormHeat_coordinate, map_smul]
  have hbi : oneFormEigenbasis hRic d i = oneFormEigenvector hRic d i := by
    simp only [oneFormEigenbasis, HilbertBasis.coe_mk]
  have hb : oneFormSpectralEquiv hRic d (oneFormEigenvector hRic d i) = lp.single 2 i (1 : ℝ) := by
    change (oneFormEigenbasis hRic d).repr _ = _
    simpa only [hbi] using (oneFormEigenbasis hRic d).repr_self i
  rw [hb]
  by_cases h : j = i
  · subst j
    simp
  · simp [lp.single_apply, h]

theorem oneFormHeat_continuous (f : OneFormL2 o) :
    Continuous (fun t : ℝ≥0 => oneFormHeat hRic d t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply oneFormSpectralMultiplier_tendsto hRic d
    (oneFormHeatWeight hRic d) (oneFormHeatWeight hRic d t)
    (oneFormHeatWeight_bound hRic d) (oneFormHeatWeight_bound hRic d t)
  intro i
  have hc : Continuous (fun s : ℝ≥0 => oneFormHeatWeight hRic d s i) := by
    unfold oneFormHeatWeight
    fun_prop
  exact hc.tendsto t

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormHeatWeight_tendsto_zero (i : OneFormEigenIndex hRic d) :
    Tendsto (fun t : ℝ≥0 => oneFormHeatWeight hRic d t i) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hn := ht.atTop_mul_const_of_neg (neg_neg_of_pos (oneFormHeatRate_pos hRic d i))
  have he := Real.tendsto_exp_atBot.comp hn
  simpa only [Function.comp_def, oneFormHeatWeight, mul_neg, neg_mul] using he

theorem oneFormHeat_tendsto_zero (f : OneFormL2 o) :
    Tendsto (fun t : ℝ≥0 => oneFormHeat hRic d t f) atTop (𝓝 0) := by
  have hz : oneFormSpectralMultiplier hRic d (fun _ => 0) 1 zero_le_one
      (fun _ => by norm_num) f = 0 := by
    apply (oneFormSpectralEquiv hRic d).injective
    apply lp.ext
    funext i
    rw [oneFormSpectralMultiplier_coordinate, map_zero]
    simp
  have h := oneFormSpectralMultiplier_tendsto hRic d (oneFormHeatWeight hRic d) (fun _ => 0)
    (oneFormHeatWeight_bound hRic d) (fun _ => by norm_num)
    (oneFormHeatWeight_tendsto_zero hRic d) f
  simpa only [hz, oneFormHeat] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time summability of the actual one-form heat spectrum,
using the scalar spectrum and the finite coexact images of two-form eigenspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormCoexact_finrank_le (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) ≤
      Module.finrank ℝ (TwoFormSpectralSpace hRic μ) := by
  have h := LinearMap.finrank_range_le (oneFormCodiffEigenMap (o := o) hRic μ)
  exact h.trans_eq (twoFormSmoothEigenEquiv hRic μ).finrank_eq

def oneFormCoexactToTwoFormIndex (hRic : RicciThree g)
    (i : OneFormCoexactEigenIndex (o := o) hRic) : TwoFormEigenIndex (o := o) hRic :=
  ⟨i.1, Fin.castLE (oneFormCoexact_finrank_le hRic i.1) i.2⟩

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormCoexactToTwoFormIndex_injective (hRic : RicciThree g) :
    Function.Injective (oneFormCoexactToTwoFormIndex (o := o) hRic) := by
  rintro ⟨μ, i⟩ ⟨ν, j⟩ h
  have hμ : μ = ν := congrArg Sigma.fst h
  subst ν
  have hi : i.val = j.val := congrArg (fun k : TwoFormEigenIndex (o := o) hRic => k.2.val) h
  exact congrArg (Sigma.mk μ) (Fin.ext hi)

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

omit [PreconnectedSpace M] in
theorem oneFormHeat_weight_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (oneFormHeatWeight hRic d t) := by
  have h₀ := (scalarHeat_weight_summable g o d t ht).comp_injective
    (i := fun i : OneFormExactEigenIndex g o d => i.val) Subtype.val_injective
  have h₂ := (twoFormHeat_weight_summable (o := o) hRic t ht).comp_injective
    (i := oneFormCoexactToTwoFormIndex (o := o) hRic)
    (oneFormCoexactToTwoFormIndex_injective hRic)
  change Summable (fun i : OneFormExactEigenIndex g o d =>
    oneFormHeatWeight hRic d t (Sum.inl i)) at h₀
  change Summable (fun i : OneFormCoexactEigenIndex (o := o) hRic =>
    oneFormHeatWeight hRic d t (Sum.inr i)) at h₂
  exact Summable.sum _ h₀ h₂

def oneFormHeatTrace (t : ℝ≥0) : ℝ := ∑' i, oneFormHeatWeight hRic d t i

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormHeatTrace_nonneg (t : ℝ≥0) : 0 ≤ oneFormHeatTrace hRic d t :=
  tsum_nonneg fun _ => (Real.exp_pos _).le

end
end PositiveEinsteinFour.Geometry
end


section

/-! The diagonal trace of the actual heat kernel is the sum of squared
L2 norms of its six half-time frame columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Manifold _root_.Topology NNReal ENNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatFrameCoefficient_sq_summable (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l : Fin 6) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic =>
      twoFormHeatFrameCoefficient hRic t e l i ^ 2) := by
  have h := (twoFormHeatFrameCoefficient_mem (o := o) hRic t ht e l).summable
    (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using h

theorem twoFormHeatFrameColumn_norm_sq (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l : Fin 6) :
    ‖twoFormHeatFrameColumn (o := o) hRic t ht e l‖ ^ 2 =
      ∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatFrameCoefficient hRic t e l i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    ← (twoFormEigenbasis hRic).tsum_inner_mul_inner]
  apply tsum_congr
  intro i
  rw [twoFormEigenbasis_apply, real_inner_comm (twoFormHeatFrameColumn hRic t ht e l),
    twoFormHeatFrameColumn_eigen, pow_two]

theorem twoFormHeatKernel_trace_columns (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) :
    twoFormFiberTrace (twoFormHeatKernel (o := o) hRic (t + t) (add_pos ht ht) e.base e.base) =
      ∑ l : Fin 6, ‖twoFormHeatFrameColumn (o := o) hRic t ht e l‖ ^ 2 := by
  rw [twoFormHeatKernel_diagonal_trace]
  have htime : (t + t) / 2 = t := by ring
  simp_rw [htime, twoFormHeatFrameColumn_norm_sq]
  rw [← Summable.tsum_finsetSum (fun l (_ : l ∈ (Finset.univ : Finset (Fin 6))) =>
    twoFormHeatFrameCoefficient_sq_summable hRic t ht e l)]
  apply tsum_congr
  intro i
  rw [← twoFormFrameValue_norm o (twoFormHeatSection hRic t ht (twoFormEigenvector hRic i)).val e,
    EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro l _
  rw [twoFormHeatFrameCoefficient_eq hRic t ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar contractions of the spectral kernel are intrinsic measurable
functions, even though the reference-frame coordinates need not be measurable. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

def twoFormKernelPairingMap (a b : TwoFormFour) :
    (TwoFormFour →L[ℝ] TwoFormFour) →L[ℝ] ℝ :=
  (innerSL ℝ b).comp (ContinuousLinearMap.apply ℝ TwoFormFour a)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormKernelPairing_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def twoFormHeatKernelPairingTerm (hRic : RicciThree g) (t : ℝ≥0)
    (u v : smoothTwoForms o) (i : TwoFormEigenIndex (o := o) hRic) (z : M × M) : ℝ :=
  twoFormHeatWeight hRic t i.1 *
    inner ℝ ((twoFormEigenSection hRic i).val z.1) (v.val z.1) *
    inner ℝ ((twoFormEigenSection hRic i).val z.2) (u.val z.2)

theorem twoFormHeatKernel_pairing_hasSum (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (u v : smoothTwoForms o) (z : M × M) :
    HasSum (fun i => twoFormHeatKernelPairingTerm hRic t u v i z)
      (inner ℝ (v.val z.1) (twoFormHeatKernel (o := o) hRic t ht z.1 z.2 (u.val z.2))) := by
  have hs := (twoFormHeatKernel_eigen_hasSum (o := o) hRic t ht z.1 z.2).mapL
    (twoFormKernelPairingMap (u.val z.2) (v.val z.1))
  have he : (fun i : TwoFormEigenIndex (o := o) hRic =>
      twoFormKernelPairingMap (u.val z.2) (v.val z.1)
        (twoFormHeatWeight hRic t i.1 • InnerProductSpace.rankOne ℝ
          ((twoFormEigenSection hRic i).val z.1) ((twoFormEigenSection hRic i).val z.2))) =
      (fun i => twoFormHeatKernelPairingTerm hRic t u v i z) := by
    funext i
    simp only [twoFormKernelPairingMap, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, innerSL_apply_apply, smul_apply,
      InnerProductSpace.rankOne_apply, real_inner_smul_right, twoFormHeatKernelPairingTerm]
    rw [real_inner_comm (v.val z.1)]
    ring
  rw [he] at hs
  exact hs

theorem twoFormHeatKernelPairingTerm_integrable (hRic : RicciThree g) (t : ℝ≥0)
    (u v : smoothTwoForms o) (i : TwoFormEigenIndex (o := o) hRic) :
    Integrable (twoFormHeatKernelPairingTerm hRic t u v i)
      ((normalizedVolume g).prod (normalizedVolume g)) := by
  have h := ((smoothTwoForm_pairing_integrable (twoFormEigenSection hRic i) v).mul_prod
    (smoothTwoForm_pairing_integrable (twoFormEigenSection hRic i) u)).const_mul
      (twoFormHeatWeight hRic t i.1)
  change Integrable (fun z : M × M => twoFormHeatWeight hRic t i.1 *
    inner ℝ ((twoFormEigenSection hRic i).val z.1) (v.val z.1) *
    inner ℝ ((twoFormEigenSection hRic i).val z.2) (u.val z.2)) _
  simpa only [mul_assoc] using h

theorem twoFormHeatKernelPairingTerm_integral_norm (hRic : RicciThree g) (t : ℝ≥0)
    (u v : smoothTwoForms o) (i : TwoFormEigenIndex (o := o) hRic) :
    (∫ z, ‖twoFormHeatKernelPairingTerm hRic t u v i z‖
      ∂(normalizedVolume g).prod (normalizedVolume g)) =
      twoFormHeatWeight hRic t i.1 *
        (∫ x, ‖inner ℝ ((twoFormEigenSection hRic i).val x) (v.val x)‖ ∂normalizedVolume g) *
        (∫ y, ‖inner ℝ ((twoFormEigenSection hRic i).val y) (u.val y)‖ ∂normalizedVolume g) := by
  have hw : ‖twoFormHeatWeight hRic t i.1‖ = twoFormHeatWeight hRic t i.1 :=
    Real.norm_of_nonneg (Real.exp_pos _).le
  simp only [twoFormHeatKernelPairingTerm, norm_mul, hw]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  exact congrArg (twoFormHeatWeight hRic t i.1 * ·)
    (integral_prod_mul
      (fun x : M => ‖inner ℝ ((twoFormEigenSection hRic i).val x) (v.val x)‖)
      (fun y : M => ‖inner ℝ ((twoFormEigenSection hRic i).val y) (u.val y)‖))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual iterated two-point kernel integrals and convergence of their
Gaussian-dominated correction series. Spatial integration is in the
displacement from the source point, with the usual Euclidean volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set

noncomputable section

local notation "V" => TwoFormFour →L[ℝ] TwoFormFour

def fourHeatVolterraIterate (R : ℝ → FourSpace → FourSpace → V) :
    ℕ → ℝ → FourSpace → FourSpace → V
  | 0, t, x, y => R t x y
  | n + 1, t, x, y => ∫ s : ℝ in 0..t, ∫ z : FourSpace,
      (R (t - s) x (y + z)).comp (fourHeatVolterraIterate R n s (y + z) y)

theorem fourHeatVolterraIterate_bound (R : ℝ → FourSpace → FourSpace → V)
    (A : ℝ) (hA : 0 ≤ A)
    (hR : ∀ t, 0 < t → ∀ x y, ‖R t x y‖ ≤ A * fourHeatGaussian t (x - y))
    (n : ℕ) (t : ℝ) (ht : 0 < t) (x y : FourSpace) :
    ‖fourHeatVolterraIterate R n t x y‖ ≤
      (A ^ (n + 1) * t ^ n / (n.factorial : ℝ)) * fourHeatGaussian t (x - y) := by
  induction n generalizing t x y with
  | zero => simpa only [fourHeatVolterraIterate, zero_add, pow_one, pow_zero,
      mul_one, Nat.factorial_zero, Nat.cast_one, div_one] using hR t ht x y
  | succ n ih =>
    have hF (s : ℝ) (hs : s ∈ Ioo 0 t) (z : FourSpace) :
        ‖R (t - s) x (y + z)‖ ≤ A * fourHeatGaussian (t - s) ((x - y) - z) := by
      simpa only [sub_add_eq_sub_sub] using hR (t - s) (sub_pos.mpr hs.2) x (y + z)
    have hG (s : ℝ) (hs : s ∈ Ioo 0 t) (z : FourSpace) :
        ‖fourHeatVolterraIterate R n s (y + z) y‖ ≤
          (A ^ (n + 1) * s ^ n / (n.factorial : ℝ)) * fourHeatGaussian s z := by
      simpa only [add_sub_cancel_left] using ih s hs.1 (y + z) y
    have h := fourHeatVolterra_step_bound n A t hA ht (x - y)
      (fun s z => R (t - s) x (y + z))
      (fun s z => fourHeatVolterraIterate R n s (y + z) y) hF hG
    simpa only [fourHeatVolterraIterate, Nat.succ_eq_add_one, Nat.add_assoc] using h

theorem fourHeatVolterra_majorant_summable (A t : ℝ) (x : FourSpace) :
    Summable (fun n : ℕ => (A ^ (n + 1) * t ^ n / (n.factorial : ℝ)) *
      fourHeatGaussian t x) := by
  have h := (Real.summable_pow_div_factorial (A * t)).mul_left (A * fourHeatGaussian t x)
  apply h.congr
  intro n
  rw [mul_pow, pow_succ]
  ring

theorem fourHeatVolterraIterate_norm_summable (R : ℝ → FourSpace → FourSpace → V)
    (A : ℝ) (hA : 0 ≤ A)
    (hR : ∀ t, 0 < t → ∀ x y, ‖R t x y‖ ≤ A * fourHeatGaussian t (x - y))
    (t : ℝ) (ht : 0 < t) (x y : FourSpace) :
    Summable (fun n => ‖fourHeatVolterraIterate R n t x y‖) := by
  apply (fourHeatVolterra_majorant_summable A t (x - y)).of_norm_bounded
  intro n
  simpa only [norm_norm] using fourHeatVolterraIterate_bound R A hA hR n t ht x y

theorem fourHeatVolterraIterate_summable (R : ℝ → FourSpace → FourSpace → V)
    (A : ℝ) (hA : 0 ≤ A)
    (hR : ∀ t, 0 < t → ∀ x y, ‖R t x y‖ ≤ A * fourHeatGaussian t (x - y))
    (t : ℝ) (ht : 0 < t) (x y : FourSpace) :
    Summable (fun n => fourHeatVolterraIterate R n t x y) := by
  have := FiniteDimensional.complete ℝ V
  exact (fourHeatVolterraIterate_norm_summable R A hA hR t ht x y).of_norm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform fiber bounds give actual global one-form L2 bounds. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}
  {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatNormalOneAmplitudeL2_norm_le
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, ‖a x‖ ≤ B) :
    ‖heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs‖ ≤ B := by
  apply (oneFormFromContinuous_norm_le _).trans
  apply (ContinuousMap.norm_le _ hB).mpr
  intro f
  by_cases hf : f.base ∈ C.target
  · have heq := heatNormalOneAmplitude_norm_sq C hE hCt hP hD a ha hc hs f hf
    have hba := hb (C.symm f.base)
    nlinarith [norm_nonneg (a (C.symm f.base)),
      norm_nonneg (heatNormalOneAmplitude D C hCt hP hD a ha hc hs f)]
  · have hz : heatNormalOneAmplitude D C hCt hP hD a ha hc hs f = 0 := by
      change WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i]) = _
      simp only [heatNormalOneFrameLift, ite_eq_right hf]
      rfl
    rw [hz, norm_zero]
    exact hB

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global L2 amplitude has the expected scalar base integral against
every actual smooth test section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

local instance heatNormalOneAmplitudePairing_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem heatNormalOneAmplitudeL2_pairing_base (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : smoothCovariantFields M 1) :
    inner ℝ (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothOneFormL2Linear v) =
      ∫ y, heatNormalScalarLift C
        (fun x => inner ℝ (a x) (heatNormalOneValue c D.point
          v x)) y ∂normalizedVolume g := by
  let ψ := fun x => inner ℝ (a x) (heatNormalOneValue c D.point
    v x)
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have ha0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    simp only [ψ, ha0, inner_zero_left]
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := by
    intro x hx
    have hv : ContDiffAt ℝ 2 (heatNormalOneValue c D.point v) x := by
      apply (contDiffAt_piLp (p := 2)).mpr
      intro k
      exact heatNormalOneFormValue_regular 2 c D.point v x
        (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx)) k
    exact (ha.continuous.continuousAt.inner hv.continuousAt).continuousWithinAt
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hs)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [heatNormalOneAmplitudeL2_pairing]
  have hp (f : FrameBundle g) :
      inner ℝ (heatNormalOneAmplitude D C hCt hP hD a ha hc hs f)
        (smoothOneFormEuclideanValue (g := g) v f) =
      heatNormalScalarLift C ψ f.base :=
    heatNormalOneLift_pairing D C hE hCt hD a v f
  simp_rw [hp]
  rw [canonicalFrameMeasure_integral_base g o _ hLi]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A proved uniform Gaussian bound for the residual of the actual local
scalar parametrix. Its diagonal scaling is O(t) in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem fourHeatGaussian_le_diagonal (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    fourHeatGaussian t x ≤ fourHeatGaussian t 0 := by
  have hexp : Real.exp (-(4 * t)⁻¹ * ‖x‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have h : 0 ≤ (4 * t)⁻¹ * ‖x‖ ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    linarith)
  simpa only [fourHeatGaussian, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, Real.exp_zero, mul_one] using
    mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (sq_nonneg (4 * Real.pi * t)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalParametrix_residual_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ),
      |deriv (fun s => heatNormalParametrix g o e s x) t +
        fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
          (heatNormalParametrix g o e t) x| ≤ C * t ^ 3 * fourHeatGaussian t x := by
  let D := heatNormalExtension g o e
  let F := fun x => fourHeatLocalOperator (D.a x) (D.b x) 0 (heatNormalCoefficient g o e 3) x
  have hF : ContDiff ℝ 1 F := fourHeatLocalOperator_contDiff 1 D.a D.b (fun _ => 0) _
    (fun i j => (D.a_regular i j).of_le (by norm_num))
    (fun i => (D.b_regular i).of_le (by norm_num)) contDiff_const
    (heatNormalCoefficient_contDiff g o e 3 (by omega))
  obtain ⟨r₀, hr₀, hR⟩ := heatNormalParametrix_residual g o hRic e he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ ball 0 r₀ ∧
      D.a x = (heatNormalMetric g o e x)⁻¹ ∧ D.b x = heatNormalDrift g o e x := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) hr₀, D.a_near, D.b_near] with x hx ha hb
    exact ⟨hx, ha, hb⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : FourSpace) (r / 2)).bddAbove_image
    hF.continuous.abs.continuousOn
  refine ⟨r / 2, by positivity, max C 0, le_max_right _ _, ?_⟩
  intro x hx t ht
  have hxr : x ∈ ball (0 : FourSpace) r := ball_subset_ball (by linarith) hx
  have hxcl : x ∈ closedBall (0 : FourSpace) (r / 2) := ball_subset_closedBall hx
  obtain ⟨hx₀, ha, hb⟩ := hball hxr
  have hFx : |F x| ≤ max C 0 := (hC (mem_image_of_mem _ hxcl)).trans (le_max_left _ _)
  rw [hR x hx₀ t ht, abs_mul, abs_mul,
    abs_of_pos (fourHeatGaussian_pos t ht x), abs_of_pos (pow_pos ht 3)]
  have heq : F x = fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹
      (heatNormalDrift g o e x) 0 (heatNormalCoefficient g o e 3) x := by
    dsimp [F]
    rw [ha, hb]
  rw [← heq]
  calc
    _ ≤ (fourHeatGaussian t x * t ^ 3) * max C 0 :=
      mul_le_mul_of_nonneg_left hFx (mul_nonneg (fourHeatGaussian_pos t ht x).le
        (pow_nonneg ht.le 3))
    _ = _ := by ring

theorem heatNormalParametrix_residual_uniform_linear (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ),
      |deriv (fun s => heatNormalParametrix g o e s x) t +
        fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
          (heatNormalParametrix g o e t) x| ≤ C * t := by
  obtain ⟨r, hr, C, hC, hR⟩ := heatNormalParametrix_residual_bound g o hRic e he
  refine ⟨r, hr, C / (16 * Real.pi ^ 2), by positivity, ?_⟩
  intro x hx t ht
  calc
    _ ≤ C * t ^ 3 * fourHeatGaussian t x := hR x hx t ht
    _ ≤ C * t ^ 3 * fourHeatGaussian t 0 :=
      mul_le_mul_of_nonneg_left (fourHeatGaussian_le_diagonal t ht x)
        (mul_nonneg hC (pow_nonneg ht.le 3))
    _ = C * (t ^ (1 + 2) * fourHeatGaussian t 0) := by ring
    _ = _ := by rw [fourHeatGaussian_diagonal_power 1 t ht, pow_one]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact continuous one-form chart tensors are limits of actual
smooth one-form frame tensors in the uniform norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance heatOneChartApproxCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

omit [CompactSpace M] in
theorem heatOneChart_sub (c : M) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (F H : FourSpace → CovariantCoordinates 1)
    (hF : ContinuousOn F (chartAt FourSpace c).target)
    (hH : ContinuousOn H (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) (hHs : tsupport H ⊆ K)
    (hDs : tsupport (H - F) ⊆ K) :
    heatOneChart g c (H - F) (hH.sub hF)
      (hK.of_isClosed_subset (isClosed_tsupport _) hDs) (hDs.trans hKt) =
      heatOneChart g c H hH (hK.of_isClosed_subset (isClosed_tsupport _) hHs) (hHs.trans hKt) -
      heatOneChart g c F hF (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt) := by
  classical
  apply ContinuousMap.ext
  intro f
  apply WithLp.ofLp_injective 2
  funext i
  change heatNormalOneFrameLift g c (chartAt FourSpace c).symm (H - F) f ![i] =
    heatNormalOneFrameLift g c (chartAt FourSpace c).symm H f ![i] -
      heatNormalOneFrameLift g c (chartAt FourSpace c).symm F f ![i]
  by_cases hf : f.base ∈ (chartAt FourSpace c).symm.target
  · simp only [heatNormalOneFrameLift, ite_eq_left hf, Pi.sub_apply]
    exact frameTensor_sub _ _ _ ![i]
  · simp only [heatNormalOneFrameLift, ite_eq_right hf, Pi.zero_apply, sub_self]

theorem heatOneChart_smooth_approx (c : M)
    (F : FourSpace → CovariantCoordinates 1) (hF : Continuous F)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ u : smoothCovariantFields M 1,
      ‖smoothOneFormEuclideanValue (g := g) u - heatOneChart g c F hF.continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt)‖ < ε := by
  obtain ⟨B, hB, hbound⟩ := heatOneChart_bound (g := g) c hK hKt
  let r := ε / (B + 1)
  have hr : 0 < r := div_pos hε (by positivity)
  obtain ⟨H, hH, hdist, hHsF⟩ := hF.exists_contDiff_approx (⊤ : ℕ∞)
    (ε := fun _ => r) continuous_const (fun _ => hr)
  have hHs : tsupport H ⊆ K := (closure_mono hHsF).trans hFs
  have hDs : tsupport (H - F) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hzK
    have hH0 : H z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzK (hHs h))
    have hF0 : F z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hzK (hFs h))
    exact hz (by simp only [Pi.sub_apply, hH0, hF0, sub_self])
  refine ⟨oneFormChartTest g c H hH.contDiffOn hK hKt hHs, ?_⟩
  rw [← heatOneChart_smooth c H hH.contDiffOn hK hKt hHs,
    ← heatOneChart_sub c hK hKt F H hF.continuousOn hH.continuous.continuousOn hFs hHs hDs]
  have hb := hbound (H - F) (hH.continuous.continuousOn.sub hF.continuousOn) hDs r hr.le
    (fun z a => (norm_le_pi_norm (H z - F z) a).trans
      (by simpa only [dist_eq_norm] using (hdist z).le))
  have hbr : B * r < ε := by
    have h := (mul_div_cancel₀ ε (show B + 1 ≠ 0 by positivity))
    change (B + 1) * r = ε at h
    nlinarith
  exact hb.trans_lt hbr

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact grouping of the scalar, one-form and two-form heat traces
by the finite eigenspaces of the actual shifted resolvents. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarHeatSpectralTrace (t : ℝ≥0) : ℝ := ∑' i, scalarBaseHeatWeight g o d t i

def twoFormHeatSpectralTrace (t : ℝ≥0) : ℝ :=
  ∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1

def oneFormExactHeatTrace (t : ℝ≥0) : ℝ :=
  ∑' i : OneFormExactEigenIndex g o d, scalarBaseHeatWeight g o d t i.val

def oneFormCoexactHeatTrace (t : ℝ≥0) : ℝ :=
  ∑' i : OneFormCoexactEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1

omit [PreconnectedSpace M] in
theorem oneFormHeatTrace_split (t : ℝ≥0) (ht : 0 < t) :
    oneFormHeatTrace hRic d t = oneFormExactHeatTrace d t + oneFormCoexactHeatTrace (o := o) hRic t := by
  have h := oneFormHeat_weight_summable hRic d t ht
  exact (h.comp_injective (i := Sum.inl) Sum.inl_injective).tsum_sum
    (h.comp_injective (i := Sum.inr) Sum.inr_injective)

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem twoFormHeatTrace_grouped (t : ℝ≥0) (ht : 0 < t) :
    twoFormHeatSpectralTrace (o := o) hRic t = ∑' μ : TwoFormSpectralValue (o := o) hRic,
      twoFormHeatWeight hRic t μ * (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ) := by
  rw [twoFormHeatSpectralTrace, (twoFormHeat_weight_summable hRic t ht).tsum_sigma]
  apply tsum_congr
  intro μ
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormCoexactHeatTrace_grouped (t : ℝ≥0) (ht : 0 < t) :
    oneFormCoexactHeatTrace (o := o) hRic t = ∑' μ : TwoFormSpectralValue (o := o) hRic,
      twoFormHeatWeight hRic t μ * (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) : ℝ) := by
  have h := (twoFormHeat_weight_summable (o := o) hRic t ht).comp_injective
    (i := oneFormCoexactToTwoFormIndex (o := o) hRic) (oneFormCoexactToTwoFormIndex_injective hRic)
  change Summable (fun i : OneFormCoexactEigenIndex (o := o) hRic =>
    twoFormHeatWeight hRic t i.1) at h
  rw [oneFormCoexactHeatTrace, h.tsum_sigma]
  apply tsum_congr
  intro μ
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem twoForm_heat_multiplicity_term (t : ℝ≥0) (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormHeatWeight hRic t μ * (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ) =
      2 * (twoFormHeatWeight hRic t μ * (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) : ℝ)) +
        if μ.val = 1 then (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ) else 0 := by
  split_ifs with hμ
  · rw [ oneFormCoexact_harmonic_eq_bot hRic μ hμ, finrank_bot]
    have hw : twoFormHeatWeight hRic t μ = 1 := by simp [twoFormHeatWeight, twoFormHeatRate, hμ]
    rw [hw]
    ring
  · rw [ twoForm_nonzero_coexact_multiplicity hRic μ hμ]
    push_cast
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite kernels and their actual dimension difference for the
four-dimensional Hodge–Dirac maps. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev HodgeEvenKernel := (smoothHodgeDiracEven (o := o)).ker
abbrev HodgeOddKernel := (smoothHodgeDiracOdd (o := o)).ker

local instance hodgeEvenKernelAddGroup : AddCommGroup (HodgeEvenKernel (o := o)) :=
  Submodule.addCommGroup _

local instance hodgeOddKernelAddGroup : AddCommGroup (HodgeOddKernel (o := o)) :=
  Submodule.addCommGroup _

local instance hodgeIndexHarmonicAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

def harmonicToEvenKernel :
    (ℝ × smoothHarmonicTwoForms (o := o) × ℝ) →ₗ[ℝ] HodgeEvenKernel (o := o) where
  toFun z := ⟨(smoothScalarConst z.1, z.2.1.val, smoothScalarConst z.2.2), by
    change smoothHodgeDiracEven (o := o) _ = 0
    rw [smoothHodgeDiracEven_apply, smoothScalarDifferential_const,
      smoothScalarDifferential_const]
    have hc : smoothTwoFormCodifferentialField z.2.1.val = 0 :=
      (smoothTwoFormCodifferentialField_eq_zero_iff _).mpr z.2.1.property.2
    have hd := (smoothTwoForm_closed_iff_codifferential_hodge z.2.1.val).mp z.2.1.property.1
    simp only [hc, hd, zero_add, sub_zero, Prod.zero_eq_mk]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
theorem harmonicToEvenKernel_injective :
    Function.Injective (harmonicToEvenKernel (o := o)) := by
  intro u v huv
  apply Prod.ext
  · exact congrArg (fun w : HodgeEvenKernel (o := o) =>
      w.val.1.val (Classical.arbitrary M)) huv
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun w : HodgeEvenKernel (o := o) => w.val.2.1) huv)
    · exact congrArg (fun w : HodgeEvenKernel (o := o) =>
        w.val.2.2.val (Classical.arbitrary M)) huv

theorem hodgeOddKernel_subsingleton (hRic : RicciThree g) :
    Subsingleton (HodgeOddKernel (o := o)) := by
  have hz (u : HodgeOddKernel (o := o)) : u = 0 := by
    obtain ⟨h₁, h₂⟩ := smoothHodgeDiracOdd_kernel hRic u.val.1 u.val.2 u.property
    exact Subtype.ext (Prod.ext h₁ h₂)
  exact ⟨fun u v => (hz u).trans (hz v).symm⟩

theorem hodgeOddKernel_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (HodgeOddKernel (o := o)) = 0 := by
  let _ := hodgeOddKernel_subsingleton (o := o) hRic
  exact Module.finrank_zero_of_subsingleton

variable [PreconnectedSpace M]

theorem harmonicToEvenKernel_surjective (hRic : RicciThree g) :
    Function.Surjective (harmonicToEvenKernel (o := o)) := by
  intro u
  obtain ⟨⟨r, hr⟩, ha, ⟨s, hs⟩⟩ := smoothHodgeDiracEven_kernel hRic
    u.val.1 u.val.2.2 u.val.2.1 u.property
  refine ⟨(r, ⟨u.val.2.1, ha⟩, s), ?_⟩
  exact Subtype.ext (Prod.ext hr.symm (Prod.ext rfl hs.symm))

def harmonicEvenKernelEquiv (hRic : RicciThree g) :
    (ℝ × smoothHarmonicTwoForms (o := o) × ℝ) ≃ₗ[ℝ] HodgeEvenKernel (o := o) :=
  LinearEquiv.ofBijective harmonicToEvenKernel
    ⟨harmonicToEvenKernel_injective, harmonicToEvenKernel_surjective hRic⟩

theorem hodgeEvenKernel_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (HodgeEvenKernel (o := o)) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  exact FiniteDimensional.of_surjective harmonicToEvenKernel
    (harmonicToEvenKernel_surjective hRic)

theorem hodgeEvenKernel_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (HodgeEvenKernel (o := o)) =
      2 + Module.finrank ℝ (smoothHarmonicTwoForms (o := o)) := by
  let _ := smoothHarmonicTwoForms_finite (o := o) hRic
  rw [← (harmonicEvenKernelEquiv (o := o) hRic).finrank_eq]
  simp only [Module.finrank_prod, Module.finrank_self, Nat.one_add, Nat.add_one]
  omega

def hodgeDiracKernelDifference : ℤ :=
  (Module.finrank ℝ (HodgeEvenKernel (o := o)) : ℤ) -
    (Module.finrank ℝ (HodgeOddKernel (o := o)) : ℤ)

theorem hodgeDiracKernelDifference_hodge (hRic : RicciThree g) :
    hodgeDiracKernelDifference (o := o) = 2 +
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℤ) +
      (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℤ) := by
  rw [hodgeDiracKernelDifference, hodgeEvenKernel_finrank hRic, hodgeOddKernel_finrank hRic,
    ← twoFormDeRhamCohomology_finrank hRic, twoFormDeRhamCohomology_hodge_dimension hRic]
  push_cast
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual smooth solvability for the even Hodge Laplacian and
surjectivity of the parity-changing Hodge–Dirac operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothEvenHodgePoisson (hRic : RicciThree g)
    (f b : SmoothScalar (M := M)) (a : smoothTwoForms o)
    (hf : smoothScalarMean g o f = 0) (hb : smoothScalarMean g o b = 0)
    (ha : ∀ h ∈ smoothHarmonicTwoForms (o := o), smoothTwoFormL2Inner a h = 0) :
    ∃ x : HodgeEvenSections o, smoothHodgeDiracOdd (smoothHodgeDiracEven x) = (f, a, b) := by
  obtain ⟨F, hF⟩ := exists_smoothPositivePoisson o hRic f hf
  obtain ⟨B, hB⟩ := exists_smoothPositivePoisson o hRic b hb
  obtain ⟨A, hA⟩ := exists_smoothHodgePoisson_pointwise hRic a ha
  refine ⟨(F, A, B), ?_⟩
  rw [smoothHodgeDirac_square_even hRic, hA]
  exact Prod.ext hF (Prod.ext rfl hB)

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem smoothHodgeDiracOdd_injective (hRic : RicciThree g) :
    Function.Injective (smoothHodgeDiracOdd (o := o)) := by
  intro u v huv
  apply sub_eq_zero.mp
  have hz : smoothHodgeDiracOdd (o := o) (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  obtain ⟨h₁, h₂⟩ := smoothHodgeDiracOdd_kernel hRic (u - v).1 (u - v).2 hz
  exact Prod.ext h₁ h₂

theorem smoothHodgeDiracEven_surjective (hRic : RicciThree g) :
    Function.Surjective (smoothHodgeDiracEven (o := o)) := by
  rintro ⟨u, v⟩
  have hf : smoothScalarMean g o (-smoothOneFormDivergence g u) = 0 := by
    rw [map_neg]
    have h := oneFormDivergence_mean_zero (o := o) hRic u
    change smoothScalarMean g o (smoothOneFormDivergence g u) = 0 at h
    rw [h, neg_zero]
  have hb : smoothScalarMean g o (smoothOneFormDivergence g v) = 0 :=
    oneFormDivergence_mean_zero (o := o) hRic v
  have ha : ∀ h ∈ smoothHarmonicTwoForms (o := o),
      smoothTwoFormL2Inner
        (smoothOneFormExterior u + smoothTwoFormHodge o (smoothOneFormExterior v)) h = 0 := by
    intro h hh
    rw [smoothTwoFormL2Inner_add, smoothTwoFormL2Inner_hodge_left,
      smoothHarmonic_orthogonal_exact hRic u h hh,
      smoothHarmonic_orthogonal_exact hRic v _ (smoothHarmonicTwoForms_hodge hRic h hh), add_zero]
  obtain ⟨x, hx⟩ := exists_smoothEvenHodgePoisson hRic _ _ _ hf hb ha
  refine ⟨x, smoothHodgeDiracOdd_injective (o := o) hRic ?_⟩
  exact hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Definiteness and formal self-adjointness for the full smooth Hodge
operator, with the actual integral pairing on each degree. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothHodgePairing (x y : HodgeSections o) : ℝ :=
  smoothHodgeEvenPairing x.1 y.1 + smoothHodgeOddPairing (o := o) x.2 y.2

theorem smoothHodgeEvenPairing_comm (x y : HodgeEvenSections o) :
    smoothHodgeEvenPairing x y = smoothHodgeEvenPairing y x := by
  unfold smoothHodgeEvenPairing
  rw [smoothTwoFormL2Inner_comm]
  simp only [mul_comm]

theorem smoothHodgeOddPairing_comm (x y : HodgeOddSections M) :
    smoothHodgeOddPairing (o := o) x y = smoothHodgeOddPairing (o := o) y x := by
  unfold smoothHodgeOddPairing
  rw [smoothOneFormL2Pairing_comm x.1 y.1, smoothOneFormL2Pairing_comm x.2 y.2]

theorem smoothHodgePairing_comm (x y : HodgeSections o) :
    smoothHodgePairing x y = smoothHodgePairing y x := by
  rw [smoothHodgePairing, smoothHodgePairing, smoothHodgeEvenPairing_comm,
    smoothHodgeOddPairing_comm]

theorem smoothHodgePairing_definite (x : HodgeSections o)
    (hx : smoothHodgePairing x x = 0) : x = 0 := by
  let F := ∫ e, x.1.1.val e.base * x.1.1.val e.base ∂canonicalFrameMeasure g o
  let A := smoothTwoFormL2Inner x.1.2.1 x.1.2.1
  let B := ∫ e, x.1.2.2.val e.base * x.1.2.2.val e.base ∂canonicalFrameMeasure g o
  let U := smoothOneFormL2Pairing (o := o) x.2.1 x.2.1
  let V := smoothOneFormL2Pairing (o := o) x.2.2 x.2.2
  have hF : 0 ≤ F := integral_nonneg (fun _ => mul_self_nonneg _)
  have hA : 0 ≤ A := smoothTwoFormL2Inner_nonneg _
  have hB : 0 ≤ B := integral_nonneg (fun _ => mul_self_nonneg _)
  have hU : 0 ≤ U := smoothOneFormL2Pairing_nonneg _
  have hV : 0 ≤ V := smoothOneFormL2Pairing_nonneg _
  change F + A + B + (U + V) = 0 at hx
  have hF0 : F = 0 := by linarith only [hx, hA, hB, hU, hV, hF]
  have hA0 : A = 0 := by linarith only [hx, hA, hB, hU, hV, hF]
  have hB0 : B = 0 := by linarith only [hx, hA, hB, hU, hV, hF]
  have hU0 : U = 0 := by linarith only [hx, hA, hB, hU, hV, hF]
  have hV0 : V = 0 := by linarith only [hx, hA, hB, hU, hV, hF]
  have hf := smoothScalar_eq_zero_of_square_integral (o := o) x.1.1
    (show (∫ e, x.1.1.val e.base ^ 2 ∂canonicalFrameMeasure g o) = 0 by
      simpa only [pow_two] using hF0)
  have hb := smoothScalar_eq_zero_of_square_integral (o := o) x.1.2.2
    (show (∫ e, x.1.2.2.val e.base ^ 2 ∂canonicalFrameMeasure g o) = 0 by
      simpa only [pow_two] using hB0)
  exact Prod.ext (Prod.ext hf (Prod.ext (smoothTwoFormL2Inner_definite _ hA0) hb))
    (Prod.ext (smoothOneFormL2Pairing_definite _ hU0) (smoothOneFormL2Pairing_definite _ hV0))

theorem smoothHodgeDirac_selfAdjoint (hRic : RicciThree g) (x y : HodgeSections o) :
    smoothHodgePairing (smoothHodgeDirac x) y = smoothHodgePairing x (smoothHodgeDirac y) := by
  change smoothHodgeEvenPairing (smoothHodgeDiracOdd x.2) y.1 +
      smoothHodgeOddPairing (o := o) (smoothHodgeDiracEven x.1) y.2 =
    smoothHodgeEvenPairing x.1 (smoothHodgeDiracOdd y.2) +
      smoothHodgeOddPairing (o := o) x.2 (smoothHodgeDiracEven y.1)
  rw [smoothHodgeDirac_adjoint hRic, smoothHodgeEvenPairing_comm,
    ← smoothHodgeDirac_adjoint hRic, smoothHodgeOddPairing_comm]
  exact add_comm _ _

theorem smoothHodgePairing_zero_right (x : HodgeSections o) : smoothHodgePairing x 0 = 0 := by
  simp [smoothHodgePairing, smoothHodgeEvenPairing, smoothHodgeOddPairing,
    smoothTwoFormL2Inner, smoothOneFormL2Pairing, covariantFieldFramed_eq, frameTensor]

end
end PositiveEinsteinFour.Geometry
end


section

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter
open scoped Manifold ContDiff _root_.Topology NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem oneFormHeat_joint_continuous (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    Continuous (fun tf : ℝ≥0 × OneFormL2 o => oneFormHeat hRic d tf.1 tf.2) := by
  apply continuous_iff_continuousAt.mpr
  intro tf
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have htime := Metric.continuousAt_iff.mp
    ((oneFormHeat_continuous hRic d tf.2).continuousAt (x := tf.1))
    (ε / 2) (half_pos hε)
  obtain ⟨δ, hδ, htime⟩ := htime
  refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), ?_⟩
  intro sf hsf
  have hst : dist sf.1 tf.1 < δ := by
    calc
      dist sf.1 tf.1 ≤ dist sf tf := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ < δ := lt_of_lt_of_le hsf (min_le_left _ _)
  have hsu : dist sf.2 tf.2 < ε / 2 := by
    calc
      dist sf.2 tf.2 ≤ dist sf tf := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ < ε / 2 := lt_of_lt_of_le hsf (min_le_right _ _)
  calc
    dist (oneFormHeat hRic d sf.1 sf.2) (oneFormHeat hRic d tf.1 tf.2) ≤
        dist (oneFormHeat hRic d sf.1 sf.2) (oneFormHeat hRic d sf.1 tf.2) +
        dist (oneFormHeat hRic d sf.1 tf.2) (oneFormHeat hRic d tf.1 tf.2) := dist_triangle _ _ _
    _ ≤ dist sf.2 tf.2 + dist (oneFormHeat hRic d sf.1 tf.2) (oneFormHeat hRic d tf.1 tf.2) := by
      apply add_le_add_left
      rw [dist_eq_norm, ← map_sub, dist_eq_norm]
      exact oneFormHeat_contraction hRic d sf.1 (sf.2 - tf.2)
    _ < ε / 2 + ε / 2 := add_lt_add hsu (htime hst)
    _ = ε := add_halves ε

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual positive one-form heat spectrum stays away from zero.
Trace summability leaves only finitely many modes in a bounded interval. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology NNReal

noncomputable section

private theorem finite_positive_lower_bound {ι : Type*} (s : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ s, 0 < r i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ r i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨ε, hε, hεs⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    refine ⟨min ε (r i), lt_min hε (hr i (Finset.mem_insert_self i s)), ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hεs j hj)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormHeatRate_lower_bound :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i : OneFormEigenIndex hRic d, ε ≤ oneFormHeatRate hRic d i := by
  classical
  have hs := (oneFormHeat_weight_summable hRic d 1 zero_lt_one).tendsto_cofinite_zero
  have hev : ∀ᶠ i in cofinite, oneFormHeatWeight hRic d 1 i < Real.exp (-1) :=
    hs.eventually (gt_mem_nhds (Real.exp_pos (-1)))
  have hfinite : {i : OneFormEigenIndex hRic d | ¬oneFormHeatWeight hRic d 1 i < Real.exp (-1)}.Finite :=
    (mem_cofinite.mp hev)
  obtain ⟨ε, hε, hbound⟩ := finite_positive_lower_bound hfinite.toFinset
    (oneFormHeatRate hRic d) (fun i _ => oneFormHeatRate_pos hRic d i)
  refine ⟨min ε 1, lt_min hε zero_lt_one, fun i => ?_⟩
  by_cases hi : i ∈ hfinite.toFinset
  · exact (min_le_left _ _).trans (hbound i hi)
  · have hweight : oneFormHeatWeight hRic d 1 i < Real.exp (-1) := by
      simpa only [Finite.mem_toFinset, mem_ofPred_eq, not_not] using hi
    have hr : 1 < oneFormHeatRate hRic d i := by
      change Real.exp (-(1 : ℝ≥0) * oneFormHeatRate hRic d i) < Real.exp (-1) at hweight
      have he := Real.exp_lt_exp.mp hweight
      norm_num at he
      linarith
    exact (min_le_right _ _).trans hr.le

theorem oneFormHeatRate_inv_sqrt_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ i : OneFormEigenIndex hRic d,
      |(Real.sqrt (oneFormHeatRate hRic d i))⁻¹| ≤ C := by
  obtain ⟨ε, hε, hb⟩ := oneFormHeatRate_lower_bound hRic d
  refine ⟨(Real.sqrt ε)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hε), fun i => ?_⟩
  rw [abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (oneFormHeatRate_pos hRic d i)))]
  exact inv_anti₀ (Real.sqrt_pos.mpr hε) (Real.sqrt_le_sqrt (hb i))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual signature operator between the two chirality subspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def signaturePositiveSections : Submodule ℝ (HodgeSections o) :=
  Module.End.eigenspace (signatureGrading (o := o)) (1 : ℝ)

def signatureNegativeSections : Submodule ℝ (HodgeSections o) :=
  Module.End.eigenspace (signatureGrading (o := o)) (-1 : ℝ)

local instance signaturePositiveAddGroup : AddCommGroup (signaturePositiveSections (o := o)) :=
  Submodule.addCommGroup _

local instance signatureNegativeAddGroup : AddCommGroup (signatureNegativeSections (o := o)) :=
  Submodule.addCommGroup _

theorem signaturePositive_star (x : signaturePositiveSections (o := o)) :
    signatureGrading x.val = x.val := by
  simpa only [one_smul] using Module.End.mem_eigenspace_iff.mp x.property

theorem signatureNegative_star (x : signatureNegativeSections (o := o)) :
    signatureGrading x.val = -x.val := by
  simpa only [neg_one_smul] using Module.End.mem_eigenspace_iff.mp x.property

def signatureOperator : signaturePositiveSections (o := o) →ₗ[ℝ]
    signatureNegativeSections (o := o) where
  toFun x := ⟨smoothHodgeDirac x.val, by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [neg_one_smul]
    have h := smoothHodgeDirac_signature x.val
    rw [signaturePositive_star] at h
    calc
      signatureGrading (smoothHodgeDirac x.val) =
          -(-signatureGrading (smoothHodgeDirac x.val)) := by abel
      _ = -smoothHodgeDirac x.val := by rw [← h]⟩
  map_add' x y := Subtype.ext (map_add smoothHodgeDirac x.val y.val)
  map_smul' r x := Subtype.ext (map_smul smoothHodgeDirac r x.val)

def signatureOperatorOpposite : signatureNegativeSections (o := o) →ₗ[ℝ]
    signaturePositiveSections (o := o) where
  toFun x := ⟨smoothHodgeDirac x.val, by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [one_smul]
    have h := smoothHodgeDirac_signature x.val
    rw [signatureNegative_star, map_neg] at h
    exact (neg_inj.mp h).symm⟩
  map_add' x y := Subtype.ext (map_add smoothHodgeDirac x.val y.val)
  map_smul' r x := Subtype.ext (map_smul smoothHodgeDirac r x.val)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The spectral kernel represents the actual heat operator under the
intrinsic smooth-section pairing and the normalized volume measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance twoFormKernelAction_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem twoFormHeatKernelPairingTerm_integral_norm_summable
    (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (u v : smoothTwoForms o) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic =>
      ∫ z, ‖twoFormHeatKernelPairingTerm hRic t u v i z‖
        ∂(normalizedVolume g).prod (normalizedVolume g)) := by
  let C (w : smoothTwoForms o) := (1 + ‖smoothTwoFormToL2 (w : SmoothL2TwoForm o)‖ ^ 2) / 2
  have hC (w : smoothTwoForms o) : 0 ≤ C w := by
    dsimp [C]
    positivity
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) _
    ((twoFormHeat_weight_summable (o := o) hRic t ht).mul_right (C v * C u))
  intro i
  rw [twoFormHeatKernelPairingTerm_integral_norm]
  have hw : 0 ≤ twoFormHeatWeight hRic t i.1 := (Real.exp_pos _).le
  have hy : 0 ≤ ∫ x, ‖inner ℝ ((twoFormEigenSection hRic i).val x) (u.val x)‖
      ∂normalizedVolume g := integral_nonneg (fun _ => norm_nonneg _)
  calc
    _ ≤ (twoFormHeatWeight hRic t i.1 * C v) * C u :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (twoFormEigenSection_pairing_integral_norm_bound hRic i v) hw)
        (twoFormEigenSection_pairing_integral_norm_bound hRic i u) hy (mul_nonneg hw (hC v))
    _ = _ := mul_assoc _ _ _

theorem twoFormHeatKernel_pairing_integrable (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (u v : smoothTwoForms o) :
    Integrable (fun z : M × M => inner ℝ (v.val z.1)
      (twoFormHeatKernel (o := o) hRic t ht z.1 z.2 (u.val z.2)))
      ((normalizedVolume g).prod (normalizedVolume g)) := by
  have he : (fun z : M × M => inner ℝ (v.val z.1)
      (twoFormHeatKernel (o := o) hRic t ht z.1 z.2 (u.val z.2))) =
      (fun z => ∑' i, twoFormHeatKernelPairingTerm hRic t u v i z) :=
    funext fun z => (twoFormHeatKernel_pairing_hasSum hRic t ht u v z).tsum_eq.symm
  rw [he]
  exact scalar_integrable_series
    (fun i => twoFormHeatKernelPairingTerm_integrable hRic t u v i)
    (twoFormHeatKernelPairingTerm_integral_norm_summable hRic t ht u v)
    (fun _ => (twoFormHeatKernel_pairing_hasSum hRic t ht u v _).summable.hasSum)

theorem twoFormHeatKernelPairingTerm_integral (hRic : RicciThree g) (t : ℝ≥0)
    (u v : smoothTwoForms o) (i : TwoFormEigenIndex (o := o) hRic) :
    (∫ z, twoFormHeatKernelPairingTerm hRic t u v i z
      ∂(normalizedVolume g).prod (normalizedVolume g)) =
      twoFormHeatWeight hRic t i.1 *
        inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o)) (twoFormEigenvector hRic i) *
        inner ℝ (twoFormEigenvector hRic i) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) := by
  simp only [twoFormHeatKernelPairingTerm, mul_assoc]
  rw [integral_const_mul]
  have hp := integral_prod_mul (μ := normalizedVolume g) (ν := normalizedVolume g)
    (fun x : M => inner ℝ ((twoFormEigenSection hRic i).val x) (v.val x))
    (fun y : M => inner ℝ ((twoFormEigenSection hRic i).val y) (u.val y))
  rw [hp]
  have hu := smoothTwoFormToL2_inner (twoFormEigenSection hRic i : SmoothL2TwoForm o)
    (u : SmoothL2TwoForm o)
  have hv := smoothTwoFormToL2_inner (twoFormEigenSection hRic i : SmoothL2TwoForm o)
    (v : SmoothL2TwoForm o)
  rw [twoFormEigenSection_L2] at hu hv
  rw [← hu, ← hv]
  have hc := real_inner_comm (twoFormEigenvector hRic i)
    (smoothTwoFormToL2 (u : SmoothL2TwoForm o))
  rw [hc]
  ring

theorem twoFormHeatKernel_pairing_integral (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (u v : smoothTwoForms o) :
    (∫ z : M × M, inner ℝ (v.val z.1)
      (twoFormHeatKernel (o := o) hRic t ht z.1 z.2 (u.val z.2))
      ∂(normalizedVolume g).prod (normalizedVolume g)) =
      inner ℝ (twoFormHeat hRic t (smoothTwoFormToL2 (u : SmoothL2TwoForm o)))
        (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) := by
  have he : (fun z : M × M => inner ℝ (v.val z.1)
      (twoFormHeatKernel (o := o) hRic t ht z.1 z.2 (u.val z.2))) =
      (fun z => ∑' i, twoFormHeatKernelPairingTerm hRic t u v i z) :=
    funext fun z => (twoFormHeatKernel_pairing_hasSum hRic t ht u v z).tsum_eq.symm
  rw [he, ← integral_tsum_of_summable_integral_norm
    (fun i => twoFormHeatKernelPairingTerm_integrable hRic t u v i)
    (twoFormHeatKernelPairingTerm_integral_norm_summable hRic t ht u v)]
  simp_rw [twoFormHeatKernelPairingTerm_integral]
  exact (twoFormHeat_pairing_tsum hRic t _ _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real-time notation for the spectral columns and diagonal trace, with
the zero extension used only to express limits through positive time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatRealColumn (hRic : RicciThree g) (t : ℝ) (e : FrameBundle g)
    (l : Fin 6) : TwoFormL2 o :=
  if ht : 0 < t then twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht) e l else 0

theorem twoFormHeatRealColumn_pos (hRic : RicciThree g) (t : ℝ) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 6) :
    twoFormHeatRealColumn (o := o) hRic t e l =
      twoFormHeatFrameColumn hRic t.toNNReal (Real.toNNReal_pos.mpr ht) e l :=
  dite_eq_left ht

def twoFormHeatRealTrace (hRic : RicciThree g) (t : ℝ) (x : M) : ℝ :=
  if ht : 0 < t then
    twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t.toNNReal (Real.toNNReal_pos.mpr ht) x x)
  else 0

theorem twoFormHeatRealTrace_columns (hRic : RicciThree g) (t : ℝ) (ht : 0 < t)
    (e : FrameBundle g) :
    twoFormHeatRealTrace (o := o) hRic (t + t) e.base =
      ∑ l : Fin 6, ‖twoFormHeatRealColumn (o := o) hRic t e l‖ ^ 2 := by
  simpa only [twoFormHeatRealTrace, dite_eq_left (add_pos ht ht), twoFormHeatRealColumn,
    dite_eq_left ht, Real.toNNReal_add ht.le ht.le] using
    twoFormHeatKernel_trace_columns hRic t.toNNReal (Real.toNNReal_pos.mpr ht) e

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform remainder bound for every entry of the constructed bundle
parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalBundleParametrix_residual_bound {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ), ∀ k l : Fin 6,
      |deriv (fun s => heatNormalBundleParametrix E s x k l) t +
        fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
          (fun y q => heatNormalBundleParametrix E t y q l) x k| ≤
      C * t ^ 3 * fourHeatGaussian t x := by
  let F := fun (x : FourSpace) (k l : Fin 6) =>
    fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
      (fun y q => E.amplitude 3 y q l) x k
  have hF (k l : Fin 6) : ContDiff ℝ 1 (fun x => F x k l) := by
    exact fourHeatBundleOperator_contDiff 1 E.base.a E.base.b E.B E.C _
      (fun i j => (E.base.a_regular i j).of_le (by norm_num))
      (fun i => (E.base.b_regular i).of_le (by norm_num))
      (fun i k l => (E.B_regular i k l).of_le (by norm_num))
      (fun k l => (E.C_regular k l).of_le (by norm_num))
      (fun q => (E.amplitude_regular 3 (by omega) q l).of_le (by norm_num)) k
  let S := fun x => ∑ k : Fin 6, ∑ l : Fin 6, |F x k l|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    continuous_finsetSum _ (fun l _ => (hF k l).continuous.abs))
  have hle (x : FourSpace) (k l : Fin 6) : |F x k l| ≤ S x := by
    apply (Finset.single_le_sum (fun q _ => abs_nonneg (F x k q)) (Finset.mem_univ l)).trans
    exact Finset.single_le_sum (fun p _ => Finset.sum_nonneg (fun q _ => abs_nonneg (F x p q)))
      (Finset.mem_univ k)
  obtain ⟨r₀, hr₀, hR⟩ := heatNormalBundleParametrix_residual E hRic he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ ball 0 r₀ ∧
      E.base.a x = (heatNormalMetric g o e x)⁻¹ ∧ E.base.b x = heatNormalDrift g o e x ∧
      E.B x = heatNormalBundleFirst D x ∧ E.C x = heatNormalBundleZero D x := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) hr₀, E.base.a_near, E.base.b_near,
      E.B_near, E.C_near] with x hx ha hb hB hC
    exact ⟨hx, ha, hb, hB, hC⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : FourSpace) (r / 2)).bddAbove_image hS.continuousOn
  refine ⟨r / 2, by positivity, max C 0, le_max_right _ _, ?_⟩
  intro x hx t ht k l
  have hxr : x ∈ ball (0 : FourSpace) r := ball_subset_ball (by linarith) hx
  have hxcl : x ∈ closedBall (0 : FourSpace) (r / 2) := ball_subset_closedBall hx
  obtain ⟨hx₀, ha, hb, hB, hC'⟩ := hball hxr
  have hFx : |F x k l| ≤ max C 0 :=
    (hle x k l).trans ((hC (mem_image_of_mem _ hxcl)).trans (le_max_left _ _))
  rw [hR x hx₀ t ht k l, abs_mul, abs_mul,
    abs_of_pos (fourHeatGaussian_pos t ht x), abs_of_pos (pow_pos ht 3)]
  have heq : F x k l = fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹
      (heatNormalDrift g o e x) (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
      (fun y q => E.amplitude 3 y q l) x k := by
    dsimp only [F]
    rw [ha, hb, hB, hC']
  rw [← heq]
  calc
    _ ≤ (fourHeatGaussian t x * t ^ 3) * max C 0 :=
      mul_le_mul_of_nonneg_left hFx (mul_nonneg (fourHeatGaussian_pos t ht x).le
        (pow_nonneg ht.le 3))
    _ = _ := by ring

theorem heatNormalBundleParametrix_residual_uniform_linear {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ), ∀ k l : Fin 6,
      |deriv (fun s => heatNormalBundleParametrix E s x k l) t +
        fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
          (fun y q => heatNormalBundleParametrix E t y q l) x k| ≤ C * t := by
  obtain ⟨r, hr, C, hC, hR⟩ := heatNormalBundleParametrix_residual_bound E hRic he
  refine ⟨r, hr, C / (16 * Real.pi ^ 2), by positivity, ?_⟩
  intro x hx t ht k l
  calc
    _ ≤ C * t ^ 3 * fourHeatGaussian t x := hR x hx t ht k l
    _ ≤ C * t ^ 3 * fourHeatGaussian t 0 :=
      mul_le_mul_of_nonneg_left (fourHeatGaussian_le_diagonal t ht x)
        (mul_nonneg hC (pow_nonneg ht.le 3))
    _ = C * (t ^ (1 + 2) * fourHeatGaussian t 0) := by ring
    _ = _ := by rw [fourHeatGaussian_diagonal_power 1 t ht, pow_one]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact normal-coordinate pairings of the actual global L2 amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem heatNormalOneAmplitudeL2_pairing_normal (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : smoothCovariantFields M 1) :
    inner ℝ (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothOneFormL2Linear v) =
      (normalizedChartFactor g).toReal * ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (a x) (heatNormalOneValue c D.point
          v x) := by
  rw [heatNormalOneAmplitudeL2_pairing_base D C hE]
  apply heatNormalScalarLift_integral D C hE hCt hP hD
  apply subset_trans (closure_mono ?_) hs
  intro x hx
  contrapose! hx
  apply Function.notMem_support.mpr
  rw [Function.notMem_support.mp hx, inner_zero_left]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform remainder bound for every entry of the constructed bundle
parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneParametrix_residual_bound {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ), ∀ k l : Fin 4,
      |deriv (fun s => heatNormalOneParametrix E s x k l) t +
        fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalOneFirst D x) (heatNormalOneZero D x)
          (fun y q => heatNormalOneParametrix E t y q l) x k| ≤
      C * t ^ 3 * fourHeatGaussian t x := by
  let F := fun (x : FourSpace) (k l : Fin 4) =>
    fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
      (fun y q => E.amplitude 3 y q l) x k
  have hF (k l : Fin 4) : ContDiff ℝ 1 (fun x => F x k l) := by
    exact fourHeatOneOperator_contDiff 1 E.base.a E.base.b E.B E.C _
      (fun i j => (E.base.a_regular i j).of_le (by norm_num))
      (fun i => (E.base.b_regular i).of_le (by norm_num))
      (fun i k l => (E.B_regular i k l).of_le (by norm_num))
      (fun k l => (E.C_regular k l).of_le (by norm_num))
      (fun q => (E.amplitude_regular 3 (by omega) q l).of_le (by norm_num)) k
  let S := fun x => ∑ k : Fin 4, ∑ l : Fin 4, |F x k l|
  have hS : Continuous S := continuous_finsetSum _ (fun k _ =>
    continuous_finsetSum _ (fun l _ => (hF k l).continuous.abs))
  have hle (x : FourSpace) (k l : Fin 4) : |F x k l| ≤ S x := by
    apply (Finset.single_le_sum (fun q _ => abs_nonneg (F x k q)) (Finset.mem_univ l)).trans
    exact Finset.single_le_sum (fun p _ => Finset.sum_nonneg (fun q _ => abs_nonneg (F x p q)))
      (Finset.mem_univ k)
  obtain ⟨r₀, hr₀, hR⟩ := heatNormalOneParametrix_residual E hRic he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ ball 0 r₀ ∧
      E.base.a x = (heatNormalMetric g o e x)⁻¹ ∧ E.base.b x = heatNormalDrift g o e x ∧
      E.B x = heatNormalOneFirst D x ∧ E.C x = heatNormalOneZero D x := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) hr₀, E.base.a_near, E.base.b_near,
      E.B_near, E.C_near] with x hx ha hb hB hC
    exact ⟨hx, ha, hb, hB, hC⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : FourSpace) (r / 2)).bddAbove_image hS.continuousOn
  refine ⟨r / 2, by positivity, max C 0, le_max_right _ _, ?_⟩
  intro x hx t ht k l
  have hxr : x ∈ ball (0 : FourSpace) r := ball_subset_ball (by linarith) hx
  have hxcl : x ∈ closedBall (0 : FourSpace) (r / 2) := ball_subset_closedBall hx
  obtain ⟨hx₀, ha, hb, hB, hC'⟩ := hball hxr
  have hFx : |F x k l| ≤ max C 0 :=
    (hle x k l).trans ((hC (mem_image_of_mem _ hxcl)).trans (le_max_left _ _))
  rw [hR x hx₀ t ht k l, abs_mul, abs_mul,
    abs_of_pos (fourHeatGaussian_pos t ht x), abs_of_pos (pow_pos ht 3)]
  have heq : F x k l = fourHeatOneOperator (heatNormalMetric g o e x)⁻¹
      (heatNormalDrift g o e x) (heatNormalOneFirst D x) (heatNormalOneZero D x)
      (fun y q => E.amplitude 3 y q l) x k := by
    dsimp only [F]
    rw [ha, hb, hB, hC']
  rw [← heq]
  calc
    _ ≤ (fourHeatGaussian t x * t ^ 3) * max C 0 :=
      mul_le_mul_of_nonneg_left hFx (mul_nonneg (fourHeatGaussian_pos t ht x).le
        (pow_nonneg ht.le 3))
    _ = _ := by ring

theorem heatNormalOneParametrix_residual_uniform_linear {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ), ∀ k l : Fin 4,
      |deriv (fun s => heatNormalOneParametrix E s x k l) t +
        fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalOneFirst D x) (heatNormalOneZero D x)
          (fun y q => heatNormalOneParametrix E t y q l) x k| ≤ C * t := by
  obtain ⟨r, hr, C, hC, hR⟩ := heatNormalOneParametrix_residual_bound E hRic he
  refine ⟨r, hr, C / (16 * Real.pi ^ 2), by positivity, ?_⟩
  intro x hx t ht k l
  calc
    _ ≤ C * t ^ 3 * fourHeatGaussian t x := hR x hx t ht k l
    _ ≤ C * t ^ 3 * fourHeatGaussian t 0 :=
      mul_le_mul_of_nonneg_left (fourHeatGaussian_le_diagonal t ht x)
        (mul_nonneg hC (pow_nonneg ht.le 3))
    _ = C * (t ^ (1 + 2) * fourHeatGaussian t 0) := by ring
    _ = _ := by rw [fourHeatGaussian_diagonal_power 1 t ht, pow_one]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact continuous chart one-forms lie in the actual one-form L2 completion. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}
local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatOneChart_L2_realization (c : M)
    (F : FourSpace → CovariantCoordinates 1) (hF : Continuous F)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) :
    oneFormFrameL2 (oneFormFromContinuous (o := o)
      (heatOneChart g c F hF.continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt))) =
    ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ
      (heatOneChart g c F hF.continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt)) := by
  let A := (oneFormFrameL2 (o := o)).comp (oneFormFromContinuous (o := o))
  let B := ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (E := FourSpace)
  have hclosed : IsClosed {T | A T = B T} := isClosed_eq A.continuous B.continuous
  apply hclosed.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨u, hu⟩ := heatOneChart_smooth_approx (g := g) c F hF hK hKt hFs ε hε
  refine ⟨smoothOneFormEuclideanValue (g := g) u, ?_, ?_⟩
  · change oneFormFrameL2 (oneFormFromContinuous (smoothOneFormEuclideanValue (g := g) u)) = _
    rw [oneFormFromContinuous_smooth, oneFormFrameL2_smooth]
  · simpa only [dist_eq_norm, norm_sub_rev] using hu

theorem heatOneChart_L2_norm (c : M)
    (F : FourSpace → CovariantCoordinates 1) (hF : Continuous F)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hFs : tsupport F ⊆ K) :
    ‖oneFormFromContinuous (o := o)
      (heatOneChart g c F hF.continuousOn
        (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt))‖ ^ 2 =
    ∫ f, ‖heatOneChart g c F hF.continuousOn
      (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt) f‖ ^ 2
        ∂canonicalFrameMeasure g o := by
  rw [← oneFormFrameL2_norm, heatOneChart_L2_realization c F hF hK hKt hFs,
    ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
    (heatOneChart g c F hF.continuousOn
      (hK.of_isClosed_subset (isClosed_tsupport _) hFs) (hFs.trans hKt))] with f hf
  rw [hf, real_inner_self_eq_norm_sq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! One O(t) cutoff-residual constant works for every actual normal frame
in a compact coordinate neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformCutoffResidual (E : HeatFamilySmoothCoefficients) (r : ℝ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (hχb : ∀ x, |χ x| ≤ 1)
    (s : ℝ) (hs : 0 < s) (hinner : ∀ x ∈ ball 0 s, χ x = 1)
    (hRic : RicciThree g) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonNormalMember g o c E r e),
      frameCoordinateState g c e ∈ K → e ∈ o.positive →
      ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
        |deriv (fun v => heatNormalCutoffParametrix N.extension χ v x k l) t +
          fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
            (N.extension.B x) (N.extension.C x)
            (fun y q => heatNormalCutoffParametrix N.extension χ t y q l) x k| ≤ B * t := by
  obtain ⟨C₀, hC₀, hb⟩ := E.lastCoefficient_compact_bound (tsupport χ ×ˢ K) (hc.prod hK)
  obtain ⟨C₁, hC₁, hcom⟩ := heatFamilyCommutator_gaussian_bound E χ hχ hc K hK s hs hinner
  let B₀ := C₀ / (16 * Real.pi ^ 2)
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  refine ⟨B₀ + C₁, add_nonneg hB₀ hC₁, ?_⟩
  intro e N hq he t ht x k l
  let A := N.extension
  let q := frameCoordinateState g c e
  let u : Fin 4 → FourSpace → Fin 6 → ℝ := fun m y a => A.amplitude m y a l
  have hu (m : Fin 4) (a : Fin 6) : ContDiff ℝ 2 (fun y => u m y a) :=
    (A.amplitude_regular m (by omega) a l).of_le (by norm_num)
  by_cases hx : x ∈ tsupport χ
  · have hxr := hχs hx
    have hsym (i j : Fin 4) : A.base.a x i j = A.base.a x j i := by
      rw [(N.actual x hxr).1]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    let Q := deriv (fun v => heatNormalBundleParametrix A v x k l) t +
      fourHeatBundleOperator (A.base.a x) (A.base.b x) (A.B x) (A.C x)
        (fun y a => heatNormalBundleParametrix A t y a l) x k
    have hQ : |Q| ≤ B₀ * t := by
      have hres := N.parametrix_residual hRic he x hxr t ht.1 k l
      change Q = fourHeatGaussian t x * t ^ 3 * E.lastCoefficient (x, q) k l at hres
      rw [hres, abs_mul, abs_mul, abs_of_pos (fourHeatGaussian_pos t ht.1 x),
        abs_of_pos (pow_pos ht.1 3)]
      calc
        _ ≤ (fourHeatGaussian t x * t ^ 3) * C₀ :=
          mul_le_mul_of_nonneg_left (hb (x, q) ⟨hx, hq⟩ k l)
            (mul_nonneg (fourHeatGaussian_pos t ht.1 x).le (pow_nonneg ht.1.le 3))
        _ ≤ (fourHeatGaussian t 0 * t ^ 3) * C₀ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (fourHeatGaussian_le_diagonal t ht.1 x)
              (pow_nonneg ht.1.le 3)) hC₀
        _ = C₀ * (t ^ (1 + 2) * fourHeatGaussian t 0) := by ring
        _ = B₀ * t := by rw [fourHeatGaussian_diagonal_power 1 t ht.1, pow_one]; dsimp [B₀]; ring
    have hid := heatNormalCutoffParametrix_residual_identity A χ t ht.1 x hχ.contDiffAt
      (A.base.a x) (A.base.b x) (A.B x) (A.C x) hsym k l
    have hscaled := fourHeatScaledCommutator_identity A.base.a A.base.b A.B χ u hu t ht.1 x k
    have hfamily : fourHeatScaledCommutator A.base.a A.base.b A.B χ u t x k =
        heatFamilyCommutator E χ t (x, q) k l := by
      have hu' : u = fun (m : Fin 4) y a => E.amplitude m (y, q) a l := by
        funext m y a
        exact congrArg (fun f : FourSpace → HeatMat6 => f y a l)
          (N.amplitude_family m (by omega))
      rw [hu']
      change fourHeatScaledCommutator N.extension.base.a N.extension.base.b N.extension.B χ _ t x k = _
      rw [N.a_family, N.b_family, N.B_family]
      rfl
    have hid' : deriv (fun v => heatNormalCutoffParametrix A χ v x k l) t +
        fourHeatBundleOperator (A.base.a x) (A.base.b x) (A.B x) (A.C x)
          (fun y a => heatNormalCutoffParametrix A χ t y a l) x k =
        χ x * Q + (fourHeatGaussian t x / t) * heatFamilyCommutator E χ t (x, q) k l := by
      rw [← hfamily, ← hscaled, hid]
      dsimp only [Q, heatNormalBundleParametrix, u]
      ring
    change |deriv (fun v => heatNormalCutoffParametrix A χ v x k l) t + _| ≤ _
    rw [hid']
    calc
      _ ≤ |χ x * Q| + |(fourHeatGaussian t x / t) * heatFamilyCommutator E χ t (x, q) k l| :=
        abs_add_le _ _
      _ ≤ B₀ * t + C₁ * t := by
        apply add_le_add _ (hcom q hq t ht x k l)
        rw [abs_mul]
        exact (mul_le_mul (hχb x) hQ (abs_nonneg Q) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by ring
  · rw [heatNormalCutoffParametrix_residual_zero N.extension χ t x hx, abs_zero]
    exact mul_nonneg (add_nonneg hB₀ hC₁) ht.1.le

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite kernel and cokernel of the actual smooth even Hodge–Dirac
map, and its algebraic index. The heat-kernel index formula is not assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem hodgeDiracEven_cokernel_subsingleton (hRic : RicciThree g) :
    Subsingleton (HodgeOddSections M ⧸ LinearMap.range (smoothHodgeDiracEven (o := o))) := by
  rw [LinearMap.range_eq_top.mpr (smoothHodgeDiracEven_surjective (o := o) hRic)]
  infer_instance

theorem hodgeDiracEven_finite_kernel_cokernel (hRic : RicciThree g) :
    FiniteDimensional ℝ (HodgeEvenKernel (o := o)) ∧
      FiniteDimensional ℝ (HodgeOddSections M ⧸ LinearMap.range (smoothHodgeDiracEven (o := o))) := by
  refine ⟨hodgeEvenKernel_finite hRic, ?_⟩
  rw [LinearMap.range_eq_top.mpr (smoothHodgeDiracEven_surjective (o := o) hRic)]
  exact FiniteDimensional.of_surjective (0 : ℝ →ₗ[ℝ]
    HodgeOddSections M ⧸ (⊤ : Submodule ℝ (HodgeOddSections M)))
    (fun x => ⟨0, Subsingleton.elim _ _⟩)

theorem smoothHodgeDiracEven_index (hRic : RicciThree g) :
    (smoothHodgeDiracEven (o := o)).index = 2 +
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℤ) +
      (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℤ) := by
  rw [LinearMap.index_of_surjective (smoothHodgeDiracEven_surjective (o := o) hRic)]
  change (Module.finrank ℝ (HodgeEvenKernel (o := o)) : ℤ) = _
  rw [hodgeEvenKernel_finrank hRic, ← twoFormDeRhamCohomology_finrank hRic,
    twoFormDeRhamCohomology_hodge_dimension hRic]
  push_cast
  ring

theorem smoothHodgeDiracEven_index_eq_euler (hRic : RicciThree g) :
    (smoothHodgeDiracEven (o := o)).index = hodgeComplexEuler g o := by
  rw [smoothHodgeDiracEven_index hRic, hodgeComplexEuler_hodge hRic]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every actual smooth full form is harmonic plus a Hodge–Dirac image. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem exists_smoothHodge_full_decomposition (hRic : RicciThree g)
    (y : HodgeSections o) :
    ∃ k : HodgeSections o, smoothHodgeDirac k = 0 ∧
      ∃ x : HodgeSections o, y = k + smoothHodgeDirac x := by
  obtain ⟨H, hH, hperp⟩ := exists_smoothHarmonic_projection hRic y.1.2.1
  let r := smoothScalarMean g o y.1.1
  let s := smoothScalarMean g o y.1.2.2
  let f := y.1.1 - smoothScalarConst r
  let b := y.1.2.2 - smoothScalarConst s
  have hf : smoothScalarMean g o f = 0 := by
    change smoothScalarMean g o (y.1.1 - smoothScalarConst r) = 0
    rw [map_sub, smoothScalarMean_const]
    exact sub_self _
  have hb : smoothScalarMean g o b = 0 := by
    change smoothScalarMean g o (y.1.2.2 - smoothScalarConst s) = 0
    rw [map_sub, smoothScalarMean_const]
    exact sub_self _
  obtain ⟨P, hP⟩ := exists_smoothEvenHodgePoisson hRic f b (y.1.2.1 - H) hf hb hperp
  obtain ⟨Q, hQ⟩ := smoothHodgeDiracEven_surjective (o := o) hRic y.2
  let k : HodgeSections o := ((smoothScalarConst r, H, smoothScalarConst s), 0)
  let x : HodgeSections o := (Q, smoothHodgeDiracEven P)
  have hk : smoothHodgeDirac k = 0 := by
    apply Prod.ext
    · change smoothHodgeDiracOdd (o := o) (0 : HodgeOddSections M) = 0
      exact map_zero _
    · exact (harmonicToEvenKernel (o := o) (r, ⟨H, hH⟩, s)).property
  refine ⟨k, hk, x, ?_⟩
  change y = ((smoothScalarConst r, H, smoothScalarConst s), 0) +
    (smoothHodgeDiracOdd (smoothHodgeDiracEven P), smoothHodgeDiracEven Q)
  rw [hP, hQ]
  apply Prod.ext
  · apply Prod.ext
    · change y.1.1 = smoothScalarConst r + (y.1.1 - smoothScalarConst r)
      abel
    · apply Prod.ext
      · change y.1.2.1 = H + (y.1.2.1 - H)
        abel
      · change y.1.2.2 = smoothScalarConst s + (y.1.2.2 - smoothScalarConst s)
        abel
  · change y.2 = 0 + y.2
    exact (zero_add _).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Bochner heat convolution, its eigenmode pairing and its
quadratic norm bound for a linearly vanishing residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M] {g : SmoothMetric M} {o : FrameOrientation g}

def oneFormHeatConvolution (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o)) (R : ℝ → OneFormL2 o) (t : ℝ) : OneFormL2 o :=
  ∫ s in (0 : ℝ)..t, oneFormHeat hRic d (t - s).toNNReal (R s)

theorem oneFormHeatConvolution_integrable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (R : ℝ → OneFormL2 o) (t : ℝ) (ht : 0 ≤ t) (hR : ContinuousOn R (Icc 0 t)) :
    IntervalIntegrable (fun s => oneFormHeat hRic d (t - s).toNNReal (R s)) volume 0 t := by
  have htime : Continuous (fun s : ℝ => (t - s).toNNReal) :=
    continuous_real_toNNReal.comp (continuous_const.sub continuous_id)
  exact ((oneFormHeat_joint_continuous hRic d).comp_continuousOn
    (htime.continuousOn.prodMk hR)).intervalIntegrable_of_Icc ht

theorem oneFormHeatConvolution_norm_le (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (R : ℝ → OneFormL2 o) (t : ℝ) (ht : 0 ≤ t) (B : ℝ)
    (hR : ∀ s ∈ Icc 0 t, ‖R s‖ ≤ B * s) :
    ‖oneFormHeatConvolution hRic d R t‖ ≤ B * t ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun s : ℝ => B * s) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, B * s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht _ hi
      exact Filter.Eventually.of_forall fun s hs =>
        (oneFormHeat_contraction hRic d (t - s).toNNReal (R s)).trans
          (hR s ⟨hs.1.le, hs.2⟩)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id]; ring

theorem oneFormHeatConvolution_eigen (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (R : ℝ → OneFormL2 o) (t : ℝ) (ht : 0 ≤ t) (hR : ContinuousOn R (Icc 0 t))
    (i : OneFormEigenIndex hRic d) :
    inner ℝ (oneFormHeatConvolution hRic d R t) (oneFormEigenvector hRic d i) =
      ∫ s in (0 : ℝ)..t, Real.exp (-oneFormHeatRate hRic d i * (t - s)) *
        inner ℝ (R s) (oneFormEigenvector hRic d i) := by
  have hi := oneFormHeatConvolution_integrable hRic d R t ht hR
  have hp := (innerSL ℝ (oneFormEigenvector hRic d i)).intervalIntegral_comp_comm hi
  change (∫ s in (0 : ℝ)..t,
    inner ℝ (oneFormEigenvector hRic d i) (oneFormHeat hRic d (t - s).toNNReal (R s))) =
      inner ℝ (oneFormEigenvector hRic d i) (oneFormHeatConvolution hRic d R t) at hp
  rw [real_inner_comm, ← hp]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht] using hs
  change inner ℝ (oneFormEigenvector hRic d i) (oneFormHeat hRic d (t - s).toNNReal (R s)) =
    Real.exp (-oneFormHeatRate hRic d i * (t - s)) * inner ℝ (R s) (oneFormEigenvector hRic d i)
  rw [real_inner_comm, oneFormHeat_selfAdjoint, oneFormHeat_eigenvector, real_inner_smul_right]
  unfold oneFormHeatWeight
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs'.2)]
  ring_nf

end
end PositiveEinsteinFour.Geometry
end


section

/-! A bounded inverse square root on the strictly positive degree-one spectrum. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormInverseSquareRoot : OneFormL2 o →L[ℝ] OneFormL2 o :=
  oneFormSpectralMultiplier hRic d (fun i => (Real.sqrt (oneFormHeatRate hRic d i))⁻¹)
    (oneFormHeatRate_inv_sqrt_bound hRic d).choose
    (oneFormHeatRate_inv_sqrt_bound hRic d).choose_spec.1.le
    (oneFormHeatRate_inv_sqrt_bound hRic d).choose_spec.2

theorem oneFormInverseSquareRoot_eigen (i : OneFormEigenIndex hRic d) :
    oneFormInverseSquareRoot hRic d (oneFormEigenvector hRic d i) =
      (Real.sqrt (oneFormHeatRate hRic d i))⁻¹ • oneFormEigenvector hRic d i := by
  classical
  apply (oneFormSpectralEquiv hRic d).injective
  apply lp.ext
  funext j
  rw [oneFormInverseSquareRoot, oneFormSpectralMultiplier_coordinate, map_smul]
  have hbi : oneFormEigenbasis hRic d i = oneFormEigenvector hRic d i := by
    simp only [oneFormEigenbasis, HilbertBasis.coe_mk]
  have hb : oneFormSpectralEquiv hRic d (oneFormEigenvector hRic d i) = lp.single 2 i (1 : ℝ) := by
    change (oneFormEigenbasis hRic d).repr _ = _
    simpa only [hbi] using (oneFormEigenbasis hRic d).repr_self i
  rw [hb]
  by_cases h : j = i
  · subst j
    simp
  · simp [lp.single_apply, h]

def oneFormScalarPotential : OneFormL2 o →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (oneFormExactSpectralLift d).comp (oneFormInverseSquareRoot hRic d)

def oneFormTwoFormPotential : OneFormL2 o →L[ℝ] TwoFormL2 o :=
  (oneFormCoexactSpectralLift hRic).comp (oneFormInverseSquareRoot hRic d)

theorem oneFormScalarPotential_exact (i : OneFormExactEigenIndex g o d) :
    oneFormScalarPotential hRic d (oneFormExactEigenvector g o d i) =
      (Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ • scalarBaseEigenvector g o d i.val := by
  have h := oneFormInverseSquareRoot_eigen hRic d (Sum.inl i)
  change oneFormInverseSquareRoot hRic d (oneFormExactEigenvector g o d i) =
    (Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ • oneFormExactEigenvector g o d i at h
  change oneFormExactSpectralLift d (oneFormInverseSquareRoot hRic d _) = _
  rw [h, map_smul, oneFormExactSpectralLift_eigen]

theorem oneFormScalarPotential_coexact (i : OneFormCoexactEigenIndex (o := o) hRic) :
    oneFormScalarPotential hRic d (oneFormCoexactEigenvector hRic i) = 0 := by
  have h := oneFormInverseSquareRoot_eigen hRic d (Sum.inr i)
  change oneFormInverseSquareRoot hRic d (oneFormCoexactEigenvector hRic i) =
    (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ • oneFormCoexactEigenvector hRic i at h
  change oneFormExactSpectralLift d (oneFormInverseSquareRoot hRic d _) = _
  rw [h, map_smul, oneFormExactSpectralLift_coexact, smul_zero]

theorem oneFormTwoFormPotential_coexact (i : OneFormCoexactEigenIndex (o := o) hRic) :
    oneFormTwoFormPotential hRic d (oneFormCoexactEigenvector hRic i) =
      (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ • oneFormCoexactLiftL2 hRic i := by
  have h := oneFormInverseSquareRoot_eigen hRic d (Sum.inr i)
  change oneFormInverseSquareRoot hRic d (oneFormCoexactEigenvector hRic i) =
    (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ • oneFormCoexactEigenvector hRic i at h
  change oneFormCoexactSpectralLift hRic (oneFormInverseSquareRoot hRic d _) = _
  rw [h, map_smul, oneFormCoexactSpectralLift_eigen]

theorem oneFormTwoFormPotential_exact (i : OneFormExactEigenIndex g o d) :
    oneFormTwoFormPotential hRic d (oneFormExactEigenvector g o d i) = 0 := by
  have h := oneFormInverseSquareRoot_eigen hRic d (Sum.inl i)
  change oneFormInverseSquareRoot hRic d (oneFormExactEigenvector g o d i) =
    (Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ • oneFormExactEigenvector g o d i at h
  change oneFormCoexactSpectralLift hRic (oneFormInverseSquareRoot hRic d _) = _
  rw [h, map_smul, oneFormCoexactSpectralLift_exact, smul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual kernel elements of the two signature operators consist of
one constant scalar and the corresponding harmonic Hodge summand. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

abbrev SignaturePositiveKernel := (signatureOperator (o := o)).ker
abbrev SignatureNegativeKernel := (signatureOperatorOpposite (o := o)).ker

theorem signaturePositiveKernel_data (hRic : RicciThree g)
    (x : SignaturePositiveKernel (o := o)) :
    x.val.val.2 = 0 ∧
      x.val.val.1.2.1 ∈ smoothHarmonicTwoForms ∧
      smoothTwoFormHodge o x.val.val.1.2.1 = x.val.val.1.2.1 ∧
      x.val.val.1.2.2 = -x.val.val.1.1 ∧
      ∃ r : ℝ, x.val.val.1.1 = smoothScalarConst r := by
  have hd := congrArg Subtype.val x.property
  change smoothHodgeDirac x.val.val = 0 at hd
  have he := congrArg Prod.snd hd
  change smoothHodgeDiracEven x.val.val.1 = 0 at he
  obtain ⟨hf, ha, _⟩ := smoothHodgeDiracEven_kernel hRic
    x.val.val.1.1 x.val.val.1.2.2 x.val.val.1.2.1 he
  have ho := congrArg Prod.fst hd
  change smoothHodgeDiracOdd x.val.val.2 = 0 at ho
  obtain ⟨hu, hv⟩ := smoothHodgeDiracOdd_kernel hRic
    x.val.val.2.1 x.val.val.2.2 ho
  have hg := signaturePositive_star x.val
  have hstar := congrArg (fun z : HodgeSections o => z.1.2.1) hg
  have hb := congrArg (fun z : HodgeSections o => z.1.2.2) hg
  exact ⟨Prod.ext hu hv, ha, hstar, hb.symm, hf⟩

theorem signatureNegativeKernel_data (hRic : RicciThree g)
    (x : SignatureNegativeKernel (o := o)) :
    x.val.val.2 = 0 ∧
      x.val.val.1.2.1 ∈ smoothHarmonicTwoForms ∧
      smoothTwoFormHodge o x.val.val.1.2.1 = -x.val.val.1.2.1 ∧
      x.val.val.1.2.2 = x.val.val.1.1 ∧
      ∃ r : ℝ, x.val.val.1.1 = smoothScalarConst r := by
  have hd := congrArg Subtype.val x.property
  change smoothHodgeDirac x.val.val = 0 at hd
  have he := congrArg Prod.snd hd
  change smoothHodgeDiracEven x.val.val.1 = 0 at he
  obtain ⟨hf, ha, _⟩ := smoothHodgeDiracEven_kernel hRic
    x.val.val.1.1 x.val.val.1.2.2 x.val.val.1.2.1 he
  have ho := congrArg Prod.fst hd
  change smoothHodgeDiracOdd x.val.val.2 = 0 at ho
  obtain ⟨hu, hv⟩ := smoothHodgeDiracOdd_kernel hRic
    x.val.val.2.1 x.val.val.2.2 ho
  have hg := signatureNegative_star x.val
  have hstar := congrArg (fun z : HodgeSections o => z.1.2.1) hg
  have hb := congrArg (fun z : HodgeSections o => z.1.2.2) hg
  change -x.val.val.1.1 = -x.val.val.1.2.2 at hb
  exact ⟨Prod.ext hu hv, ha, hstar, (neg_inj.mp hb).symm, hf⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two chirality projections and their actual Dirac intertwining. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance signatureProjectionPositiveAddGroup : AddCommGroup (signaturePositiveSections (o := o)) :=
  Submodule.addCommGroup _
local instance signatureProjectionNegativeAddGroup : AddCommGroup (signatureNegativeSections (o := o)) :=
  Submodule.addCommGroup _

def signaturePlusMap : HodgeSections o →ₗ[ℝ] signaturePositiveSections (o := o) :=
  ((2 : ℝ)⁻¹ • (LinearMap.id + signatureGrading (o := o))).codRestrict _ (by
    intro x
    apply Module.End.mem_eigenspace_iff.mpr
    change signatureGrading ((2 : ℝ)⁻¹ • (x + signatureGrading x)) =
      (1 : ℝ) • ((2 : ℝ)⁻¹ • (x + signatureGrading x))
    rw [map_smul, map_add, signatureGrading_involutive, one_smul, add_comm])

def signatureMinusMap : HodgeSections o →ₗ[ℝ] signatureNegativeSections (o := o) :=
  ((2 : ℝ)⁻¹ • (LinearMap.id - signatureGrading (o := o))).codRestrict _ (by
    intro x
    apply Module.End.mem_eigenspace_iff.mpr
    change signatureGrading ((2 : ℝ)⁻¹ • (x - signatureGrading x)) =
      (-1 : ℝ) • ((2 : ℝ)⁻¹ • (x - signatureGrading x))
    rw [map_smul, map_sub, signatureGrading_involutive]
    module)

theorem signaturePlusMap_self (x : signaturePositiveSections (o := o)) :
    signaturePlusMap x.val = x := by
  apply Subtype.ext
  change (2 : ℝ)⁻¹ • (x.val + signatureGrading x.val) = x.val
  rw [signaturePositive_star]
  module

theorem signatureMinusMap_self (x : signatureNegativeSections (o := o)) :
    signatureMinusMap x.val = x := by
  apply Subtype.ext
  change (2 : ℝ)⁻¹ • (x.val - signatureGrading x.val) = x.val
  rw [signatureNegative_star]
  module

theorem signaturePlusMap_dirac (x : HodgeSections o) :
    signatureOperator (signaturePlusMap x) = signatureMinusMap (smoothHodgeDirac x) := by
  apply Subtype.ext
  change smoothHodgeDirac ((2 : ℝ)⁻¹ • (x + signatureGrading x)) =
    (2 : ℝ)⁻¹ • (smoothHodgeDirac x - signatureGrading (smoothHodgeDirac x))
  rw [map_smul, map_add, smoothHodgeDirac_signature]
  rfl

theorem signatureMinusMap_dirac (x : HodgeSections o) :
    signatureOperatorOpposite (signatureMinusMap x) = signaturePlusMap (smoothHodgeDirac x) := by
  apply Subtype.ext
  change smoothHodgeDirac ((2 : ℝ)⁻¹ • (x - signatureGrading x)) =
    (2 : ℝ)⁻¹ • (smoothHodgeDirac x + signatureGrading (smoothHodgeDirac x))
  rw [map_smul, map_sub, smoothHodgeDirac_signature]
  module

end
end PositiveEinsteinFour.Geometry
end


section

/-! Counting a fixed eigenvalue in the actual finite eigenspace indexing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

theorem tsum_eigenvalue_finrank {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Module.End ℝ V) :
    (∑' μ : A.Eigenvalues,
      if μ.val = 1 then (Module.finrank ℝ (A.eigenspace μ.val) : ℝ) else 0) =
        (Module.finrank ℝ (A.eigenspace 1) : ℝ) := by
  classical
  by_cases h : A.HasEigenvalue 1
  · let μ : A.Eigenvalues := ⟨1, h⟩
    rw [tsum_eq_single μ]
    · simp only [μ, Module.End.Eigenvalues.val_mk, ↓reduceIte]
      rfl
    · intro ν hν
      have hn : ν.val ≠ 1 := fun he => hν (Subtype.ext he)
      simp only [hn, ↓reduceIte]
  · have hz : A.eigenspace 1 = ⊥ := not_ne_iff.mp h
    have he : ∀ μ : A.Eigenvalues, μ.val ≠ 1 := by
      intro μ hm
      apply μ.property
      change A.eigenspace μ.val = ⊥
      rw [hm]
      exact hz
    simp only [he, ↓reduceIte, tsum_zero]
    change 0 = (Module.finrank ℝ (A.eigenspace 1) : ℝ)
    rw [hz, finrank_bot, Nat.cast_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarHeat_zero_weight_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : ScalarBaseEigenIndex g o d => if i.1.val = 1 then (1 : ℝ) else 0) := by
  classical
  apply Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity) _
    (scalarHeat_weight_summable g o d t ht)
  intro i
  split_ifs with hi
  · simp only [scalarBaseHeatWeight, scalarBaseHeatRate, hi, inv_one, sub_self,
      mul_zero, Real.exp_zero, le_refl]
  · exact (Real.exp_pos _).le

theorem scalarHeat_zero_weight_sum (t : ℝ≥0) (ht : 0 < t) :
    (∑' i : ScalarBaseEigenIndex g o d, if i.1.val = 1 then (1 : ℝ) else 0) =
      (Module.finrank ℝ (Module.End.eigenspace (scalarBaseResolvent g o d).toLinearMap 1) : ℝ) := by
  classical
  rw [(scalarHeat_zero_weight_summable d t ht).tsum_sigma]
  convert tsum_eigenvalue_finrank (scalarBaseResolvent g o d).toLinearMap using 1
  apply tsum_congr
  intro μ
  rw [tsum_fintype]
  split_ifs <;> simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic Hodge-signed diagonal trace of the actual heat kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

def twoFormFiberSignedTrace : (TwoFormFour →L[ℝ] TwoFormFour) →L[ℝ] ℝ :=
  twoFormFiberTrace.comp ((ContinuousLinearMap.compL ℝ TwoFormFour TwoFormFour TwoFormFour)
    twoFormHodge.toLinearIsometry.toContinuousLinearMap)

theorem twoFormFiberSignedTrace_rankOne (a b : TwoFormFour) :
    twoFormFiberSignedTrace (InnerProductSpace.rankOne ℝ a b) = inner ℝ b (twoFormHodge a) := by
  have he : twoFormHodge.toLinearIsometry.toContinuousLinearMap.comp
      (InnerProductSpace.rankOne ℝ a b) = InnerProductSpace.rankOne ℝ (twoFormHodge a) b := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply, map_smul]
    rfl
  change twoFormFiberTrace (twoFormHodge.toLinearIsometry.toContinuousLinearMap.comp _) = _
  rw [he, twoFormFiberTrace_apply, InnerProductSpace.trace_rankOne]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatKernel_signed_diagonal (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (x : M) :
    twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic t ht x x) =
      ∑' i : TwoFormEigenIndex (o := o) hRic,
        inner ℝ ((twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x)
          (twoFormHodge ((twoFormHeatSection hRic (t / 2) (half_pos ht)
            (twoFormEigenvector hRic i)).val x)) := by
  have hs := (twoFormHeatKernel_hasSum (o := o) hRic t ht x x).mapL twoFormFiberSignedTrace
  simpa only [twoFormHeatKernelTerm, twoFormFiberSignedTrace_rankOne] using hs.tsum_eq.symm

theorem smoothTwoForm_hodge_pairing_integral (u : smoothTwoForms o) :
    (∫ x, inner ℝ (u.val x) (twoFormHodge (u.val x)) ∂normalizedVolume g) =
      inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o))
        (twoFormL2Hodge (smoothTwoFormToL2 (u : SmoothL2TwoForm o))) := by
  calc
    _ = inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o))
        (smoothTwoFormToL2 (smoothL2Hodge (u : SmoothL2TwoForm o))) :=
      (smoothTwoFormToL2_inner (u : SmoothL2TwoForm o)
        (smoothL2Hodge (u : SmoothL2TwoForm o))).symm
    _ = _ := congrArg (fun a : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o)) a)
        (twoFormL2Hodge_smooth (u : SmoothL2TwoForm o)).symm

theorem twoFormHeatSection_signed_integral (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (i : TwoFormEigenIndex (o := o) hRic) :
    (∫ x, inner ℝ ((twoFormHeatSection hRic (t / 2) (half_pos ht)
        (twoFormEigenvector hRic i)).val x)
      (twoFormHodge ((twoFormHeatSection hRic (t / 2) (half_pos ht)
        (twoFormEigenvector hRic i)).val x)) ∂normalizedVolume g) =
      twoFormHeatWeight hRic t i.1 *
        inner ℝ (twoFormEigenvector hRic i) (twoFormL2Hodge (twoFormEigenvector hRic i)) := by
  rw [smoothTwoForm_hodge_pairing_integral, twoFormHeatSection_L2, twoFormHeat_eigenvector,
    map_smul, real_inner_smul_left, real_inner_smul_right]
  rw [← mul_assoc, ← pow_two, twoFormHeatWeight_half_sq]

theorem twoFormHeatKernel_signed_integral (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic t ht x x)
      ∂normalizedVolume g) =
      ∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1 *
        inner ℝ (twoFormEigenvector hRic i) (twoFormL2Hodge (twoFormEigenvector hRic i)) := by
  have := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let w := fun i : TwoFormEigenIndex (o := o) hRic =>
    twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)
  let F := fun i x => inner ℝ ((w i).val x) (twoFormHodge ((w i).val x))
  have hFi (i) : Integrable (F i) (normalizedVolume g) :=
    smoothTwoForm_pairing_integrable (w i) (smoothTwoFormHodge o (w i))
  have hbound (i) : (∫ x, ‖F i x‖ ∂normalizedVolume g) ≤ twoFormHeatWeight hRic t i.1 := by
    calc
      _ ≤ ∫ x, ‖(w i).val x‖ ^ 2 ∂normalizedVolume g := by
        apply integral_mono (hFi i).norm
          (((smoothTwoForm_norm_continuous (w i)).pow 2).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
        intro x
        change ‖inner ℝ ((w i).val x) (twoFormHodge ((w i).val x))‖ ≤ ‖(w i).val x‖ ^ 2
        exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans_eq (by rw [twoFormHodge.norm_map, pow_two])
      _ = _ := (twoFormHeatSection_eigen_integral hRic (t / 2) (half_pos ht) i).trans
        (twoFormHeatWeight_half_sq hRic t i.1)
  have hFs := Summable.of_nonneg_of_le (fun i => integral_nonneg (fun x => norm_nonneg (F i x)))
    hbound (twoFormHeat_weight_summable (o := o) hRic t ht)
  simp_rw [twoFormHeatKernel_signed_diagonal]
  change (∫ x, ∑' i, F i x ∂normalizedVolume g) = _
  rw [← integral_tsum_of_summable_integral_norm hFi hFs]
  exact tsum_congr (fun i => twoFormHeatSection_signed_integral hRic t ht i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A fixed bump and one residual constant for all actual normal
parametrices near an initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatActualUniformResidual (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ∃ E : HeatFamilySmoothCoefficients, ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∃ B ≥ (0 : ℝ), ∀ e' ∈ U,
        ∃ N : HeatCommonNormalMember g o e.base E r e',
          e' ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
            |deriv (fun v => heatNormalCutoffParametrix N.extension
                (heatNormalChartBump r hr) v x k l) t +
              fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
                (N.extension.B x) (N.extension.C x)
                (fun y q => heatNormalCutoffParametrix N.extension
                  (heatNormalChartBump r hr) t y q l) x k| ≤ B * t := by
  obtain ⟨E, r, hr, U, hU, heU, hN, _⟩ := exists_heatUniformNormalFamily g o e
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  have hχb (x : FourSpace) : |χ x| ≤ 1 := by
    rw [abs_of_nonneg (heatNormalChartBump r hr).nonneg]
    exact (heatNormalChartBump r hr).le_one
  have hinner (x : FourSpace) (hx : x ∈ ball 0 (r / 4)) : χ x = 1 :=
    (heatNormalChartBump r hr).one_of_mem_closedBall (ball_subset_closedBall hx)
  obtain ⟨B, hB, hb⟩ := heatUniformCutoffResidual E r
    (closedBall (frameCoordinateState g e.base e) (r / 2)) (isCompact_closedBall _ _)
    χ (heatNormalChartBump r hr).contDiff (heatNormalChartBump r hr).hasCompactSupport
    hχs hχb (r / 4) (by positivity) hinner hRic
  refine ⟨E, r, hr, U, hU, heU, B, hB, ?_⟩
  intro e' he'
  obtain ⟨hq, ⟨N⟩⟩ := hN e' he'
  exact ⟨N, hb e' N (ball_subset_closedBall hq)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact coordinate changes for continuous one-tensors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatCompactOneLift (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 1) (z : FourSpace) : CovariantCoordinates 1 := by
  classical
  exact if z ∈ C.target then T (C.symm z) else 0

theorem heatCompactOneLift_support (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 1) :
    support (heatCompactOneLift C T) ⊆ C '' tsupport T := by
  classical
  intro z hz
  by_cases h : z ∈ C.target
  · refine ⟨C.symm z, subset_closure ?_, C.right_inv h⟩
    simpa only [heatCompactOneLift, ite_eq_left h, mem_support] using hz
  · exact False.elim (hz (by simp only [heatCompactOneLift, ite_eq_right h]))

theorem heatCompactOneLift_tsupport (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 1) (hc : HasCompactSupport T)
    (hs : tsupport T ⊆ C.source) :
    tsupport (heatCompactOneLift C T) ⊆ C '' tsupport T :=
  closure_minimal (heatCompactOneLift_support C T)
    (hc.image_of_continuousOn (C.continuousOn.mono hs)).isClosed

theorem heatCompactOneLift_continuous (C : OpenPartialHomeomorph FourSpace FourSpace)
    (T : FourSpace → CovariantCoordinates 1) (hT : ContinuousOn T C.source)
    (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source) :
    Continuous (heatCompactOneLift C T) := by
  classical
  have hK := hc.image_of_continuousOn (C.continuousOn.mono hs)
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ C.target
  · have h := (hT.continuousAt (C.open_source.mem_nhds (C.map_target hz))).comp
      (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds hz))
    apply h.congr_of_eventuallyEq
    filter_upwards [C.open_target.mem_nhds hz] with w hw
    exact ite_eq_left hw
  · have hzK : z ∉ C '' tsupport T := by
      rintro ⟨x, hx, rfl⟩
      exact hz (C.map_source (hs hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 1))).congr_of_eventuallyEq
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
    exact not_ne_iff.mp (fun hn => hw (heatCompactOneLift_support C T hn))


end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported actual normal parametrix whose full residual
is uniformly O(t), including the annulus where the cutoff varies. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalCutoffParametrix_bound_of_support {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ R > (0 : ℝ), ∀ (χ : FourSpace → ℝ), ContDiff ℝ 2 χ → HasCompactSupport χ →
      tsupport χ ⊆ ball 0 R → (∀ x, |χ x| ≤ 1) →
      ∀ r > (0 : ℝ), (∀ x ∈ ball 0 r, χ x = 1) →
      ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
        |deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
          fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
            (fun y q => heatNormalCutoffParametrix E χ t y q l) x k| ≤ C * t := by
  obtain ⟨R₀, hR₀, C₀, hC₀, hbound⟩ :=
    heatNormalBundleParametrix_residual_uniform_linear E hRic he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ ball 0 R₀ ∧
      E.base.a x = (heatNormalMetric g o e x)⁻¹ ∧ E.base.b x = heatNormalDrift g o e x ∧
      E.B x = heatNormalBundleFirst D x ∧ E.C x = heatNormalBundleZero D x := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) hR₀, E.base.a_near, E.base.b_near,
      E.B_near, E.C_near] with x hx ha hb hB hC
    exact ⟨hx, ha, hb, hB, hC⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨R, hR, ?_⟩
  intro χ hχ hχc hχs hχb r hr hinner
  let u (l : Fin 6) : Fin 4 → FourSpace → Fin 6 → ℝ := fun m y q => E.amplitude m y q l
  have hu (l : Fin 6) (m : Fin 4) (q : Fin 6) : ContDiff ℝ 2 (fun y => u l m y q) :=
    (E.amplitude_regular m (by omega) q l).of_le (by norm_num)
  have herror (l : Fin 6) := fourHeatScaledCommutator_gaussian_bound
    E.base.a E.base.b E.B χ (u l)
    (fun i j => (E.base.a_regular i j).continuous)
    (fun i => (E.base.b_regular i).continuous)
    (fun i k q => (E.B_regular i k q).continuous)
    hχ hχc (hu l) r hr hinner
  choose C₁ hC₁ herror using herror
  refine ⟨C₀ + ∑ l, C₁ l, add_nonneg hC₀ (Finset.sum_nonneg fun l _ => hC₁ l), ?_⟩
  intro t ht x k l
  by_cases hx : x ∈ tsupport χ
  · obtain ⟨hx₀, ha, hb, hB, hC⟩ := hball (hχs hx)
    have hsym (i j : Fin 4) : E.base.a x i j = E.base.a x j i := by
      rw [ha]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    let Q := deriv (fun s => heatNormalBundleParametrix E s x k l) t +
      fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalBundleParametrix E t y q l) x k
    have hQ : |Q| ≤ C₀ * t := by
      dsimp only [Q]
      rw [ha, hb, hB, hC]
      exact hbound x hx₀ t ht.1 k l
    have hid := heatNormalCutoffParametrix_residual_identity E χ t ht.1 x hχ.contDiffAt
      (E.base.a x) (E.base.b x) (E.B x) (E.C x) hsym k l
    have hscaled := fourHeatScaledCommutator_identity E.base.a E.base.b E.B χ (u l)
      (hu l) t ht.1 x k
    have hid' : deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
        fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => heatNormalCutoffParametrix E χ t y q l) x k =
        χ x * Q + (fourHeatGaussian t x / t) *
          fourHeatScaledCommutator E.base.a E.base.b E.B χ (u l) t x k := by
      rw [← hscaled, hid]
      dsimp only [Q, heatNormalBundleParametrix, u]
      ring
    rw [hid']
    have hCl : C₁ l ≤ ∑ q, C₁ q :=
      Finset.single_le_sum (fun q _ => hC₁ q) (Finset.mem_univ l)
    calc
      _ ≤ |χ x * Q| + |(fourHeatGaussian t x / t) *
          fourHeatScaledCommutator E.base.a E.base.b E.B χ (u l) t x k| := abs_add_le _ _
      _ ≤ C₀ * t + C₁ l * t := by
        apply add_le_add _ (herror l t ht x k)
        rw [abs_mul]
        exact (mul_le_mul (hχb x) hQ (abs_nonneg Q) (by norm_num)).trans_eq (one_mul _)
      _ ≤ (C₀ + ∑ q, C₁ q) * t := by
        nlinarith [mul_le_mul_of_nonneg_right hCl ht.1.le]
  · rw [heatNormalCutoffParametrix_residual_zero E χ t x hx]
    rw [abs_zero]
    exact mul_nonneg (add_nonneg hC₀ (Finset.sum_nonneg fun q _ => hC₁ q)) ht.1.le

theorem heatNormalCutoffParametrix_bound {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ (R : ℝ) (hR : 0 < R), ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
      |deriv (fun s => heatNormalCutoffParametrix E (heatNormalChartBump R hR) s x k l) t +
        fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => heatNormalCutoffParametrix E (heatNormalChartBump R hR) t y q l) x k| ≤
        C * t := by
  obtain ⟨R, hR, h⟩ := heatNormalCutoffParametrix_bound_of_support E hRic he
  refine ⟨R, hR, ?_⟩
  apply h (heatNormalChartBump R hR) (heatNormalChartBump R hR).contDiff
    (heatNormalChartBump R hR).hasCompactSupport
  · rw [(heatNormalChartBump R hR).tsupport_eq]
    exact closedBall_subset_ball (by change R / 2 < R; linarith)
  · intro x
    rw [abs_of_nonneg (heatNormalChartBump R hR).nonneg]
    exact (heatNormalChartBump R hR).le_one
  · exact div_pos hR (by norm_num : (0 : ℝ) < 4)
  · intro x hx
    exact (heatNormalChartBump R hR).one_of_mem_closedBall (ball_subset_closedBall hx)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact normal one-form parametrix columns and their actual time derivatives. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalOneCutoffParametrix (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (x : FourSpace) (k l : Fin 4) : ℝ := χ x * heatNormalOneParametrix E t x k l

theorem heatNormalOneParametrix_space_regular (E : HeatNormalOneExtension D)
    (t : ℝ) (k l : Fin 4) : ContDiff ℝ 4 (fun x => heatNormalOneParametrix E t x k l) := by
  have hP := (((E.amplitude_regular 0 (by omega) k l).add
    ((contDiff_const (c := t)).mul (E.amplitude_regular 1 (by omega) k l))).add
    ((contDiff_const (c := t ^ 2)).mul (E.amplitude_regular 2 (by omega) k l))).add
    ((contDiff_const (c := t ^ 3)).mul (E.amplitude_regular 3 (by omega) k l))
  exact ((fourHeatGaussian_smooth t).of_le (by norm_num)).mul hP

def heatNormalOneCutoffColumn (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 4) (x : FourSpace) : FourSpace :=
  WithLp.toLp 2 (fun k => heatNormalOneCutoffParametrix E χ t x k l)

theorem heatNormalOneCutoffColumn_regular (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (t : ℝ) (l : Fin 4) :
    ContDiff ℝ 4 (heatNormalOneCutoffColumn E χ t l) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  exact hχ.mul (heatNormalOneParametrix_space_regular E t k l)

theorem heatNormalOneCutoffColumn_support (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) :
    tsupport (heatNormalOneCutoffColumn E χ t l) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have hχ : χ x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  apply WithLp.ofLp_injective 2
  funext k
  simp only [heatNormalOneCutoffColumn, WithLp.ofLp_toLp, heatNormalOneCutoffParametrix,
    hχ, zero_mul, Pi.zero_apply, WithLp.ofLp_zero]

def heatNormalOneTimeColumn (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 4) (x : FourSpace) : FourSpace :=
  WithLp.toLp 2 (fun k => χ x * fourHeatGaussianPolynomialTime
    (fun m y => E.amplitude m y k l) t x)

theorem heatNormalOneTimeColumn_component (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (l k : Fin 4) (x : FourSpace) :
    heatNormalOneTimeColumn E χ t l x k =
      deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t :=
  ((fourHeatGaussianPolynomial_hasDerivAt (fun m y => E.amplitude m y k l) t ht x).const_mul
    (χ x)).deriv.symm

theorem heatNormalOneTimeColumn_regular (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (t : ℝ) (l : Fin 4) :
    ContDiff ℝ 2 (heatNormalOneTimeColumn E χ t l) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  have hu (m : Fin 4) : ContDiff ℝ 2 (fun y => E.amplitude m y k l) :=
    (E.amplitude_regular m (by omega) k l).of_le (by norm_num)
  have hQ : ContDiff ℝ 2 (fun x => fourHeatPolynomialTime (fun m y => E.amplitude m y k l) t x) :=
    ((hu 1).add ((contDiff_const (c := 2 * t)).mul (hu 2))).add
      ((contDiff_const (c := 3 * t ^ 2)).mul (hu 3))
  have hF : ContDiff ℝ 2 (fourHeatGaussianTimeFactor t) :=
    ((contDiff_norm_sq ℝ).div_const (4 * t ^ 2)).sub contDiff_const
  have hG : ContDiff ℝ 2 (fourHeatGaussian t) := (fourHeatGaussian_smooth t).of_le (by norm_num)
  exact hχ.mul (((hF.mul hG).mul (fourHeatPolynomial_contDiff _ hu t)).add (hG.mul hQ))

theorem heatNormalOneTimeColumn_support (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) :
    tsupport (heatNormalOneTimeColumn E χ t l) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have hχ : χ x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  apply WithLp.ofLp_injective 2
  funext k
  simp only [heatNormalOneTimeColumn, WithLp.ofLp_toLp, hχ, zero_mul, WithLp.ofLp_zero,
    Pi.zero_apply]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalOneGlobalColumn (E : HeatNormalOneExtension D)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatNormalOneAmplitudeL2 D C hCt hP hD (heatNormalOneCutoffColumn E χ t l)
    ((heatNormalOneCutoffColumn_regular E χ hχ t l).of_le (by norm_num))
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneCutoffColumn_support E χ t l))
    ((heatNormalOneCutoffColumn_support E χ t l).trans hs)

def heatNormalOneGlobalTimeColumn (E : HeatNormalOneExtension D)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatNormalOneAmplitudeL2 D C hCt hP hD (heatNormalOneTimeColumn E χ t l)
    (heatNormalOneTimeColumn_regular E χ hχ t l)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneTimeColumn_support E χ t l))
    ((heatNormalOneTimeColumn_support E χ t l).trans hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reconstruction of the actual one-form heat operator by differentiated
scalar and two-form heat potentials. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormHeatReconstructed (t : ℝ≥0) (ht : 0 < t) : OneFormL2 o →L[ℝ] OneFormL2 o :=
  (scalarH1Differential d).comp ((scalarHeatH1Lift d t ht).comp (oneFormScalarPotential hRic d)) +
    (twoFormH1Codifferential hRic).comp ((twoFormHeatLift hRic t ht).comp (oneFormTwoFormPotential hRic d))

theorem oneFormHeatReconstructed_exact (t : ℝ≥0) (ht : 0 < t)
    (i : OneFormExactEigenIndex g o d) :
    oneFormHeatReconstructed hRic d t ht (oneFormExactEigenvector g o d i) =
      scalarBaseHeatWeight g o d t i.val • oneFormExactEigenvector g o d i := by
  change scalarH1Differential d (scalarHeatH1Lift d t ht (oneFormScalarPotential hRic d _)) +
    twoFormH1Codifferential hRic (twoFormHeatLift hRic t ht (oneFormTwoFormPotential hRic d _)) = _
  rw [oneFormScalarPotential_exact, oneFormTwoFormPotential_exact, map_zero, map_zero, add_zero,
    map_smul, scalarHeatH1Lift_eigen, map_smul, map_smul, scalarH1Differential_smooth]
  change _ = _ • ((Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ • _)
  rw [smul_comm]
  rfl

theorem oneFormHeatReconstructed_coexact (t : ℝ≥0) (ht : 0 < t)
    (i : OneFormCoexactEigenIndex (o := o) hRic) :
    oneFormHeatReconstructed hRic d t ht (oneFormCoexactEigenvector hRic i) =
      twoFormHeatWeight hRic t i.1 • oneFormCoexactEigenvector hRic i := by
  change scalarH1Differential d (scalarHeatH1Lift d t ht (oneFormScalarPotential hRic d _)) +
    twoFormH1Codifferential hRic (twoFormHeatLift hRic t ht (oneFormTwoFormPotential hRic d _)) = _
  rw [oneFormScalarPotential_coexact, oneFormTwoFormPotential_coexact, map_zero, map_zero, zero_add,
    map_smul, twoFormHeatLift_coexactLift, map_smul, map_smul]
  have hc := twoFormH1Codifferential_smooth hRic (oneFormCoexactLift hRic i : SmoothH1TwoForm o)
  rw [hc]
  change (Real.sqrt (i.1.val⁻¹ - 1))⁻¹ • (twoFormHeatWeight hRic t i.1 •
      smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField (oneFormCoexactLift hRic i))) = _
  rw [oneFormCoexactLift_codifferential, smul_smul, smul_smul]
  congr 1
  have hn : Real.sqrt (i.1.val⁻¹ - 1) ≠ 0 :=
    (Real.sqrt_pos.mpr (oneFormCoexactEigenvector_rate_pos hRic i)).ne'
  calc
    _ = twoFormHeatWeight hRic t i.1 * ((Real.sqrt (i.1.val⁻¹ - 1))⁻¹ * Real.sqrt (i.1.val⁻¹ - 1)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn, mul_one]

theorem oneFormHeat_reconstructed (t : ℝ≥0) (ht : 0 < t) :
    oneFormHeatReconstructed hRic d t ht = oneFormHeat hRic d t := by
  apply ContinuousLinearMap.ext
  intro f
  apply sub_eq_zero.mp
  have he (i : OneFormEigenIndex hRic d) :
      (oneFormHeatReconstructed hRic d t ht - oneFormHeat hRic d t) (oneFormEigenvector hRic d i) ∈
        (⊥ : Submodule ℝ (OneFormL2 o)) := by
    rw [Submodule.mem_bot]
    change oneFormHeatReconstructed hRic d t ht (oneFormEigenvector hRic d i) -
      oneFormHeat hRic d t (oneFormEigenvector hRic d i) = (0 : OneFormL2 o)
    rw [oneFormHeat_eigenvector]
    rcases i with i | i
    · change oneFormHeatReconstructed hRic d t ht (oneFormExactEigenvector g o d i) -
        scalarBaseHeatWeight g o d t i.val • oneFormExactEigenvector g o d i = 0
      rw [oneFormHeatReconstructed_exact, sub_self]
    · change oneFormHeatReconstructed hRic d t ht (oneFormCoexactEigenvector hRic i) -
        twoFormHeatWeight hRic t i.1 • oneFormCoexactEigenvector hRic i = 0
      rw [oneFormHeatReconstructed_coexact, sub_self]
  exact continuousLinearMap_mem_closed_of_total (oneFormEigenvector hRic d)
    (oneFormEigenvector_total hRic d) (oneFormHeatReconstructed hRic d t ht - oneFormHeat hRic d t)
    ⊥ isClosed_singleton he f

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar heat trace consists of its positive modes and one constant mode. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

include hRic in
theorem scalarHeatTrace_split (t : ℝ≥0) (ht : 0 < t) :
    scalarHeatSpectralTrace d t = oneFormExactHeatTrace d t + 1 := by
  classical
  have hs := scalarHeat_weight_summable g o d t ht
  have he := hs.tsum_subtype_add_tsum_subtype_compl
    {i : ScalarBaseEigenIndex g o d | 0 < scalarBaseHeatRate g o d i}
  have hz : (∑' i : {i : ScalarBaseEigenIndex g o d |
      i ∈ {i | 0 < scalarBaseHeatRate g o d i}ᶜ}, scalarBaseHeatWeight g o d t i.val) = 1 := by
    rw [tsum_subtype]
    have hi : {i : ScalarBaseEigenIndex g o d | i ∈ {i | 0 < scalarBaseHeatRate g o d i}ᶜ}.indicator
        (scalarBaseHeatWeight g o d t) =
        (fun i => if i.1.val = 1 then (1 : ℝ) else 0) := by
      funext i
      by_cases h : i.1.val = 1
      · have hr := (scalarBaseHeatRate_eq_zero g o d i).mpr h
        simp [Set.indicator, hr, scalarBaseHeatWeight, h]
      · have hr : 0 < scalarBaseHeatRate g o d i :=
          lt_of_le_of_ne (scalarBaseHeatRate_nonneg g o d i)
            (Ne.symm (fun he => h ((scalarBaseHeatRate_eq_zero g o d i).mp he)))
        simp [Set.indicator, hr, h]
    rw [hi, scalarHeat_zero_weight_sum d t ht, scalarBase_fixed_finrank hRic d]
    norm_num
  change oneFormExactHeatTrace d t + _ = scalarHeatSpectralTrace d t at he
  have hz' : (∑' i : ↑{i : ScalarBaseEigenIndex g o d | 0 < scalarBaseHeatRate g o d i}ᶜ,
      scalarBaseHeatWeight g o d t i.val) = 1 := hz
  rw [hz'] at he
  exact he.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The negative-chirality signature kernel has dimension one plus the
anti-self-dual harmonic dimension. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance signatureNegativeSectionAddGroup : AddCommGroup (signatureNegativeSections (o := o)) :=
  Submodule.addCommGroup _
local instance signatureNegativeKernelAddGroup : AddCommGroup (SignatureNegativeKernel (o := o)) :=
  Submodule.addCommGroup _
local instance signatureNegativeHarmonicAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

def signatureNegativeKernel_harmonic (hRic : RicciThree g)
    (x : SignatureNegativeKernel (o := o)) : smoothHarmonicNegative (o := o) hRic :=
  ⟨⟨x.val.val.1.2.1, (signatureNegativeKernel_data hRic x).2.1⟩, by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [neg_one_smul]
    apply Subtype.ext
    exact (signatureNegativeKernel_data hRic x).2.2.1⟩

def signatureNegativeCoordinates (hRic : RicciThree g) :
    SignatureNegativeKernel (o := o) →ₗ[ℝ] ℝ × smoothHarmonicNegative (o := o) hRic where
  toFun x := (x.val.val.1.1.val (Classical.arbitrary M), signatureNegativeKernel_harmonic hRic x)
  map_add' _ _ := Prod.ext rfl (Subtype.ext (Subtype.ext rfl))
  map_smul' _ _ := Prod.ext rfl (Subtype.ext (Subtype.ext rfl))

theorem signatureNegativeCoordinates_injective (hRic : RicciThree g) :
    Function.Injective (signatureNegativeCoordinates (o := o) hRic) := by
  intro x y hxy
  have hx := signatureNegativeKernel_data hRic x
  have hy := signatureNegativeKernel_data hRic y
  obtain ⟨r, hr⟩ := hx.2.2.2.2
  obtain ⟨s, hs⟩ := hy.2.2.2.2
  have hv := congrArg Prod.fst hxy
  change x.val.val.1.1.val (Classical.arbitrary M) =
    y.val.val.1.1.val (Classical.arbitrary M) at hv
  rw [hr, hs] at hv
  have hrs : r = s := hv
  have hf : x.val.val.1.1 = y.val.val.1.1 :=
    hr.trans ((congrArg (smoothScalarConst (M := M)) hrs).trans hs.symm)
  have ha : x.val.val.1.2.1 = y.val.val.1.2.1 :=
    congrArg (fun z : ℝ × smoothHarmonicNegative (o := o) hRic => z.2.val.val) hxy
  have hb : x.val.val.1.2.2 = y.val.val.1.2.2 := by
    rw [hx.2.2.2.1, hy.2.2.2.1, hf]
  exact Subtype.ext (Subtype.ext
    (Prod.ext (Prod.ext hf (Prod.ext ha hb)) (hx.1.trans hy.1.symm)))

theorem signatureNegativeCoordinates_surjective (hRic : RicciThree g) :
    Function.Surjective (signatureNegativeCoordinates (o := o) hRic) := by
  rintro ⟨r, h⟩
  let t : HodgeSections o := ((smoothScalarConst r, h.val.val, smoothScalarConst r), 0)
  have ht : t ∈ signatureNegativeSections (o := o) := by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [neg_one_smul]
    apply Prod.ext
    · change signatureEvenGrading (smoothScalarConst r, h.val.val, smoothScalarConst r) =
        (-smoothScalarConst r, -h.val.val, -smoothScalarConst r)
      rw [signatureEvenGrading_apply]
      exact Prod.ext rfl (Prod.ext
        (congrArg Subtype.val (smoothHarmonicNegative_star hRic h)) rfl)
    · change signatureOddGrading (0 : HodgeOddSections M) = -0
      rw [map_zero, neg_zero]
  have hd : smoothHodgeDirac t = 0 := by
    apply Prod.ext
    · change smoothHodgeDiracOdd (o := o) (0 : HodgeOddSections M) = 0
      exact map_zero _
    · exact (harmonicToEvenKernel (o := o) (r, h.val, r)).property
  let x : SignatureNegativeKernel (o := o) := ⟨⟨t, ht⟩, Subtype.ext hd⟩
  refine ⟨x, ?_⟩
  exact Prod.ext rfl (Subtype.ext (Subtype.ext rfl))

def signatureNegativeKernelEquiv (hRic : RicciThree g) :
    SignatureNegativeKernel (o := o) ≃ₗ[ℝ] ℝ × smoothHarmonicNegative (o := o) hRic :=
  LinearEquiv.ofBijective (signatureNegativeCoordinates hRic)
    ⟨signatureNegativeCoordinates_injective hRic, signatureNegativeCoordinates_surjective hRic⟩

theorem signatureNegativeKernel_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (SignatureNegativeKernel (o := o)) :=
  FiniteDimensional.of_injective (signatureNegativeCoordinates hRic)
    (signatureNegativeCoordinates_injective hRic)

theorem signatureNegativeKernel_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (SignatureNegativeKernel (o := o)) =
      1 + Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) := by
  rw [(signatureNegativeKernelEquiv (o := o) hRic).finrank_eq,
    Module.finrank_prod, Module.finrank_self]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive-chirality signature kernel has dimension one plus the
self-dual harmonic dimension. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance signaturePositiveSectionAddGroup : AddCommGroup (signaturePositiveSections (o := o)) :=
  Submodule.addCommGroup _
local instance signaturePositiveKernelAddGroup : AddCommGroup (SignaturePositiveKernel (o := o)) :=
  Submodule.addCommGroup _
local instance signaturePositiveHarmonicAddGroup : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

def signaturePositiveKernel_harmonic (hRic : RicciThree g)
    (x : SignaturePositiveKernel (o := o)) : smoothHarmonicPositive (o := o) hRic :=
  ⟨⟨x.val.val.1.2.1, (signaturePositiveKernel_data hRic x).2.1⟩, by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [one_smul]
    apply Subtype.ext
    exact (signaturePositiveKernel_data hRic x).2.2.1⟩

def signaturePositiveCoordinates (hRic : RicciThree g) :
    SignaturePositiveKernel (o := o) →ₗ[ℝ] ℝ × smoothHarmonicPositive (o := o) hRic where
  toFun x := (x.val.val.1.1.val (Classical.arbitrary M), signaturePositiveKernel_harmonic hRic x)
  map_add' _ _ := Prod.ext rfl (Subtype.ext (Subtype.ext rfl))
  map_smul' _ _ := Prod.ext rfl (Subtype.ext (Subtype.ext rfl))

theorem signaturePositiveCoordinates_injective (hRic : RicciThree g) :
    Function.Injective (signaturePositiveCoordinates (o := o) hRic) := by
  intro x y hxy
  have hx := signaturePositiveKernel_data hRic x
  have hy := signaturePositiveKernel_data hRic y
  obtain ⟨r, hr⟩ := hx.2.2.2.2
  obtain ⟨s, hs⟩ := hy.2.2.2.2
  have hv := congrArg Prod.fst hxy
  change x.val.val.1.1.val (Classical.arbitrary M) =
    y.val.val.1.1.val (Classical.arbitrary M) at hv
  rw [hr, hs] at hv
  have hrs : r = s := hv
  have hf : x.val.val.1.1 = y.val.val.1.1 :=
    hr.trans ((congrArg (smoothScalarConst (M := M)) hrs).trans hs.symm)
  have ha : x.val.val.1.2.1 = y.val.val.1.2.1 :=
    congrArg (fun z : ℝ × smoothHarmonicPositive (o := o) hRic => z.2.val.val) hxy
  have hb : x.val.val.1.2.2 = y.val.val.1.2.2 := by
    rw [hx.2.2.2.1, hy.2.2.2.1, hf]
  exact Subtype.ext (Subtype.ext
    (Prod.ext (Prod.ext hf (Prod.ext ha hb)) (hx.1.trans hy.1.symm)))

theorem signaturePositiveCoordinates_surjective (hRic : RicciThree g) :
    Function.Surjective (signaturePositiveCoordinates (o := o) hRic) := by
  rintro ⟨r, h⟩
  let t : HodgeSections o := ((smoothScalarConst r, h.val.val, smoothScalarConst (-r)), 0)
  have ht : t ∈ signaturePositiveSections (o := o) := by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [one_smul]
    apply Prod.ext
    · change signatureEvenGrading (smoothScalarConst r, h.val.val, smoothScalarConst (-r)) =
        (smoothScalarConst r, h.val.val, smoothScalarConst (-r))
      rw [signatureEvenGrading_apply]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact Subtype.ext (funext (fun _ => neg_neg r))
      · exact congrArg Subtype.val (smoothHarmonicPositive_star hRic h)
      · rfl
    · change signatureOddGrading (0 : HodgeOddSections M) = 0
      exact map_zero _
  have hd : smoothHodgeDirac t = 0 := by
    apply Prod.ext
    · change smoothHodgeDiracOdd (o := o) (0 : HodgeOddSections M) = 0
      exact map_zero _
    · exact (harmonicToEvenKernel (o := o) (r, h.val, -r)).property
  let x : SignaturePositiveKernel (o := o) := ⟨⟨t, ht⟩, Subtype.ext hd⟩
  refine ⟨x, ?_⟩
  exact Prod.ext rfl (Subtype.ext (Subtype.ext rfl))

def signaturePositiveKernelEquiv (hRic : RicciThree g) :
    SignaturePositiveKernel (o := o) ≃ₗ[ℝ] ℝ × smoothHarmonicPositive (o := o) hRic :=
  LinearEquiv.ofBijective (signaturePositiveCoordinates hRic)
    ⟨signaturePositiveCoordinates_injective hRic, signaturePositiveCoordinates_surjective hRic⟩

theorem signaturePositiveKernel_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (SignaturePositiveKernel (o := o)) :=
  FiniteDimensional.of_injective (signaturePositiveCoordinates hRic)
    (signaturePositiveCoordinates_injective hRic)

theorem signaturePositiveKernel_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (SignaturePositiveKernel (o := o)) =
      1 + Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) := by
  rw [(signaturePositiveKernelEquiv (o := o) hRic).finrank_eq,
    Module.finrank_prod, Module.finrank_self]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time Hodge-signed heat trace equals the harmonic signature.
 -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_signed_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic => twoFormHeatWeight hRic t i.1 *
      inner ℝ (twoFormEigenvector hRic i) (twoFormL2Hodge (twoFormEigenvector hRic i))) := by
  apply (twoFormHeat_weight_summable (o := o) hRic t ht).of_norm_bounded
  intro i
  have hw : 0 ≤ twoFormHeatWeight hRic t i.1 := (Real.exp_pos _).le
  rw [norm_mul, Real.norm_of_nonneg hw]
  have hb := norm_inner_le_norm (𝕜 := ℝ) (twoFormEigenvector hRic i)
    (twoFormL2Hodge (twoFormEigenvector hRic i))
  rw [twoFormL2Hodge_norm, (twoFormEigenvector_orthonormal hRic).1 i, one_mul] at hb
  exact (mul_le_mul_of_nonneg_left hb hw).trans_eq (mul_one _)

theorem twoFormHeat_spectral_signed_trace (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    (∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1 *
      inner ℝ (twoFormEigenvector hRic i) (twoFormL2Hodge (twoFormEigenvector hRic i))) =
    LinearMap.trace ℝ (Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1)
      (twoFormEigenspaceHodge hRic 1) := by
  classical
  have he : (∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1 *
      inner ℝ (twoFormEigenvector hRic i) (twoFormL2Hodge (twoFormEigenvector hRic i))) =
      ∑' μ : TwoFormSpectralValue (o := o) hRic, twoFormHeatWeight hRic t μ *
        LinearMap.trace ℝ (TwoFormSpectralSpace hRic μ) (twoFormEigenspaceHodge hRic μ.val) := by
    rw [(twoFormHeat_signed_summable (o := o) hRic t ht).tsum_sigma]
    apply tsum_congr
    intro μ
    rw [tsum_fintype]
    change (∑ j, twoFormHeatWeight hRic t μ * inner ℝ
      (twoFormEigenvector hRic ⟨μ,j⟩) (twoFormL2Hodge (twoFormEigenvector hRic ⟨μ,j⟩))) = _
    rw [← Finset.mul_sum, ← twoFormEigenspaceHodge_trace_basis]
  rw [he]
  by_cases h1 : Module.End.HasEigenvalue (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1
  · let μ₁ : TwoFormSpectralValue (o := o) hRic := ⟨1, h1⟩
    rw [tsum_eq_single μ₁]
    · have hw : twoFormHeatWeight hRic t μ₁ = 1 := by simp [twoFormHeatWeight, twoFormHeatRate, μ₁]
      rw [hw, one_mul]
      rfl
    · intro μ hμ
      have hne : μ.val ≠ 1 := fun hv => hμ (Subtype.ext hv)
      rw [twoFormEigenspaceHodge_trace_zero hRic μ hne, mul_zero]
  · have hbot : Module.End.eigenspace (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1 = ⊥ :=
      not_ne_iff.mp h1
    have hsub : Subsingleton (Module.End.eigenspace
        (twoFormShiftedResolvent (o := o) hRic).toLinearMap 1) := by
      rw [hbot]
      infer_instance
    have hzero : twoFormEigenspaceHodge (o := o) hRic 1 = 0 := by
      have := hsub
      exact Subsingleton.elim _ _
    rw [hzero, map_zero]
    calc
      _ = ∑' _μ : TwoFormSpectralValue (o := o) hRic, (0 : ℝ) := by
        apply tsum_congr
        intro μ
        have hne : μ.val ≠ 1 := by
          intro hv
          exact h1 (hv ▸ μ.property)
        rw [twoFormEigenspaceHodge_trace_zero hRic μ hne, mul_zero]
      _ = 0 := tsum_zero

theorem twoFormHeatKernel_signature_trace (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic t ht x x)
      ∂normalizedVolume g) =
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℝ) -
        (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℝ) := by
  rw [twoFormHeatKernel_signed_integral hRic t ht, twoFormHeat_spectral_signed_trace hRic t ht,
    twoFormHarmonicEigenspace_trace hRic]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual signed spectral diagonal as the Gram sum of its six columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff Manifold _root_.Topology NNReal

noncomputable section

theorem twoFormHodge_inner_coordinates (a : TwoFormFour) :
    inner ℝ a (twoFormHodge a) =
      ∑ i, ∑ j, twoFormHodgeMatrix i j * (a i * a j) := by
  rw [← twoFormHodgeMatrix_apply a]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatFrameColumn_inner (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l m : Fin 6) :
    inner ℝ (twoFormHeatFrameColumn (o := o) hRic t ht e l)
      (twoFormHeatFrameColumn (o := o) hRic t ht e m) =
      ∑' i, twoFormHeatFrameCoefficient (o := o) hRic t e l i * twoFormHeatFrameCoefficient (o := o) hRic t e m i := by
  rw [← (twoFormEigenbasis (o := o) hRic).tsum_inner_mul_inner]
  apply tsum_congr
  intro i
  rw [twoFormEigenbasis_apply,
    real_inner_comm (twoFormHeatFrameColumn (o := o) hRic t ht e m),
    twoFormHeatFrameColumn_eigen, twoFormHeatFrameColumn_eigen]

theorem twoFormHeatFrameCoefficient_product_summable (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l m : Fin 6) :
    Summable (fun i => twoFormHeatFrameCoefficient (o := o) hRic t e l i *
      twoFormHeatFrameCoefficient (o := o) hRic t e m i) := by
  have h := (twoFormEigenbasis (o := o) hRic).summable_inner_mul_inner
    (twoFormHeatFrameColumn (o := o) hRic t ht e l) (twoFormHeatFrameColumn (o := o) hRic t ht e m)
  simpa only [twoFormEigenbasis_apply,
    real_inner_comm (twoFormHeatFrameColumn (o := o) hRic t ht e m), twoFormHeatFrameColumn_eigen] using h

theorem twoFormHeatKernel_signed_columns (hRic : RicciThree g)
    (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (he : e ∈ o.positive) :
    twoFormFiberSignedTrace (twoFormHeatKernel (o := o) hRic (t + t) (add_pos ht ht) e.base e.base) =
      ∑ l, ∑ m, twoFormHodgeMatrix l m *
        inner ℝ (twoFormHeatFrameColumn (o := o) hRic t ht e l) (twoFormHeatFrameColumn (o := o) hRic t ht e m) := by
  rw [twoFormHeatKernel_signed_diagonal]
  have htime : (t + t) / 2 = t := by ring
  simp only [htime, twoFormHeatFrameColumn_inner (o := o)]
  have hs (l m : Fin 6) := (twoFormHeatFrameCoefficient_product_summable (o := o) hRic t ht e l m).mul_left
    (twoFormHodgeMatrix l m)
  simp_rw [← tsum_mul_left]
  have hsum (l : Fin 6) : (∑ m, ∑' i,
      twoFormHodgeMatrix l m * (twoFormHeatFrameCoefficient (o := o) hRic t e l i *
        twoFormHeatFrameCoefficient (o := o) hRic t e m i)) =
      ∑' i, ∑ m, twoFormHodgeMatrix l m * (twoFormHeatFrameCoefficient (o := o) hRic t e l i *
        twoFormHeatFrameCoefficient (o := o) hRic t e m i) :=
    (Summable.tsum_finsetSum (fun m _ => hs l m)).symm
  simp_rw [hsum]
  rw [← Summable.tsum_finsetSum (fun l _ => summable_sum (fun m _ => hs l m))]
  apply tsum_congr
  intro i
  have hp := twoFormFrameValue_inner (o := o)
    (twoFormHeatSection (o := o) hRic t ht (twoFormEigenvector (o := o) hRic i)).val
    (fun x => twoFormHodge ((twoFormHeatSection (o := o) hRic t ht (twoFormEigenvector (o := o) hRic i)).val x)) e
  rw [twoFormFrameValue_hodge o _ e he, twoFormHodge_inner_coordinates] at hp
  rw [← hp]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  rw [twoFormHeatFrameCoefficient_eq hRic t ht, twoFormHeatFrameCoefficient_eq hRic t ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two-form heat trace is twice its coexact trace plus the harmonic dimension. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

theorem twoFormHeat_grouped_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun μ : TwoFormSpectralValue (o := o) hRic =>
      twoFormHeatWeight hRic t μ * (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ)) := by
  have hs := (twoFormHeat_weight_summable (o := o) hRic t ht).sigma
  apply hs.congr
  intro μ
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

theorem oneFormCoexactHeat_grouped_summable (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun μ : TwoFormSpectralValue (o := o) hRic =>
      twoFormHeatWeight hRic t μ * (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) : ℝ)) := by
  have hs := ((twoFormHeat_weight_summable (o := o) hRic t ht).comp_injective
    (i := oneFormCoexactToTwoFormIndex (o := o) hRic)
      (oneFormCoexactToTwoFormIndex_injective hRic)).sigma
  apply hs.congr
  intro μ
  change (∑' j : Fin (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ)),
    twoFormHeatWeight hRic t μ) = _
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]

theorem twoFormHeatTrace_split (t : ℝ≥0) (ht : 0 < t) :
    twoFormHeatSpectralTrace (o := o) hRic t =
      2 * oneFormCoexactHeatTrace (o := o) hRic t +
        (Module.finrank ℝ (smoothHarmonicTwoForms (o := o)) : ℝ) := by
  classical
  have hg := twoFormHeat_grouped_summable (o := o) hRic t ht
  have hc := oneFormCoexactHeat_grouped_summable (o := o) hRic t ht
  have hz : Summable (fun μ : TwoFormSpectralValue (o := o) hRic =>
      if μ.val = 1 then (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ) else 0) := by
    apply (hg.sub (hc.mul_left 2)).congr
    intro μ
    rw [twoForm_heat_multiplicity_term hRic t μ]
    ring
  rw [twoFormHeatTrace_grouped hRic t ht, oneFormCoexactHeatTrace_grouped hRic t ht]
  calc
    _ = ∑' μ : TwoFormSpectralValue (o := o) hRic,
        (2 * (twoFormHeatWeight hRic t μ *
          (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ) : ℝ)) +
            if μ.val = 1 then (Module.finrank ℝ (TwoFormSpectralSpace hRic μ) : ℝ) else 0) :=
      tsum_congr (twoForm_heat_multiplicity_term hRic t)
    _ = _ := by
      rw [(hc.mul_left 2).tsum_add hz, tsum_mul_left,
        tsum_eigenvalue_finrank (twoFormShiftedResolvent (o := o) hRic).toLinearMap,
        ← (smoothHarmonicResolventEquiv (o := o) hRic).finrank_eq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal parametrix columns as elements of the
global two-form Hilbert space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalCutoffColumn (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 6) (x : FourSpace) : TwoFormFour :=
  WithLp.toLp 2 (fun k => heatNormalCutoffParametrix E χ t x k l)

theorem heatNormalCutoffColumn_regular (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (t : ℝ) (l : Fin 6) :
    ContDiff ℝ 2 (heatNormalCutoffColumn E χ t l) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  exact hχ.mul (heatNormalBundleParametrix_space_regular E t k l)

theorem heatNormalCutoffColumn_support (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) :
    tsupport (heatNormalCutoffColumn E χ t l) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have hχ : χ x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  apply WithLp.ofLp_injective 2
  funext k
  simp only [heatNormalCutoffColumn, WithLp.ofLp_toLp, heatNormalCutoffParametrix,
    hχ, zero_mul, Pi.zero_apply, WithLp.ofLp_zero]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalGlobalParametrixColumn (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalAmplitudeL2 D C hCt hP hD (heatNormalCutoffColumn E χ t l)
    (heatNormalCutoffColumn_regular E χ hχ t l)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E χ t l))
    ((heatNormalCutoffColumn_support E χ t l).trans hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Express compact normal-coordinate tensors in one actual smooth
manifold chart, without changing their frame-bundle values. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Function
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] {g : SmoothMetric M} {c : M}

omit [T3Space M] in
theorem heatNormalOneChart_realization (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : FourSpace → CovariantCoordinates 1) (f : FrameBundle g) :
    heatNormalOneFrameLift g c C T f =
    heatNormalOneFrameLift g c (chartAt FourSpace c).symm
      (heatCompactOneLift (C.trans (chartAt FourSpace c)) T) f := by
  classical
  let B := C.trans (chartAt FourSpace c)
  by_cases hf : f.base ∈ C.target
  · have hfc := hCt hf
    have hz : chartAt FourSpace c f.base ∈ B.target := by
      change chartAt FourSpace c f.base ∈ (chartAt FourSpace c).target ∧
        (chartAt FourSpace c).symm (chartAt FourSpace c f.base) ∈ C.target
      exact ⟨(chartAt FourSpace c).map_source hfc, by rwa [(chartAt FourSpace c).left_inv hfc]⟩
    rw [heatNormalOneFrameLift, ite_eq_left hf, heatNormalOneFrameLift,
      ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hfc)]
    change frameTensor _ (T (C.symm f.base)) =
      frameTensor _ (heatCompactOneLift B T (chartAt FourSpace c f.base))
    rw [heatCompactOneLift, ite_eq_left hz]
    change frameTensor _ (T (C.symm f.base)) =
      frameTensor _ (T (C.symm ((chartAt FourSpace c).symm (chartAt FourSpace c f.base))))
    rw [(chartAt FourSpace c).left_inv hfc]
  · rw [heatNormalOneFrameLift, ite_eq_right hf]
    by_cases hfc : f.base ∈ (chartAt FourSpace c).source
    · have hz : chartAt FourSpace c f.base ∉ B.target := by
        intro h
        apply hf
        have h' : (chartAt FourSpace c).symm (chartAt FourSpace c f.base) ∈ C.target := h.2
        rwa [(chartAt FourSpace c).left_inv hfc] at h'
      rw [heatNormalOneFrameLift,
        ite_eq_left (show f.base ∈ (chartAt FourSpace c).symm.target from hfc)]
      change (0 : CovariantCoordinates 1) =
        frameTensor _ (heatCompactOneLift B T (chartAt FourSpace c f.base))
      rw [heatCompactOneLift, ite_eq_right hz]
      funext a
      simp only [frameTensor, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    · rw [heatNormalOneFrameLift,
        ite_eq_right (show f.base ∉ (chartAt FourSpace c).symm.target from hfc)]

local instance heatNormalOneChartCompact [CompactSpace M] : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatNormalOneTensor_L2_realization [CompactSpace M] [MeasurableSpace M]
    [BorelSpace M] [Nonempty M] {o : FrameOrientation g}
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : FourSpace → CovariantCoordinates 1) (hT : ContinuousOn T C.source)
    (hc : HasCompactSupport T) (hs : tsupport T ⊆ C.source)
 :
    let F : C(FrameBundle g, FourSpace) :=
      ⟨fun f => WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C T f ![i]),
        (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (continuous_apply ![i]).comp
          (heatNormalOneFrameLift_continuous g c C T hCt hT hc hs)))⟩
    oneFormFrameL2 (oneFormFromContinuous (o := o) F) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F := by
  let B := C.trans (chartAt FourSpace c)
  have hBs : tsupport T ⊆ B.source := by rwa [heatNormalChartMap_source C hCt]
  have hBT : ContinuousOn T B.source := hT.mono (by rw [heatNormalChartMap_source C hCt])
  let H := heatCompactOneLift B T
  have hH : Continuous H := heatCompactOneLift_continuous B T hBT hc hBs
  have hK : IsCompact (B '' tsupport T) := hc.image_of_continuousOn (B.continuousOn.mono hBs)
  have hKt : B '' tsupport T ⊆ (chartAt FourSpace c).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (B.map_source (hBs hx)).1
  have hHs := heatCompactOneLift_tsupport B T hc hBs
  have heq : heatOneChart g c H hH.continuousOn
      (hK.of_isClosed_subset (isClosed_tsupport _) hHs) (hHs.trans hKt) =
      (⟨fun f => WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C T f ![i]),
        (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i => (continuous_apply ![i]).comp
          (heatNormalOneFrameLift_continuous g c C T hCt hT hc hs)))⟩ :
        C(FrameBundle g, FourSpace)) := by
    ext f i
    exact congrFun (heatNormalOneChart_realization C hCt T f).symm ![i]
  simpa only [heq] using heatOneChart_L2_realization (o := o) c H hH
    hK hKt hHs

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative and exact cutoff residual of the actual normal
bundle parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneParametrix_time_differentiable {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (t : ℝ) (ht : 0 < t) (x : FourSpace)
    (k l : Fin 4) : DifferentiableAt ℝ (fun s => heatNormalOneParametrix E s x k l) t := by
  exact ((fourHeatGaussian_hasDerivAt_time t ht x).mul
    (fourHeatPolynomial_hasDerivAt (fun m y => E.amplitude m y k l) t x)).differentiableAt

theorem heatNormalOneCutoffParametrix_residual_identity {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t)
    (x : FourSpace) (hχ : ContDiffAt ℝ 2 χ x) (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (ha : ∀ i j, a i j = a j i) (k l : Fin 4) :
    deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
      fourHeatOneOperator a b B C
        (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k =
    χ x * (deriv (fun s => heatNormalOneParametrix E s x k l) t +
      fourHeatOneOperator a b B C
        (fun y q => heatNormalOneParametrix E t y q l) x k) +
      fourHeatLocalOperator a b 0 χ x * heatNormalOneParametrix E t x k l -
      2 * (∑ i, ∑ j, a i j * partialDeriv χ i x *
        partialDeriv (fun y => heatNormalOneParametrix E t y k l) j x) +
      ∑ i, ∑ q, B i k q * partialDeriv χ i x * heatNormalOneParametrix E t x q l := by
  have hd := (heatNormalOneParametrix_time_differentiable E t ht x k l).hasDerivAt.const_mul
    (χ x)
  change HasDerivAt (fun s => heatNormalOneCutoffParametrix E χ s x k l) _ t at hd
  rw [hd.deriv]
  unfold heatNormalOneCutoffParametrix
  rw [fourHeatOneOperator_cutoff a b B C χ _ x ha hχ
    (fun q => ((heatNormalOneParametrix_space_regular E t q l).of_le (by norm_num)).contDiffAt) k]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative and Hodge image are combined before estimation,
so the actual Gaussian transport cancellations are retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalOneResidualColumn (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 4) : FourSpace → FourSpace :=
  heatNormalOneTimeColumn E χ t l + heatNormalOneOperatorAmplitude E (heatNormalOneCutoffColumn E χ t l)

theorem heatNormalOneResidualColumn_component (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (l k : Fin 4) (x : FourSpace) :
    heatNormalOneResidualColumn E χ t l x k =
      deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
        fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k := by
  change heatNormalOneTimeColumn E χ t l x k + _ = _
  rw [heatNormalOneTimeColumn_component E χ t ht l k x]
  rfl

theorem heatNormalOneResidualColumn_regular (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (t : ℝ) (l : Fin 4) :
    ContDiff ℝ 2 (heatNormalOneResidualColumn E χ t l) :=
  (heatNormalOneTimeColumn_regular E χ (hχ.of_le (by norm_num)) t l).add
    (heatNormalOneOperatorAmplitude_regular E _ (heatNormalOneCutoffColumn_regular E χ hχ t l))

theorem heatNormalOneResidualColumn_support (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) :
    tsupport (heatNormalOneResidualColumn E χ t l) ⊆ tsupport χ :=
  (tsupport_add _ _).trans (union_subset (heatNormalOneTimeColumn_support E χ t l)
    ((heatNormalOneOperatorAmplitude_support E _).trans (heatNormalOneCutoffColumn_support E χ t l)))

theorem heatNormalOneResidualColumn_bound (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (B : ℝ)
    (h : ∀ x k l, |deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
      fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k| ≤ B * t)
    (l : Fin 4) (x : FourSpace) : ‖heatNormalOneResidualColumn E χ t l x‖ ≤ 4 * (B * t) := by
  calc
    _ ≤ ∑ k, |heatNormalOneResidualColumn E χ t l x k| := fourSpace_norm_le_sum _
    _ ≤ ∑ _k : Fin 4, B * t := Finset.sum_le_sum fun k _ => by
      rw [heatNormalOneResidualColumn_component E χ t ht l k x]
      exact h x k l
    _ = _ := by simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative of the actual compact normal kernel under one
scalar pairing; only the cutoff-weighted test must be continuous. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCutoffParametrix_pairing_deriv (E : HeatNormalOneExtension D)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hc : HasCompactSupport χ) (t : ℝ) (ht : 0 < t) (k l : Fin 4) :
    HasDerivAt (fun s => ∫ x, heatNormalOneCutoffParametrix E χ s x k l * f x)
      (∫ x, deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t * f x) t := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => E.amplitude m x k l
  have h := fourHeat_compact_polynomial_pairing_deriv (fun x => χ x * f x) hχf hc.mul_right
    u (fun m => (E.amplitude_regular m (by omega) k l).continuous) t ht
  have hfun : (fun s => ∫ x, (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x)) =
      fun s => ∫ x, heatNormalOneCutoffParametrix E χ s x k l * f x := by
    funext s
    apply integral_congr_ae
    filter_upwards [] with x
    change (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x) =
      (χ x * (fourHeatGaussian s x * fourHeatPolynomial u s x)) * f x
    ring
  have hval : (∫ x, (χ x * f x) * fourHeatGaussianPolynomialTime u t x) =
      ∫ x, deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t * f x := by
    apply integral_congr_ae
    filter_upwards [] with x
    have hd := (fourHeatGaussianPolynomial_hasDerivAt u t ht x).const_mul (χ x)
    change HasDerivAt (fun s => heatNormalOneCutoffParametrix E χ s x k l)
      (χ x * fourHeatGaussianPolynomialTime u t x) t at hd
    rw [hd.deriv]
    ring
  rwa [hfun, hval] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual de Rham heat supertrace equals the Euler index at positive time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem hodgeHeat_supertrace (t : ℝ≥0) (ht : 0 < t) :
    2 * scalarHeatSpectralTrace d t - 2 * oneFormHeatTrace hRic d t +
      twoFormHeatSpectralTrace (o := o) hRic t = (hodgeComplexEuler g o : ℝ) := by
  rw [scalarHeatTrace_split hRic d t ht, oneFormHeatTrace_split hRic d t ht,
    twoFormHeatTrace_split hRic t ht, hodgeComplexEuler_hodge hRic]
  have hd := (smoothHarmonicSumEquiv (o := o) hRic).finrank_eq
  rw [Module.finrank_prod] at hd
  rw [← hd]
  push_cast
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every positive-time output of the actual one-form heat semigroup is smooth. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem oneFormHeat_smooth_representative (t : ℝ≥0) (ht : 0 < t) (f : OneFormL2 o) :
    ∃ u : smoothCovariantFields M 1, smoothOneFormL2Linear (o := o) u = oneFormHeat hRic d t f := by
  obtain ⟨a, ha⟩ := scalarBaseHeat_smooth_representative g o d t ht (oneFormScalarPotential hRic d f)
  let b := twoFormHeatSection hRic t ht (oneFormTwoFormPotential hRic d f)
  have hb := twoFormHeatSection_L2 hRic t ht (oneFormTwoFormPotential hRic d f)
  refine ⟨smoothScalarDifferential g a + smoothTwoFormCodifferentialField b, ?_⟩
  rw [← oneFormHeat_reconstructed hRic d t ht]
  change smoothOneFormL2Linear (o := o) (_ + _) =
    scalarH1Differential d (scalarHeatH1Lift d t ht (oneFormScalarPotential hRic d f)) +
      twoFormH1Codifferential hRic (twoFormHeatLift hRic t ht (oneFormTwoFormPotential hRic d f))
  rw [map_add, scalarHeatH1Lift_smooth d t ht _ a ha,
    twoFormHeatLift_smooth hRic t ht _ b hb.symm,
    scalarH1Differential_smooth]
  have hc := twoFormH1Codifferential_smooth hRic (b : SmoothH1TwoForm o)
  rw [hc]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual signature cokernel is represented uniquely by negative
harmonic sections. This uses smooth Hodge solvability and its integral
adjoint identity, not an index premise. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance signatureCokernelNegativeGroup : AddCommGroup (signatureNegativeSections (o := o)) :=
  Submodule.addCommGroup _
local instance signatureCokernelPositiveGroup : AddCommGroup (signaturePositiveSections (o := o)) :=
  Submodule.addCommGroup _
local instance signatureCokernelKernelGroup : AddCommGroup (SignatureNegativeKernel (o := o)) :=
  Submodule.addCommGroup _

theorem exists_signatureNegative_decomposition (hRic : RicciThree g)
    (y : signatureNegativeSections (o := o)) :
    ∃ k : SignatureNegativeKernel (o := o), ∃ x : signaturePositiveSections (o := o),
      y = k.val + signatureOperator x := by
  obtain ⟨k, hk, x, hx⟩ := exists_smoothHodge_full_decomposition hRic y.val
  have hkm : signatureOperatorOpposite (signatureMinusMap k) = 0 := by
    rw [signatureMinusMap_dirac, hk, map_zero]
  refine ⟨⟨signatureMinusMap k, hkm⟩, signaturePlusMap x, ?_⟩
  have hm := congrArg (signatureMinusMap (o := o)) hx
  rw [signatureMinusMap_self, map_add, ← signaturePlusMap_dirac] at hm
  exact hm

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem signatureNegative_exact_eq_zero (hRic : RicciThree g)
    (k : SignatureNegativeKernel (o := o))
    (hk : k.val ∈ LinearMap.range (signatureOperator (o := o))) : k = 0 := by
  obtain ⟨x, hx⟩ := hk
  have hDk : smoothHodgeDirac k.val.val = 0 := congrArg Subtype.val k.property
  have hDx : smoothHodgeDirac x.val = k.val.val := congrArg Subtype.val hx
  have he : smoothHodgePairing k.val.val k.val.val = 0 := by
    calc
      smoothHodgePairing k.val.val k.val.val =
          smoothHodgePairing (smoothHodgeDirac x.val) k.val.val := by rw [hDx]
      _ = smoothHodgePairing x.val (smoothHodgeDirac k.val.val) :=
        smoothHodgeDirac_selfAdjoint hRic _ _
      _ = 0 := by rw [hDk, smoothHodgePairing_zero_right]
  exact Subtype.ext (Subtype.ext (smoothHodgePairing_definite _ he))

abbrev SignatureCokernel :=
  signatureNegativeSections (o := o) ⧸ LinearMap.range (signatureOperator (o := o))

def signatureNegativeToCokernel :
    SignatureNegativeKernel (o := o) →ₗ[ℝ] SignatureCokernel (o := o) :=
  (LinearMap.range (signatureOperator (o := o))).mkQ.comp
    (SignatureNegativeKernel (o := o)).subtype

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem signatureNegativeToCokernel_injective (hRic : RicciThree g) :
    Function.Injective (signatureNegativeToCokernel (o := o)) := by
  intro u v huv
  have hz : signatureNegativeToCokernel (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hm : (u - v).val ∈ LinearMap.range (signatureOperator (o := o)) :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  exact sub_eq_zero.mp (signatureNegative_exact_eq_zero hRic (u - v) hm)

theorem signatureNegativeToCokernel_surjective (hRic : RicciThree g) :
    Function.Surjective (signatureNegativeToCokernel (o := o)) := by
  intro q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective
    (p := LinearMap.range (signatureOperator (o := o))) q
  obtain ⟨k, x, hx⟩ := exists_signatureNegative_decomposition hRic y
  refine ⟨k, ?_⟩
  apply (Submodule.Quotient.eq (LinearMap.range (signatureOperator (o := o)))).mpr
  change k.val - y ∈ LinearMap.range (signatureOperator (o := o))
  refine ⟨-x, ?_⟩
  rw [map_neg, hx]
  abel

def signatureCokernelEquiv (hRic : RicciThree g) :
    SignatureCokernel (o := o) ≃ₗ[ℝ] SignatureNegativeKernel (o := o) :=
  (LinearEquiv.ofBijective signatureNegativeToCokernel
    ⟨signatureNegativeToCokernel_injective hRic,
      signatureNegativeToCokernel_surjective hRic⟩).symm

theorem signatureCokernel_finite (hRic : RicciThree g) :
    FiniteDimensional ℝ (SignatureCokernel (o := o)) := by
  let _ := signatureNegativeKernel_finite (o := o) hRic
  exact FiniteDimensional.of_injective (signatureCokernelEquiv hRic).toLinearMap
    (signatureCokernelEquiv hRic).injective

theorem signatureCokernel_finrank (hRic : RicciThree g) :
    Module.finrank ℝ (SignatureCokernel (o := o)) =
      1 + Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) := by
  rw [(signatureCokernelEquiv hRic).finrank_eq, signatureNegativeKernel_finrank hRic]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Vector-valued heat and derivative series in the actual L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_series (hRic : RicciThree g) (t : ℝ≥0) (f : TwoFormL2 o) :
    HasSum (fun i : TwoFormEigenIndex (o := o) hRic =>
      (twoFormHeatWeight hRic t i.1 * inner ℝ (twoFormEigenvector hRic i) f) •
        twoFormEigenvector hRic i) (twoFormHeat hRic t f) := by
  have hs := ((twoFormEigenbasis hRic).hasSum_repr f).mapL (twoFormHeat hRic t)
  have he : (fun i : TwoFormEigenIndex (o := o) hRic =>
      twoFormHeat hRic t ((twoFormEigenbasis hRic).repr f i • twoFormEigenbasis hRic i)) =
      (fun i => (twoFormHeatWeight hRic t i.1 * inner ℝ (twoFormEigenvector hRic i) f) •
        twoFormEigenvector hRic i) := by
    funext i
    rw [map_smul, HilbertBasis.repr_apply_apply, twoFormEigenbasis_apply, twoFormHeat_eigenvector,
      smul_smul, mul_comm]
  rwa [he] at hs

theorem twoFormHeatLiftSource_eigen (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormHeatLiftSource hRic t ht (twoFormEigenvector hRic i) =
      (i.1.val⁻¹ * twoFormHeatWeight hRic t i.1) • twoFormEigenvector hRic i := by
  apply twoFormShiftedResolvent_injective hRic
  rw [twoFormHeatLiftSource_resolvent, twoFormHeat_eigenvector, map_smul]
  have he := Module.End.mem_eigenspace_iff.mp (twoFormEigenvector_hasEigenvector hRic i).1
  change twoFormShiftedResolvent hRic (twoFormEigenvector hRic i) =
    i.1.val • twoFormEigenvector hRic i at he
  rw [he, smul_smul]
  congr 1
  have hn := ne_of_gt (twoFormSpectralValue_bounds hRic i.1).1
  field_simp

def twoFormHeatDerivative (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormHeat hRic t - twoFormHeatLiftSource hRic t ht

theorem twoFormHeatDerivative_eigen (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormHeatDerivative hRic t ht (twoFormEigenvector hRic i) =
      (-twoFormHeatRate hRic i.1 * twoFormHeatWeight hRic t i.1) • twoFormEigenvector hRic i := by
  change twoFormHeat hRic t _ - twoFormHeatLiftSource hRic t ht _ = _
  rw [twoFormHeat_eigenvector, twoFormHeatLiftSource_eigen, ← sub_smul]
  congr 1
  unfold twoFormHeatRate
  ring

theorem twoFormHeatDerivative_series (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) :
    HasSum (fun i : TwoFormEigenIndex (o := o) hRic =>
      (-twoFormHeatRate hRic i.1 * twoFormHeatWeight hRic t i.1 *
        inner ℝ (twoFormEigenvector hRic i) f) • twoFormEigenvector hRic i)
      (twoFormHeatDerivative hRic t ht f) := by
  have hs := ((twoFormEigenbasis hRic).hasSum_repr f).mapL (twoFormHeatDerivative hRic t ht)
  have he : (fun i : TwoFormEigenIndex (o := o) hRic => twoFormHeatDerivative hRic t ht
      ((twoFormEigenbasis hRic).repr f i • twoFormEigenbasis hRic i)) =
      (fun i => (-twoFormHeatRate hRic i.1 * twoFormHeatWeight hRic t i.1 *
        inner ℝ (twoFormEigenvector hRic i) f) • twoFormEigenvector hRic i) := by
    funext i
    rw [map_smul, HilbertBasis.repr_apply_apply, twoFormEigenbasis_apply,
      twoFormHeatDerivative_eigen, smul_smul]
    congr 1
    ring
  rwa [he] at hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global compact parametrix has the actual initial delta pairing
against every smooth two-form. The normalized measure factor is explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalGlobalParametrixColumn_initial (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (hχ0 : χ 0 = 1) (l : Fin 6)
    (v : SmoothL2TwoForm o) :
    Tendsto (fun t => inner ℝ (heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs t l)
        (smoothTwoFormToL2 v)) (𝓝[Ioi 0] 0)
      (𝓝 ((normalizedChartFactor g).toReal *
        heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val 0 l)) := by
  let V := heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val
  let f := fun k x => frameExponentialJacobian g o e x * V x k
  have hV : ContinuousOn V C.source := by
    intro x hx
    exact (heatNormalTwoFormValue_contDiffAt 2 (v : smoothTwoForms o).property c D.point x
      (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx))).continuousAt.continuousWithinAt
  have hf (k : Fin 6) : ContinuousOn (f k) C.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      ((EuclideanSpace.proj k).continuous.comp_continuousOn hV)
  have hχf (k : Fin 6) : Continuous (fun x => χ x * f k x) :=
    heat_continuous_mul_of_tsupport_subset hχ.continuous C.open_source (hf k) hs
  have hi (t : ℝ) (k : Fin 6) :
      Integrable (fun x => heatNormalCutoffParametrix E χ t x k l * f k x) := by
    have hcont := (hχf k).mul (heatNormalBundleParametrix_space_regular E t k l).continuous
    have hint : Integrable (fun x => (χ x * f k x) *
        heatNormalBundleParametrix E t x k l) :=
      hcont.integrable_of_hasCompactSupport ((hc.mul_right).mul_right)
    convert hint using 1
    funext x
    dsimp only [heatNormalCutoffParametrix]
    ring
  have hp (t : ℝ) :
      inner ℝ (heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs t l)
        (smoothTwoFormToL2 v) =
      (normalizedChartFactor g).toReal *
        ∑ k : Fin 6, ∫ x, heatNormalCutoffParametrix E χ t x k l * f k x := by
    have hpair := heatNormalAmplitudeL2_pairing_normal D C hE hCt hP hD
      (heatNormalCutoffColumn E χ t l) (heatNormalCutoffColumn_regular E χ hχ t l)
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E χ t l))
      ((heatNormalCutoffColumn_support E χ t l).trans hs) v
    apply hpair.trans
    congr 1
    calc
      _ = ∫ x, ∑ k : Fin 6, heatNormalCutoffParametrix E χ t x k l * f k x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [PiLp.inner_apply, heatNormalCutoffColumn, f, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          change frameExponentialJacobian g o e x *
            (V x k * heatNormalCutoffParametrix E χ t x k l) =
            heatNormalCutoffParametrix E χ t x k l * (frameExponentialJacobian g o e x * V x k)
          ring
      _ = _ := integral_finsetSum _ (fun k _ => hi t k)
  have ht := (tendsto_finsetSum Finset.univ fun k _ =>
    heatNormalCutoffParametrix_initial_local E χ (f k) (hχf k) hc hχ0 k l).const_mul
      (normalizedChartFactor g).toReal
  have hz : (∑ k : Fin 6, (if k = l then 1 else 0) * f k 0) = V 0 l := by
    simp [f, frameExponentialJacobian_zero]
  rw [hz] at ht
  exact ht.congr' (Eventually.of_forall fun t => (hp t).symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Both terms of the cutoff heat residual vanish outside the spatial
support of the actual cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneCutoffParametrix_residual_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace)
    (hx : x ∉ tsupport χ) (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (k l : Fin 4) :
    deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
      fourHeatOneOperator a b B C
        (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k = 0 := by
  have hχ : χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
  have htime : (fun s => heatNormalOneCutoffParametrix E χ s x k l) = fun _ => (0 : ℝ) := by
    funext s
    simp only [heatNormalOneCutoffParametrix, hχ.self_of_nhds, zero_mul]
  have hspace (q : Fin 4) :
      (fun y => heatNormalOneCutoffParametrix E χ t y q l) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hχ] with y hy
    simp only [heatNormalOneCutoffParametrix, hy, zero_mul]
  rw [htime, deriv_const, fourHeatOneOperator_zero_of_locally_zero a b B C hspace k,
    zero_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact norm integral for the actual compact normal amplitude, obtained
by smooth approximation inside the genuine one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance heatNormalOneExactCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance heatNormalOneExactProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem heatNormalOneAmplitude_L2_realization
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) :
    oneFormFrameL2 (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ
        (heatNormalOneAmplitude D C hCt hP hD a ha hc hs) := by
  exact heatNormalOneTensor_L2_realization C hCt (heatNormalOneCoordinates D a)
    (heatNormalOneCoordinates_continuousOn D C hP hD a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneCoordinates_support D a))
    ((heatNormalOneCoordinates_support D a).trans hs)

theorem heatNormalOneAmplitudeL2_norm_sq_integral
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) :
    ‖heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs‖ ^ 2 =
      (normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ‖a x‖ ^ 2 := by
  let F := heatNormalOneAmplitude D C hCt hP hD a ha hc hs
  let ψ := fun x => ‖a x‖ ^ 2
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have hz : a x = 0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    change ‖a x‖ ^ 2 = 0
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := (ha.continuous.norm.pow 2).continuousOn
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hs)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (f : FrameBundle g) : ‖F f‖ ^ 2 = heatNormalScalarLift C ψ f.base := by
    by_cases hf : f.base ∈ C.target
    · rw [heatNormalOneAmplitude_norm_sq C hE hCt hP hD a ha hc hs f hf,
        heatNormalScalarLift_on_target C ψ hf]
    · have hz : F f = 0 := by
        change WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i]) = _
        simp only [heatNormalOneFrameLift, ite_eq_right hf]
        rfl
      rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      simp only [heatNormalScalarLift, ite_eq_right hf]
  have hex : oneFormFrameL2 (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F :=
    heatNormalOneAmplitude_L2_realization C hCt hP hD a ha hc hs
  have hcalc : ‖heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs‖ ^ 2 =
      (normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ‖a x‖ ^ 2 := by
    calc
      _ = ‖ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F‖ ^ 2 := by
        rw [← hex, oneFormFrameL2_norm]
      _ = ∫ f, ‖F f‖ ^ 2 ∂canonicalFrameMeasure g o := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F] with f hf
        rw [hf, real_inner_self_eq_norm_sq]
      _ = ∫ y, heatNormalScalarLift C ψ y ∂normalizedVolume g := by
        simp_rw [heq]
        rw [canonicalFrameMeasure_integral_base g o _ hLi]
      _ = _ := by
        rw [heatNormalScalarLift_integral D C hE hCt hP hD ψ (hψs.trans hs)]
  exact hcalc

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second-order image of a compact C4 normal amplitude is an actual
compact C2 amplitude, so it can be realized in the same global L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalOperatorAmplitude (E : HeatNormalBundleExtension D)
    (a : FourSpace → TwoFormFour) (x : FourSpace) : TwoFormFour :=
  WithLp.toLp 2 (fun k => fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
    (fun y l => a y l) x k)

theorem heatNormalOperatorAmplitude_regular (E : HeatNormalBundleExtension D)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 4 a) :
    ContDiff ℝ 2 (heatNormalOperatorAmplitude E a) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  apply fourHeatBundleOperator_contDiff 2 E.base.a E.base.b E.B E.C
  · exact fun i j => (E.base.a_regular i j).of_le (by norm_num)
  · exact fun i => (E.base.b_regular i).of_le (by norm_num)
  · exact fun i k l => (E.B_regular i k l).of_le (by norm_num)
  · exact fun k l => (E.C_regular k l).of_le (by norm_num)
  · intro l
    exact (contDiff_piLp (p := 2)).mp ha l

theorem heatNormalOperatorAmplitude_support (E : HeatNormalBundleExtension D)
    (a : FourSpace → TwoFormFour) :
    tsupport (heatNormalOperatorAmplitude E a) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport a)
  intro x hx
  by_contra hn
  have hz : a =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hn] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hk (k : Fin 6) : (fun y => a y k) =ᶠ[𝓝 x] (fun _ => 0) :=
    hz.mono fun y hy => by change a y k = 0; rw [hy]; rfl
  apply hx
  apply WithLp.ofLp_injective 2
  funext k
  exact fourHeatBundleOperator_zero_of_locally_zero (E.base.a x) (E.base.b x) (E.B x)
    (E.C x) hk k

theorem heatNormalCutoffColumn_regular_four (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (t : ℝ) (l : Fin 6) :
    ContDiff ℝ 4 (heatNormalCutoffColumn E χ t l) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  have hP := (((E.amplitude_regular 0 (by omega) k l).add
    ((contDiff_const (c := t)).mul (E.amplitude_regular 1 (by omega) k l))).add
    ((contDiff_const (c := t ^ 2)).mul (E.amplitude_regular 2 (by omega) k l))).add
    ((contDiff_const (c := t ^ 3)).mul (E.amplitude_regular 3 (by omega) k l))
  exact hχ.mul (((fourHeatGaussian_smooth t).of_le (by norm_num)).mul hP)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative of the actual compact normal kernel under one
scalar pairing; only the cutoff-weighted test must be continuous. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCutoffParametrix_pairing_deriv (E : HeatNormalBundleExtension D)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hc : HasCompactSupport χ) (t : ℝ) (ht : 0 < t) (k l : Fin 6) :
    HasDerivAt (fun s => ∫ x, heatNormalCutoffParametrix E χ s x k l * f x)
      (∫ x, deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t * f x) t := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => E.amplitude m x k l
  have h := fourHeat_compact_polynomial_pairing_deriv (fun x => χ x * f x) hχf hc.mul_right
    u (fun m => (E.amplitude_regular m (by omega) k l).continuous) t ht
  have hfun : (fun s => ∫ x, (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x)) =
      fun s => ∫ x, heatNormalCutoffParametrix E χ s x k l * f x := by
    funext s
    apply integral_congr_ae
    filter_upwards [] with x
    change (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x) =
      (χ x * (fourHeatGaussian s x * fourHeatPolynomial u s x)) * f x
    ring
  have hval : (∫ x, (χ x * f x) * fourHeatGaussianPolynomialTime u t x) =
      ∫ x, deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t * f x := by
    apply integral_congr_ae
    filter_upwards [] with x
    have hd := (fourHeatGaussianPolynomial_hasDerivAt u t ht x).const_mul (χ x)
    change HasDerivAt (fun s => heatNormalCutoffParametrix E χ s x k l)
      (χ x * fourHeatGaussianPolynomialTime u t x) t at hd
    rw [hd.deriv]
    ring
  rwa [hfun, hval] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded continuous evaluation of actual positive-time one-form heat. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
  (t : ℝ≥0) (ht : 0 < t)

def oneFormHeatC0Value (f : OneFormL2 o) : OneFormC0 g :=
  ⟨smoothOneFormEuclideanValue (g := g) (oneFormHeat_smooth_representative hRic d t ht f).choose,
    Submodule.le_topologicalClosure _ ⟨(oneFormHeat_smooth_representative hRic d t ht f).choose, rfl⟩⟩

theorem oneFormHeatC0Value_L2 (f : OneFormL2 o) :
    oneFormC0ToFrameLp (o := o) (oneFormHeatC0Value hRic d t ht f) =
      oneFormFrameL2 (oneFormHeat hRic d t f) := by
  change ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ
    (smoothOneFormEuclideanValue (g := g) _) = _
  rw [← oneFormFrameL2_smooth]
  exact congrArg oneFormFrameL2 (oneFormHeat_smooth_representative hRic d t ht f).choose_spec

def oneFormHeatC0Linear : OneFormL2 o →ₗ[ℝ] OneFormC0 g where
  toFun := oneFormHeatC0Value hRic d t ht
  map_add' f v := by
    apply oneFormC0ToFrameLp_injective (o := o)
    rw [map_add, oneFormHeatC0Value_L2, oneFormHeatC0Value_L2, oneFormHeatC0Value_L2,
      map_add, map_add]
  map_smul' r f := by
    apply oneFormC0ToFrameLp_injective (o := o)
    rw [map_smul, oneFormHeatC0Value_L2, oneFormHeatC0Value_L2, map_smul, map_smul]
    rfl

theorem oneFormHeatC0_graph_closed : IsClosed ((oneFormHeatC0Linear hRic d t ht).graph :
    Set (OneFormL2 o × OneFormC0 g)) := by
  have he : ((oneFormHeatC0Linear hRic d t ht).graph : Set (OneFormL2 o × OneFormC0 g)) =
      {p | oneFormC0ToFrameLp (o := o) p.2 = oneFormFrameL2 (oneFormHeat hRic d t p.1)} := by
    ext p
    change p.2 = oneFormHeatC0Value hRic d t ht p.1 ↔
      oneFormC0ToFrameLp (o := o) p.2 = oneFormFrameL2 (oneFormHeat hRic d t p.1)
    constructor
    · intro hp
      rw [hp]
      exact oneFormHeatC0Value_L2 hRic d t ht p.1
    · intro hp
      apply oneFormC0ToFrameLp_injective (o := o)
      exact hp.trans (oneFormHeatC0Value_L2 hRic d t ht p.1).symm
  rw [he]
  exact isClosed_eq (oneFormC0ToFrameLp.continuous.comp continuous_snd)
    (oneFormFrameL2.continuous.comp ((oneFormHeat hRic d t).continuous.comp continuous_fst))

theorem oneFormHeatC0_continuous : Continuous (oneFormHeatC0Linear hRic d t ht) := by
  exact @LinearMap.continuous_of_isClosed_graph ℝ _ (OneFormL2 o) _ _ _
    (OneFormC0 g) _ _ _ (oneFormHeatC0Linear hRic d t ht)
    (oneFormHeatC0_graph_closed hRic d t ht)

def oneFormHeatToC0 : OneFormL2 o →L[ℝ] OneFormC0 g where
  toLinearMap := oneFormHeatC0Linear hRic d t ht
  cont := oneFormHeatC0_continuous hRic d t ht

def oneFormHeatToContinuous : OneFormL2 o →L[ℝ] C(FrameBundle g, FourSpace) :=
  (oneFormContinuousSubspace g).subtypeL.comp (oneFormHeatToC0 hRic d t ht)

theorem oneFormHeatToContinuous_bound (f : OneFormL2 o) (e : FrameBundle g) :
    ‖oneFormHeatToContinuous hRic d t ht f e‖ ≤ ‖oneFormHeatToContinuous hRic d t ht‖ * ‖f‖ :=
  (ContinuousMap.norm_coe_le_norm _ e).trans ((oneFormHeatToContinuous hRic d t ht).le_opNorm f)

theorem oneFormHeatToContinuous_smooth (f : OneFormL2 o) (u : smoothCovariantFields M 1)
    (hu : smoothOneFormL2Linear (o := o) u = oneFormHeat hRic d t f) :
    oneFormHeatToContinuous hRic d t ht f = smoothOneFormEuclideanValue (g := g) u := by
  have he := (oneFormHeat_smooth_representative hRic d t ht f).choose_spec
  have hs := smoothOneFormL2Linear_injective (he.trans hu.symm)
  change smoothOneFormEuclideanValue (g := g) _ = _
  rw [hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The index of the actual smooth signature operator is the signature
of the actual degree-two de Rham intersection form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance signatureIndexPositiveGroup : AddCommGroup (signaturePositiveSections (o := o)) :=
  Submodule.addCommGroup _
local instance signatureIndexNegativeGroup : AddCommGroup (signatureNegativeSections (o := o)) :=
  Submodule.addCommGroup _
local instance signatureIndexKernelGroup : AddCommGroup (SignaturePositiveKernel (o := o)) :=
  Submodule.addCommGroup _

theorem signatureOperator_finite_kernel_cokernel (hRic : RicciThree g) :
    FiniteDimensional ℝ (SignaturePositiveKernel (o := o)) ∧
      FiniteDimensional ℝ (SignatureCokernel (o := o)) :=
  ⟨signaturePositiveKernel_finite hRic, signatureCokernel_finite hRic⟩

theorem signatureOperator_index (hRic : RicciThree g) :
    (signatureOperator (o := o)).index =
      (Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) : ℤ) -
      (Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) : ℤ) := by
  rw [LinearMap.index_eq_finrank_sub]
  change (Module.finrank ℝ (SignaturePositiveKernel (o := o)) : ℤ) -
    (Module.finrank ℝ (SignatureCokernel (o := o)) : ℤ) = _
  rw [signaturePositiveKernel_finrank hRic, signatureCokernel_finrank hRic]
  push_cast
  ring

theorem signatureOperator_index_eq_signature (hRic : RicciThree g) :
    (signatureOperator (o := o)).index = deRhamSignature (o := o) hRic := by
  rw [signatureOperator_index hRic, deRhamSignature_hodge hRic]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Summable, locally uniform bounds for differentiating the actual
positive-time spectral heat series. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_rate_weight_summable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    Summable (fun i : TwoFormEigenIndex (o := o) hRic =>
      twoFormHeatRate hRic i.1 * twoFormHeatWeight hRic t i.1) := by
  have ht2 := half_pos ht
  apply Summable.of_nonneg_of_le (fun i => mul_nonneg (twoFormHeatRate_nonneg hRic i.1)
    (Real.exp_pos _).le) _
    ((twoFormHeat_weight_summable (o := o) hRic (t / 2) ht2).mul_left
      (Real.exp (t / 2 : ℝ≥0) / (t / 2 : ℝ≥0)))
  intro i
  have hw : 0 ≤ twoFormHeatWeight hRic (t / 2) i.1 := (Real.exp_pos _).le
  have hm : 0 ≤ i.1.val⁻¹ := (inv_pos.mpr (twoFormSpectralValue_bounds hRic i.1).1).le
  have hb := twoFormHeatLiftWeight_bound hRic (t / 2) ht2 i.1
  rw [abs_of_nonneg (mul_nonneg hm hw)] at hb
  calc
    _ = twoFormHeatRate hRic i.1 * twoFormHeatWeight hRic (t / 2) i.1 ^ 2 :=
      congrArg (twoFormHeatRate hRic i.1 * ·) (twoFormHeatWeight_half_sq hRic t i.1).symm
    _ = (twoFormHeatRate hRic i.1 * twoFormHeatWeight hRic (t / 2) i.1) *
        twoFormHeatWeight hRic (t / 2) i.1 := by ring
    _ ≤ (i.1.val⁻¹ * twoFormHeatWeight hRic (t / 2) i.1) *
        twoFormHeatWeight hRic (t / 2) i.1 := by
      apply mul_le_mul_of_nonneg_right _ hw
      apply mul_le_mul_of_nonneg_right _ hw
      unfold twoFormHeatRate
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hb hw

def twoFormHeatRealTerm (hRic : RicciThree g) (f : TwoFormL2 o)
    (i : TwoFormEigenIndex (o := o) hRic) (s : ℝ) : TwoFormL2 o :=
  (Real.exp (-s * twoFormHeatRate hRic i.1) * inner ℝ (twoFormEigenvector hRic i) f) •
    twoFormEigenvector hRic i

def twoFormHeatRealDerivativeTerm (hRic : RicciThree g) (f : TwoFormL2 o)
    (i : TwoFormEigenIndex (o := o) hRic) (s : ℝ) : TwoFormL2 o :=
  (-twoFormHeatRate hRic i.1 * Real.exp (-s * twoFormHeatRate hRic i.1) *
    inner ℝ (twoFormEigenvector hRic i) f) • twoFormEigenvector hRic i

theorem twoFormHeatRealDerivativeTerm_bound (hRic : RicciThree g) (ε : ℝ≥0)
    (f : TwoFormL2 o) (i : TwoFormEigenIndex (o := o) hRic) (s : ℝ) (hs : ε ≤ s) :
    ‖twoFormHeatRealDerivativeTerm hRic f i s‖ ≤
      (twoFormHeatRate hRic i.1 * twoFormHeatWeight hRic ε i.1) * ‖f‖ := by
  have hr := twoFormHeatRate_nonneg hRic i.1
  have hc : ‖inner ℝ (twoFormEigenvector hRic i) f‖ ≤ ‖f‖ := by
    simpa only [(twoFormEigenvector_orthonormal hRic).1 i, one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (twoFormEigenvector hRic i) f
  have hw : Real.exp (-s * twoFormHeatRate hRic i.1) ≤ twoFormHeatWeight hRic ε i.1 := by
    apply Real.exp_le_exp.mpr
    nlinarith
  simp only [twoFormHeatRealDerivativeTerm, norm_smul, norm_mul,
    Real.norm_eq_abs, abs_neg, abs_of_nonneg hr, abs_of_pos (Real.exp_pos _),
    (twoFormEigenvector_orthonormal hRic).1 i, mul_one]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hw hr) hc (abs_nonneg _)
    (mul_nonneg hr (Real.exp_pos _).le)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-frame coefficients satisfy every hypothesis of
the finite-regularity Green identity on a proved neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.potential_symmetric (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (k l : Fin 6) :
    heatNormalPotential g c D.point x k l = heatNormalPotential g c D.point x l k := by
  have hR : ∀ i j a b, twoFormMetricCurvatureTensor g (D.frame x hx) ![a,b,i,j] =
      twoFormMetricCurvatureTensor g (D.frame x hx) ![i,j,a,b] := by
    intro i j a b
    change frameTensor (D.frame x hx).frame.matrix _ ![a,b,i,j] =
      frameTensor (D.frame x hx).frame.matrix _ ![i,j,a,b]
    rw [frameTensor_curvatureCoordinates, frameTensor_curvatureCoordinates]
    exact frame_algebraic_pairSymmetric (D.frame x hx).frame
      (frame_algebraic_lastSkew (D.frame x hx).frame) i j a b
  have hC := twoFormCurvatureMatrix_symmetric (twoFormMetricCurvatureTensor g (D.frame x hx)) hR
  have hP : (twoFormPotentialMatrix (twoFormMetricCurvatureTensor g (D.frame x hx)))ᵀ =
      twoFormPotentialMatrix (twoFormMetricCurvatureTensor g (D.frame x hx)) := by
    simp only [twoFormPotentialMatrix, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, hC]
  rw [D.potential_as_actual x hx]
  exact (congrArg (fun A : TwoFormMatrix => A k l) hP).symm

theorem HeatNormalFrameData.green_regular_near (D : HeatNormalFrameData g o c e) :
    ∀ᶠ x in 𝓝 (0 : FourSpace),
      (∀ i k l, ContDiffAt ℝ 1 (fun y => heatTwoFormConnection g c D.point i y k l) x) ∧
      (∀ i j, ContDiffAt ℝ 1 (fun y => (heatNormalMetric g o e y)⁻¹ i j) x) ∧
      ContDiffAt ℝ 1 (frameExponentialJacobian g o e) x ∧
      0 < frameExponentialJacobian g o e x ∧
      (∀ k l, ContinuousAt (fun y => heatNormalPotential g c D.point y k l) x) := by
  have hA := eventually_all.mpr fun i => eventually_all.mpr fun k =>
    eventually_all.mpr fun l => ((D.twoForm_connection_regular i k l).of_le
      (show (1 : ℕ∞ω) ≤ 11 by norm_num)).eventually (by norm_num)
  have ha := eventually_all.mpr fun i => eventually_all.mpr fun j =>
    ((heatNormalInverse_smoothAt_zero g o e i j).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)
  have hρ := ((frameExponentialJacobian_smoothAt_zero g o e).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)
  have hV := eventually_all.mpr fun k => eventually_all.mpr fun l =>
    ((D.potential_regular k l).of_le (show (1 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  filter_upwards [hA, ha, hρ, frameExponentialJacobian_eventually_pos g o e, hV]
    with x hxA hxa hxρ hxpos hxV
  exact ⟨hxA, hxa, hxρ, hxpos, fun k l => (hxV k l).continuousAt⟩

theorem HeatNormalBundleExtension.connection_operator_near
    {D : HeatNormalFrameData g o c e} (E : HeatNormalBundleExtension D) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ u : FourSpace → Fin 6 → ℝ,
      (∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) → ∀ k,
      fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x) u x k =
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) u x k := by
  filter_upwards [E.base.a_near, E.base.b_near, E.B_near, E.C_near, D.green_regular_near]
    with x ha hb hB hC hreg
  intro u hu k
  rw [ha, hb, hB, hC]
  exact (heatNormalConnectionOperator_eq D u x
    (fun i k l => (hreg.1 i k l).differentiableAt one_ne_zero) hu k).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compactly supported actual normal parametrix whose full residual
is uniformly O(t), including the annulus where the cutoff varies. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneCutoffParametrix_bound_of_support {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ R > (0 : ℝ), ∀ (χ : FourSpace → ℝ), ContDiff ℝ 2 χ → HasCompactSupport χ →
      tsupport χ ⊆ ball 0 R → (∀ x, |χ x| ≤ 1) →
      ∀ r > (0 : ℝ), (∀ x ∈ ball 0 r, χ x = 1) →
      ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
        |deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
          fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
            (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k| ≤ C * t := by
  obtain ⟨R₀, hR₀, C₀, hC₀, hbound⟩ :=
    heatNormalOneParametrix_residual_uniform_linear E hRic he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ ball 0 R₀ ∧
      E.base.a x = (heatNormalMetric g o e x)⁻¹ ∧ E.base.b x = heatNormalDrift g o e x ∧
      E.B x = heatNormalOneFirst D x ∧ E.C x = heatNormalOneZero D x := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) hR₀, E.base.a_near, E.base.b_near,
      E.B_near, E.C_near] with x hx ha hb hB hC
    exact ⟨hx, ha, hb, hB, hC⟩
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨R, hR, ?_⟩
  intro χ hχ hχc hχs hχb r hr hinner
  let u (l : Fin 4) : Fin 4 → FourSpace → Fin 4 → ℝ := fun m y q => E.amplitude m y q l
  have hu (l : Fin 4) (m : Fin 4) (q : Fin 4) : ContDiff ℝ 2 (fun y => u l m y q) :=
    (E.amplitude_regular m (by omega) q l).of_le (by norm_num)
  have herror (l : Fin 4) := fourHeatOneScaledCommutator_gaussian_bound
    E.base.a E.base.b E.B χ (u l)
    (fun i j => (E.base.a_regular i j).continuous)
    (fun i => (E.base.b_regular i).continuous)
    (fun i k q => (E.B_regular i k q).continuous)
    hχ hχc (hu l) r hr hinner
  choose C₁ hC₁ herror using herror
  refine ⟨C₀ + ∑ l, C₁ l, add_nonneg hC₀ (Finset.sum_nonneg fun l _ => hC₁ l), ?_⟩
  intro t ht x k l
  by_cases hx : x ∈ tsupport χ
  · obtain ⟨hx₀, ha, hb, hB, hC⟩ := hball (hχs hx)
    have hsym (i j : Fin 4) : E.base.a x i j = E.base.a x j i := by
      rw [ha]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    let Q := deriv (fun s => heatNormalOneParametrix E s x k l) t +
      fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalOneParametrix E t y q l) x k
    have hQ : |Q| ≤ C₀ * t := by
      dsimp only [Q]
      rw [ha, hb, hB, hC]
      exact hbound x hx₀ t ht.1 k l
    have hid := heatNormalOneCutoffParametrix_residual_identity E χ t ht.1 x hχ.contDiffAt
      (E.base.a x) (E.base.b x) (E.B x) (E.C x) hsym k l
    have hscaled := fourHeatOneScaledCommutator_identity E.base.a E.base.b E.B χ (u l)
      (hu l) t ht.1 x k
    have hid' : deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
        fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k =
        χ x * Q + (fourHeatGaussian t x / t) *
          fourHeatOneScaledCommutator E.base.a E.base.b E.B χ (u l) t x k := by
      rw [← hscaled, hid]
      dsimp only [Q, heatNormalOneParametrix, u]
      ring
    rw [hid']
    have hCl : C₁ l ≤ ∑ q, C₁ q :=
      Finset.single_le_sum (fun q _ => hC₁ q) (Finset.mem_univ l)
    calc
      _ ≤ |χ x * Q| + |(fourHeatGaussian t x / t) *
          fourHeatOneScaledCommutator E.base.a E.base.b E.B χ (u l) t x k| := abs_add_le _ _
      _ ≤ C₀ * t + C₁ l * t := by
        apply add_le_add _ (herror l t ht x k)
        rw [abs_mul]
        exact (mul_le_mul (hχb x) hQ (abs_nonneg Q) (by norm_num)).trans_eq (one_mul _)
      _ ≤ (C₀ + ∑ q, C₁ q) * t := by
        nlinarith [mul_le_mul_of_nonneg_right hCl ht.1.le]
  · rw [heatNormalOneCutoffParametrix_residual_zero E χ t x hx]
    rw [abs_zero]
    exact mul_nonneg (add_nonneg hC₀ (Finset.sum_nonneg fun q _ => hC₁ q)) ht.1.le

theorem heatNormalOneCutoffParametrix_bound {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ (R : ℝ) (hR : 0 < R), ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
      |deriv (fun s => heatNormalOneCutoffParametrix E (heatNormalChartBump R hR) s x k l) t +
        fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => heatNormalOneCutoffParametrix E (heatNormalChartBump R hR) t y q l) x k| ≤
        C * t := by
  obtain ⟨R, hR, h⟩ := heatNormalOneCutoffParametrix_bound_of_support E hRic he
  refine ⟨R, hR, ?_⟩
  apply h (heatNormalChartBump R hR) (heatNormalChartBump R hR).contDiff
    (heatNormalChartBump R hR).hasCompactSupport
  · rw [(heatNormalChartBump R hR).tsupport_eq]
    exact closedBall_subset_ball (by change R / 2 < R; linarith)
  · intro x
    rw [abs_of_nonneg (heatNormalChartBump R hR).nonneg]
    exact (heatNormalChartBump R hR).le_one
  · exact div_pos hR (by norm_num : (0 : ℝ) < 4)
  · intro x hx
    exact (heatNormalChartBump R hR).one_of_mem_closedBall (ball_subset_closedBall hx)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual time derivative column is a compact C2 normal amplitude
and therefore determines a section of the same global L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalTimeColumn (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 6) (x : FourSpace) : TwoFormFour :=
  WithLp.toLp 2 (fun k => χ x * fourHeatGaussianPolynomialTime
    (fun m y => E.amplitude m y k l) t x)

theorem heatNormalTimeColumn_component (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (l k : Fin 6) (x : FourSpace) :
    heatNormalTimeColumn E χ t l x k =
      deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t :=
  ((fourHeatGaussianPolynomial_hasDerivAt (fun m y => E.amplitude m y k l) t ht x).const_mul
    (χ x)).deriv.symm

theorem heatNormalTimeColumn_regular (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (t : ℝ) (l : Fin 6) :
    ContDiff ℝ 2 (heatNormalTimeColumn E χ t l) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  have hu (m : Fin 4) : ContDiff ℝ 2 (fun y => E.amplitude m y k l) :=
    (E.amplitude_regular m (by omega) k l).of_le (by norm_num)
  have hQ : ContDiff ℝ 2 (fun x => fourHeatPolynomialTime (fun m y => E.amplitude m y k l) t x) :=
    ((hu 1).add ((contDiff_const (c := 2 * t)).mul (hu 2))).add
      ((contDiff_const (c := 3 * t ^ 2)).mul (hu 3))
  have hF : ContDiff ℝ 2 (fourHeatGaussianTimeFactor t) :=
    ((contDiff_norm_sq ℝ).div_const (4 * t ^ 2)).sub contDiff_const
  have hG : ContDiff ℝ 2 (fourHeatGaussian t) := (fourHeatGaussian_smooth t).of_le (by norm_num)
  exact hχ.mul (((hF.mul hG).mul (fourHeatPolynomial_contDiff _ hu t)).add (hG.mul hQ))

theorem heatNormalTimeColumn_support (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) :
    tsupport (heatNormalTimeColumn E χ t l) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have hχ : χ x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  apply WithLp.ofLp_injective 2
  funext k
  simp only [heatNormalTimeColumn, WithLp.ofLp_toLp, hχ, zero_mul, WithLp.ofLp_zero,
    Pi.zero_apply]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalGlobalTimeColumn (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalAmplitudeL2 D C hCt hP hD (heatNormalTimeColumn E χ t l)
    (heatNormalTimeColumn_regular E χ hχ t l)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalTimeColumn_support E χ t l))
    ((heatNormalTimeColumn_support E χ t l).trans hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Correct normalization of the compact parametrix for the actual
probability measure used by the spectral Hodge heat kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.value_zero (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) (u : M → TwoFormFour) :
    heatNormalTwoFormValue o c D.point u 0 = twoFormFrameValue o u e := by
  apply twoFormTensor_injective
  rw [heatNormalTwoFormValue_tensor, ← twoFormFramedValue_eq, D.initial]
  exact (heat_framedValue_chart o u c e he).symm

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {D : HeatNormalFrameData g o c e}

def heatNormalizedParametrixColumn (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  ((normalizedChartFactor g).toReal)⁻¹ •
    heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs t l

theorem heatNormalizedParametrixColumn_initial (E : HeatNormalBundleExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (hχ0 : χ 0 = 1) (l : Fin 6)
    (v : SmoothL2TwoForm o) :
    Tendsto (fun t => inner ℝ (heatNormalizedParametrixColumn E C hCt hP hD χ hχ hc hs t l)
        (smoothTwoFormToL2 v)) (𝓝[Ioi 0] 0)
      (𝓝 (twoFormFrameValue o (v : smoothTwoForms o).val e l)) := by
  have h0 := heatNormalGlobalParametrixColumn_initial E C hE hCt hP hD χ hχ hc hs hχ0 l v
  have h := h0.const_mul ((normalizedChartFactor g).toReal)⁻¹
  have hn : (normalizedChartFactor g).toReal ≠ 0 := (normalizedChartFactor_toReal_pos g).ne'
  rw [D.value_zero he, ← mul_assoc, inv_mul_cancel₀ hn, one_mul] at h
  simpa only [heatNormalizedParametrixColumn, real_inner_smul_left] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Genuine L2 Riesz columns for one-form heat evaluation in an orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormEigenSection (i : OneFormEigenIndex hRic d) : smoothCovariantFields M 1 :=
  (oneFormEigenvector_smooth hRic d i).choose

omit [PreconnectedSpace M] in
theorem oneFormEigenSection_L2 (i : OneFormEigenIndex hRic d) :
    smoothOneFormL2Linear (o := o) (oneFormEigenSection hRic d i) = oneFormEigenvector hRic d i :=
  (oneFormEigenvector_smooth hRic d i).choose_spec.1.symm

def oneFormHeatEvaluation (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l : Fin 4) :
    OneFormL2 o →L[ℝ] ℝ :=
  (EuclideanSpace.proj l).comp ((ContinuousMap.evalCLM ℝ e).comp (oneFormHeatToContinuous hRic d t ht))

def oneFormHeatFrameColumn (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l : Fin 4) : OneFormL2 o :=
  (InnerProductSpace.toDual ℝ (OneFormL2 o)).symm (oneFormHeatEvaluation hRic d t ht e l)

theorem oneFormHeatFrameColumn_pairing (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 4) (f : OneFormL2 o) :
    inner ℝ (oneFormHeatFrameColumn hRic d t ht e l) f = oneFormHeatToContinuous hRic d t ht f e l :=
  InnerProductSpace.toDual_symm_apply

theorem oneFormHeatFrameColumn_norm (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) (l : Fin 4) :
    ‖oneFormHeatFrameColumn hRic d t ht e l‖ ≤ ‖oneFormHeatToContinuous hRic d t ht‖ := by
  rw [oneFormHeatFrameColumn, LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound (oneFormHeatEvaluation hRic d t ht e l)
    (norm_nonneg (oneFormHeatToContinuous hRic d t ht))
  intro f
  change |oneFormHeatToContinuous hRic d t ht f e l| ≤ _
  exact (PiLp.norm_apply_le _ l).trans (oneFormHeatToContinuous_bound hRic d t ht f e)

theorem oneFormHeatContinuous_eigen (t : ℝ≥0) (ht : 0 < t) (i : OneFormEigenIndex hRic d) :
    oneFormHeatToContinuous hRic d t ht (oneFormEigenvector hRic d i) =
      oneFormHeatWeight hRic d t i • smoothOneFormEuclideanValue (g := g) (oneFormEigenSection hRic d i) := by
  have hu : smoothOneFormL2Linear (o := o) (oneFormHeatWeight hRic d t i • oneFormEigenSection hRic d i) =
      oneFormHeat hRic d t (oneFormEigenvector hRic d i) := by
    rw [map_smul, oneFormEigenSection_L2, oneFormHeat_eigenvector]
  have he := oneFormHeatToContinuous_smooth hRic d t ht _ _ hu
  rw [he]
  exact (smoothOneFormContinuousLinear (g := g)).map_smul _ _

theorem oneFormHeatFrameColumn_eigen (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 4) (i : OneFormEigenIndex hRic d) :
    inner ℝ (oneFormHeatFrameColumn hRic d t ht e l) (oneFormEigenvector hRic d i) =
      oneFormHeatWeight hRic d t i * covariantFieldFramed g (oneFormEigenSection hRic d i).val e ![l] := by
  rw [oneFormHeatFrameColumn_pairing, oneFormHeatContinuous_eigen]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual positive-time heat operator is differentiable in L2. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped Manifold ContDiff NNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatRealTerm_derivative (hRic : RicciThree g) (f : TwoFormL2 o)
    (i : TwoFormEigenIndex (o := o) hRic) (s : ℝ) :
    HasDerivAt (twoFormHeatRealTerm hRic f i) (twoFormHeatRealDerivativeTerm hRic f i s) s := by
  have hx : HasDerivAt (fun x : ℝ => -x * twoFormHeatRate hRic i.1)
      (-twoFormHeatRate hRic i.1) s := by
    simpa only [neg_mul, one_mul, Pi.neg_apply, id_eq] using
      (hasDerivAt_id s).neg.mul_const (twoFormHeatRate hRic i.1)
  have hd := ((hx.exp).mul_const (inner ℝ (twoFormEigenvector hRic i) f)).smul_const
    (twoFormEigenvector hRic i)
  convert hd using 1
  · rfl
  · change (-twoFormHeatRate hRic i.1 * Real.exp (-s * twoFormHeatRate hRic i.1) *
      inner ℝ (twoFormEigenvector hRic i) f) • twoFormEigenvector hRic i =
      (Real.exp (-s * twoFormHeatRate hRic i.1) * -twoFormHeatRate hRic i.1 *
        inner ℝ (twoFormEigenvector hRic i) f) • twoFormEigenvector hRic i
    congr 1
    ring

theorem twoFormHeatRealTerm_hasSum (hRic : RicciThree g) (f : TwoFormL2 o)
    (s : ℝ) (hs : 0 ≤ s) :
    HasSum (fun i => twoFormHeatRealTerm hRic f i s) (twoFormHeat hRic s.toNNReal f) := by
  simpa only [twoFormHeatRealTerm, twoFormHeatWeight, Real.coe_toNNReal s hs] using
    twoFormHeat_series hRic s.toNNReal f

theorem twoFormHeat_hasDerivAt (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) :
    HasDerivAt (fun s : ℝ => twoFormHeat hRic s.toNNReal f)
      (twoFormHeatDerivative hRic t ht f) (t : ℝ) := by
  let ε : ℝ≥0 := t / 2
  have hε : (ε : ℝ) < (t : ℝ) := half_lt_self ht
  have hε0 : 0 < ε := half_pos ht
  have hs : Summable (fun i => twoFormHeatRealTerm hRic f i (t : ℝ)) := by
    exact (twoFormHeatRealTerm_hasSum hRic f t t.coe_nonneg).summable
  have hd := hasDerivAt_tsum_of_isPreconnected
    ((twoFormHeat_rate_weight_summable (o := o) hRic ε hε0).mul_right ‖f‖)
    isOpen_Ioi isPreconnected_Ioi
    (fun i s _ => twoFormHeatRealTerm_derivative hRic f i s)
    (fun i s hs => twoFormHeatRealDerivativeTerm_bound hRic ε f i s hs.le)
    hε hs hε
  have hD : (∑' i, twoFormHeatRealDerivativeTerm hRic f i (t : ℝ)) =
      twoFormHeatDerivative hRic t ht f := by
    exact (twoFormHeatDerivative_series hRic t ht f).tsum_eq
  rw [hD] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds (show (0 : ℝ) < t from ht)] with s hs
  exact (twoFormHeatRealTerm_hasSum hRic f s hs.le).tsum_eq.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The extended bundle operator is the genuine normal covariant
operator on every compact amplitude supported in its agreement region. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem heatAmplitude_component_support (a : FourSpace → TwoFormFour) (k : Fin 6) :
    tsupport (fun x => a x k) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  contrapose! hx
  apply Function.notMem_support.mpr
  rw [Function.notMem_support.mp hx]
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.compact_operator_eq
    (E : HeatNormalBundleExtension D) (U : Set FourSpace)
    (hU : ∀ x ∈ U, ∀ u : FourSpace → Fin 6 → ℝ,
      (∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) → ∀ k,
      fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x) u x k =
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) u x k)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a)
    (hs : tsupport a ⊆ U) (x : FourSpace) (k : Fin 6) :
    heatNormalOperatorAmplitude E a x k =
      fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x)
        (fun y l => a y l) x k := by
  by_cases hx : x ∈ U
  · exact hU x hx (fun y l => a y l)
      (fun l => ((contDiff_piLp (p := 2)).mp ha l).contDiffAt) k
  · have hz : ∀ l, (fun y => a y l) =ᶠ[𝓝 x] (fun _ => 0) := by
      intro l
      have hn : x ∉ tsupport a := fun h => hx (hs h)
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hn] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy]
      rfl
    change fourHeatBundleOperator _ _ _ _ _ x k = _
    rw [fourHeatBundleOperator_zero_of_locally_zero _ _ _ _ hz,
      fourHeatCovariantOperator_zero_of_locally_zero _ _ _ _ hz]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint positive-time regularity of the actual cutoff normal kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

theorem fourHeatGaussian_joint_contDiffAt (z : ℝ × FourSpace) (ht : 0 < z.1) :
    ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => fourHeatGaussian w.1 w.2) z := by
  have hP : ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => ((4 * Real.pi * w.1) ^ 2)⁻¹) z :=
    ((contDiffAt_const.mul contDiffAt_fst).pow 2).inv
      (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht.ne'))
  have hN : ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => ‖w.2‖ ^ 2) z :=
    (contDiff_norm_sq ℝ).contDiffAt.comp z contDiffAt_snd
  have hE : ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => -(4 * w.1)⁻¹ * ‖w.2‖ ^ 2) z :=
    (((contDiffAt_const.mul contDiffAt_fst).inv (mul_ne_zero (by norm_num) ht.ne')).neg).mul hN
  exact hP.mul hE.exp

theorem fourHeatPolynomial_joint_contDiff (u : Fin 4 → FourSpace → ℝ)
    (hu : ∀ m, ContDiff ℝ 2 (u m)) :
    ContDiff ℝ 2 (fun z : ℝ × FourSpace => fourHeatPolynomial u z.1 z.2) := by
  have h (m : Fin 4) : ContDiff ℝ 2 (fun z : ℝ × FourSpace => u m z.2) :=
    (hu m).comp contDiff_snd
  exact (((h 0).add (contDiff_fst.mul (h 1))).add
    ((contDiff_fst.pow 2).mul (h 2))).add ((contDiff_fst.pow 3).mul (h 3))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCutoffParametrix_joint_contDiffAt (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (z : ℝ × FourSpace) (ht : 0 < z.1)
    (k l : Fin 6) :
    ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => heatNormalCutoffParametrix E χ w.1 w.2 k l) z := by
  have hu (m : Fin 4) : ContDiff ℝ 2 (fun x => E.amplitude m x k l) :=
    (E.amplitude_regular m (by omega) k l).of_le (by norm_num)
  exact ((hχ.comp contDiff_snd).contDiffAt).mul
    ((fourHeatGaussian_joint_contDiffAt z ht).mul
      (fourHeatPolynomial_joint_contDiff _ hu).contDiffAt)

theorem heatNormalTimeColumn_joint_continuousOn (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 6) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalTimeColumn E χ z.1 l z.2)
      (Ioi 0 ×ˢ univ) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro k
  exact (hχ.comp continuous_snd).continuousOn.mul
    (fourHeatGaussianPolynomialTime_continuousOn _
      (fun m => (E.amplitude_regular m (by omega) k l).continuous))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Genuine normal one-form coefficients on one common Green-identity neighborhood. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.oneGreen_regular_near (D : HeatNormalFrameData g o c e) :
    ∀ᶠ x in 𝓝 (0 : FourSpace),
      (∀ i k l, ContDiffAt ℝ 1 (fun y => heatNormalFrameConnection g c D.point i y k l) x) ∧
      (∀ i j, ContDiffAt ℝ 1 (fun y => (heatNormalMetric g o e y)⁻¹ i j) x) ∧
      ContDiffAt ℝ 1 (frameExponentialJacobian g o e) x ∧
      0 < frameExponentialJacobian g o e x := by
  have hA := eventually_all.mpr fun i => eventually_all.mpr fun k =>
    eventually_all.mpr fun l => ((D.connection_regular i k l).of_le
      (show (1 : ℕ∞ω) ≤ 11 by norm_num)).eventually (by norm_num)
  filter_upwards [hA, D.green_regular_near] with x hxA hx
  exact ⟨hxA, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩

theorem HeatNormalOneExtension.connection_operator_near
    {D : HeatNormalFrameData g o c e} (E : HeatNormalOneExtension D) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ u : FourSpace → Fin 4 → ℝ,
      (∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) → ∀ k,
      fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x) u x k =
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c D.point) ((3 : ℝ) • (1 : Mat4)) u x k := by
  filter_upwards [E.base.a_near, E.base.b_near, E.B_near, E.C_near, D.oneGreen_regular_near]
    with x ha hb hB hC hreg
  intro u hu k
  rw [ha, hb, hB, hC]
  unfold heatNormalOneFirst heatNormalOneZero
  exact (fourHeatOneCovariantOperator_eq _ _ _ _ _ x
    (fun i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun i k l => (hreg.1 i k l).differentiableAt one_ne_zero) hu k).symm

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatNormalFrameData.actual_one_operator_uniform_near
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ u : smoothCovariantFields M 1, ∀ k : Fin 4,
      fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalOneFirst D x) (heatNormalOneZero D x)
        (heatNormalOneFormValue c D.point u) x k =
      heatNormalOneFormValue c D.point (smoothOneFormHodgeLaplacian (o := o) u) x k := by
  obtain ⟨r, C, hr, hCs, hE, _hI, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  filter_upwards [hCs ▸ ball_mem_nhds (0 : FourSpace) hr,
    frameExponentialJacobian_eventually_pos g o e] with x hx hpos
  intro u k
  apply D.actual_one_operator_at hRic x (hD hx)
    ((hP.contDiffAt (C.open_source.mem_nhds hx)).of_le (by norm_num))
    (by rw [← hE hx]; exact hCt (C.map_source hx)) _ u k
  exact Real.sqrt_pos.mp hpos

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative and Hodge image are combined before estimation,
so the actual Gaussian transport cancellations are retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_six_norm_le (v : TwoFormFour) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ k, |v k| ≤ B) : ‖v‖ ≤ 3 * B := by
  have hs : ‖v‖ ^ 2 ≤ 6 * B ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _k : Fin 6, B ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hk := abs_le.mp (h k)
        nlinarith [sq_nonneg (v k - B), sq_nonneg (v k + B)]
      _ = _ := by simp
  nlinarith [norm_nonneg v]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalResidualColumn (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 6) : FourSpace → TwoFormFour :=
  heatNormalTimeColumn E χ t l + heatNormalOperatorAmplitude E (heatNormalCutoffColumn E χ t l)

theorem heatNormalResidualColumn_component (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (l k : Fin 6) (x : FourSpace) :
    heatNormalResidualColumn E χ t l x k =
      deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
        fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => heatNormalCutoffParametrix E χ t y q l) x k := by
  change heatNormalTimeColumn E χ t l x k + _ = _
  rw [heatNormalTimeColumn_component E χ t ht l k x]
  rfl

theorem heatNormalResidualColumn_regular (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (t : ℝ) (l : Fin 6) :
    ContDiff ℝ 2 (heatNormalResidualColumn E χ t l) :=
  (heatNormalTimeColumn_regular E χ (hχ.of_le (by norm_num)) t l).add
    (heatNormalOperatorAmplitude_regular E _ (heatNormalCutoffColumn_regular_four E χ hχ t l))

theorem heatNormalResidualColumn_support (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) :
    tsupport (heatNormalResidualColumn E χ t l) ⊆ tsupport χ :=
  (tsupport_add _ _).trans (union_subset (heatNormalTimeColumn_support E χ t l)
    ((heatNormalOperatorAmplitude_support E _).trans (heatNormalCutoffColumn_support E χ t l)))

theorem heatNormalResidualColumn_bound (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ x k l, |deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
      fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalCutoffParametrix E χ t y q l) x k| ≤ B * t)
    (l : Fin 6) (x : FourSpace) : ‖heatNormalResidualColumn E χ t l x‖ ≤ 3 * (B * t) := by
  apply heat_six_norm_le _ _ (mul_nonneg hB ht.le)
  intro k
  rw [heatNormalResidualColumn_component E χ t ht l k x]
  exact h x k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed zeroth-order coefficient is purely quadratic in the
connection: the potential and the linear connection terms have zero trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatConnectionZero_signed_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6) (x : FourSpace)
    (hV : (twoFormHodgeMatrix * V).trace = 0)
    (hA : ∀ i, (twoFormHodgeMatrix * A i x).trace = 0)
    (hD : ∀ i j, (twoFormHodgeMatrix * heatSixPartial (A i) j x).trace = 0) :
    (twoFormHodgeMatrix * fourHeatConnectionZero a b A V x).trace =
      -(∑ i, ∑ j, a i j * (twoFormHodgeMatrix * A j x * A i x).trace) := by
  let L := heatSignedTraceLinear
  have hV' : L V = 0 := hV
  have hA' (i : Fin 4) : L (A i x) = 0 := hA i
  have hD' (i j : Fin 4) : L (heatSixPartial (A i) j x) = 0 := hD i j
  change L (V + (∑ i, b i • A i x) -
    ∑ i, ∑ j, a i j • (heatSixPartial (A i) j x + A j x * A i x)) = _
  simp only [map_sub, map_add, map_sum, map_smul, hV', hA', hD',
    smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add, zero_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact congrArg Matrix.trace (Matrix.mul_assoc twoFormHodgeMatrix (A j x) (A i x)).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.connection_partial_signed_trace
    (D : HeatNormalFrameData g o c e) (x : FourSpace) (i j : Fin 4)
    (hA : ∀ k l, DifferentiableAt ℝ
      (fun y => heatTwoFormConnection g c D.point i y k l) x) :
    (twoFormHodgeMatrix * heatSixPartial (heatTwoFormConnection g c D.point i) j x).trace = 0 := by
  have heq : (fun y => (twoFormHodgeMatrix * heatTwoFormConnection g c D.point i y).trace) =
      fun _ => 0 := funext (fun y => heatTwoFormConnectionMatrix_signed_trace _)
  have h := heatSignedTrace_partial (heatTwoFormConnection g c D.point i) x hA j
  rw [heq] at h
  simpa only [partialDeriv, fderiv_const_apply, _root_.zero_apply] using h.symm

def heatNormalConnectionQuadratic {D : HeatNormalFrameData g o c e}
    (a : FourSpace → Mat4) (x : FourSpace) : ℝ :=
  ∑ i, ∑ j, a x i j * (twoFormHodgeMatrix * heatTwoFormConnection g c D.point j x *
    heatTwoFormConnection g c D.point i x).trace

theorem HeatNormalFrameData.bundleZero_signed_near (D : HeatNormalFrameData g o c e) :
    (fun x => (twoFormHodgeMatrix * heatNormalBundleZero D x).trace) =ᶠ[𝓝 0]
      (fun x => -heatNormalConnectionQuadratic (D := D)
        (fun y => (heatNormalMetric g o e y)⁻¹) x) := by
  filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos, D.green_regular_near]
    with x hx hreg
  apply heatConnectionZero_signed_trace
  · rw [D.potential_as_actual x hx]
    exact heat_actual_potential_signed_trace _
  · intro i
    exact heatTwoFormConnectionMatrix_signed_trace _
  · intro i j
    exact D.connection_partial_signed_trace x i j
      (fun k l => (hreg.1 i k l).differentiableAt one_ne_zero)

theorem HeatNormalBundleExtension.C_signed_near {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) :
    (fun x => (twoFormHodgeMatrix * E.C x).trace) =ᶠ[𝓝 0]
      (fun x => -heatNormalConnectionQuadratic (D := D) E.base.a x) := by
  filter_upwards [E.C_near, E.base.a_near, D.bundleZero_signed_near] with x hC ha hs
  rw [hC, hs]
  simp only [heatNormalConnectionQuadratic, ha]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every actual member has the regularity and operator identities needed
for Green's formula throughout its common ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.exponential_source (N : HeatCommonNormalMember g o c E r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) :
    frameExponential g o e x ∈ (chartAt FourSpace c).source := by
  rw [← N.exponential (N.ball_source hx)]
  exact N.target_chart (N.chart.map_source (N.ball_source hx))

theorem HeatCommonNormalMember.frame_det (N : HeatCommonNormalMember g o c E r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) : (N.frameData.point x).2.det ≠ 0 := by
  intro hz
  have hh := congrArg Matrix.det (N.frameData.orthonormal x (ball_subset_ball N.radius_le hx))
  simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
  norm_num at hh

theorem HeatCommonNormalMember.green_regular (N : HeatCommonNormalMember g o c E r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) :
    (∀ i k l, ContDiffAt ℝ 1 (fun y => heatTwoFormConnection g c N.frameData.point i y k l) x) ∧
    (∀ i j, ContDiffAt ℝ 1 (fun y => (heatNormalMetric g o e y)⁻¹ i j) x) ∧
    ContDiffAt ℝ 1 (frameExponentialJacobian g o e) x ∧
    0 < frameExponentialJacobian g o e x ∧
    (∀ k l, ContinuousAt (fun y => heatNormalPotential g c N.frameData.point y k l) x) := by
  have hxD := ball_subset_ball N.radius_le hx
  have hJg : frameExponentialJacobian g o e =ᶠ[𝓝 x]
      (fun y => (N.extension.base.U y ^ 2)⁻¹) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    have hh := heatNormalLeadingAmplitude_normalization g o e y
      (Real.sqrt_pos.mpr (N.metric_pos y hy))
    rw [← (N.actual y hy).2.2.2.2] at hh
    exact eq_inv_of_mul_eq_one_right hh
  refine ⟨?_, ?_, ?_, Real.sqrt_pos.mpr (N.metric_pos x hx), ?_⟩
  · intro i k l
    exact heatTwoFormConnection_contDiffAt 1 c N.frameData.point x (N.point_regular x hx)
      (N.frameData.in_chart x hxD) (N.frame_det x hx) i k l
  · intro i j
    have hg : (fun y => N.extension.base.a y i j) =ᶠ[𝓝 x]
        (fun y => (heatNormalMetric g o e y)⁻¹ i j) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact congrArg (fun A : Mat4 => A i j) (N.actual y hy).1
    exact ((N.extension.base.a_regular i j).of_le (by norm_num)).contDiffAt.congr_of_eventuallyEq hg.symm
  · exact (((N.extension.base.U_regular.of_le (show (1 : ℕ∞ω) ≤ 10 by norm_num)).contDiffAt.pow 2).inv
      (pow_ne_zero 2 (N.extension.base.U_pos x).ne')).congr_of_eventuallyEq hJg
  · intro k l
    exact (heatNormalPotential_contDiffAt 2 g c N.frameData.point x (N.point_regular x hx)
      (N.frameData.in_chart x hxD) k l).continuousAt

theorem HeatCommonNormalMember.connection_operator (N : HeatCommonNormalMember g o c E r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) (u : FourSpace → Fin 6 → ℝ)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (k : Fin 6) :
    fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
      (N.extension.B x) (N.extension.C x) u x k =
    fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatTwoFormConnection g c N.frameData.point) (heatNormalPotential g c N.frameData.point x) u x k := by
  obtain ⟨ha, hb, hB, hC, _⟩ := N.actual x hx
  rw [ha, hb, hB, hC]
  exact (heatNormalConnectionOperator_eq N.frameData u x
    (fun i k l => ((N.green_regular x hx).1 i k l).differentiableAt one_ne_zero) hu k).symm

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatCommonNormalMember.actual_bundle_operator (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (x : FourSpace) (hx : x ∈ ball 0 r) (u : smoothTwoForms o) (k : Fin 6) :
    fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatNormalBundleFirst N.frameData x) (heatNormalBundleZero N.frameData x)
      (fun y l => heatNormalTwoFormValue o c N.frameData.point u.val y l) x k =
    heatNormalTwoFormValue o c N.frameData.point (smoothHodgeLaplacian hRic u).val x k :=
  N.frameData.actual_bundle_operator_at hRic x (ball_subset_ball N.radius_le hx)
    (N.point_regular x hx) (N.exponential_source x hx) (N.metric_pos x hx) u k

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form diagonal heat density and its frame-column realization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

omit [PreconnectedSpace M] in
instance oneFormEigenIndex_countable : Countable (OneFormEigenIndex hRic d) := by
  apply Set.countable_univ_iff.mp
  have h := (oneFormHeat_weight_summable hRic d 1 zero_lt_one).countable_support
  convert h using 1
  ext i
  simp only [Set.mem_univ, Function.mem_support, oneFormHeatWeight, ne_eq,
    Real.exp_ne_zero, not_false_eq_true]

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormHeatWeight_half_sq (t : ℝ≥0) (i : OneFormEigenIndex hRic d) :
    oneFormHeatWeight hRic d (t / 2) i ^ 2 = oneFormHeatWeight hRic d t i := by
  simp only [oneFormHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

def oneFormHeatDiagonal (t : ℝ≥0) (x : M) : ℝ :=
  ∑' i, oneFormHeatWeight hRic d t i * covariantFieldNormSq g (oneFormEigenSection hRic d i).val x

theorem oneFormHeatFrameColumn_norm_sq (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 4) :
    ‖oneFormHeatFrameColumn hRic d t ht e l‖ ^ 2 =
      ∑' i, (oneFormHeatWeight hRic d t i *
        covariantFieldFramed g (oneFormEigenSection hRic d i).val e ![l]) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (oneFormEigenbasis hRic d).tsum_inner_mul_inner]
  apply tsum_congr
  intro i
  simp only [oneFormEigenbasis, HilbertBasis.coe_mk]
  rw [real_inner_comm (oneFormHeatFrameColumn hRic d t ht e l), oneFormHeatFrameColumn_eigen]
  ring

theorem oneFormHeatFrameCoefficient_sq_summable (t : ℝ≥0) (ht : 0 < t)
    (e : FrameBundle g) (l : Fin 4) :
    Summable (fun i => (oneFormHeatWeight hRic d t i *
      covariantFieldFramed g (oneFormEigenSection hRic d i).val e ![l]) ^ 2) := by
  have h := (oneFormEigenbasis hRic d).summable_inner_mul_inner
    (oneFormHeatFrameColumn hRic d t ht e l) (oneFormHeatFrameColumn hRic d t ht e l)
  apply h.congr
  intro i
  simp only [oneFormEigenbasis, HilbertBasis.coe_mk]
  rw [real_inner_comm (oneFormHeatFrameColumn hRic d t ht e l), oneFormHeatFrameColumn_eigen]
  ring

theorem oneFormHeatDiagonal_summable (t : ℝ≥0) (ht : 0 < t) (x : M) :
    Summable (fun i => oneFormHeatWeight hRic d t i *
      covariantFieldNormSq g (oneFormEigenSection hRic d i).val x) := by
  have hs := (hasSum_sum (s := Finset.univ) (fun l _ =>
    (oneFormHeatFrameCoefficient_sq_summable hRic d (t / 2) (half_pos ht)
      (frameAt g x) l).hasSum)).summable
  apply hs.congr
  intro i
  have hn : covariantFieldNormSq g (oneFormEigenSection hRic d i).val x =
      frameTensorSquareNorm (covariantFieldFramed g (oneFormEigenSection hRic d i).val (frameAt g x)) :=
    covariantFieldNormSq_eq_frame _ (frameAt g x)
  rw [hn, oneForm_squareNorm,
    ← oneFormHeatWeight_half_sq hRic d t i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem oneFormHeatDiagonal_columns (t : ℝ≥0) (ht : 0 < t) (e : FrameBundle g) :
    oneFormHeatDiagonal hRic d t e.base =
      ∑ l : Fin 4, ‖oneFormHeatFrameColumn hRic d (t / 2) (half_pos ht) e l‖ ^ 2 := by
  simp_rw [oneFormHeatFrameColumn_norm_sq]
  rw [← Summable.tsum_finsetSum (fun l (_ : l ∈ (Finset.univ : Finset (Fin 4))) =>
    oneFormHeatFrameCoefficient_sq_summable hRic d (t / 2) (half_pos ht) e l)]
  apply tsum_congr
  intro i
  rw [covariantFieldNormSq_eq_frame _ e, oneForm_squareNorm,
    ← oneFormHeatWeight_half_sq hRic d t i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem oneFormHeatDiagonal_nonneg (t : ℝ≥0) (ht : 0 < t) (x : M) :
    0 ≤ oneFormHeatDiagonal hRic d t x := by
  rw [show x = (frameAt g x).base from rfl, oneFormHeatDiagonal_columns hRic d t ht]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem oneFormHeatDiagonal_bound (t : ℝ≥0) (ht : 0 < t) (x : M) :
    oneFormHeatDiagonal hRic d t x ≤ 4 * ‖oneFormHeatToContinuous hRic d (t / 2) (half_pos ht)‖ ^ 2 := by
  rw [show x = (frameAt g x).base from rfl, oneFormHeatDiagonal_columns hRic d t ht]
  calc
    _ ≤ ∑ _l : Fin 4, ‖oneFormHeatToContinuous hRic d (t / 2) (half_pos ht)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro l _
      exact (sq_le_sq₀
        (norm_nonneg (oneFormHeatFrameColumn hRic d (t / 2) (half_pos ht) (frameAt g x) l))
        (norm_nonneg (oneFormHeatToContinuous hRic d (t / 2) (half_pos ht)))).mpr
        (oneFormHeatFrameColumn_norm hRic d (t / 2) (half_pos ht) (frameAt g x) l)
    _ = _ := by simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual spectral heat evolution satisfies the geometric Hodge
heat equation at every positive time, with its proved smooth spatial representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatDerivative_generator (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) :
    twoFormHeatDerivative hRic t ht f = -twoFormHodgeGenerator hRic
      ⟨twoFormHeat hRic t f, twoFormHeat_mem_hodgeDomain hRic t ht f⟩ := by
  let u : twoFormHodgeDomain (o := o) hRic :=
    ⟨twoFormHeat hRic t f, twoFormHeat_mem_hodgeDomain hRic t ht f⟩
  have hE : twoFormHodgeDomainEquiv hRic (twoFormHeatLiftSource hRic t ht f) = u := by
    apply Subtype.ext
    exact twoFormHeatLiftSource_resolvent hRic t ht f
  have he := congrArg (twoFormHodgeDomainEquiv hRic).symm hE
  rw [LinearEquiv.symm_apply_apply] at he
  change twoFormHeat hRic t f - twoFormHeatLiftSource hRic t ht f =
    -((twoFormHodgeDomainEquiv hRic).symm u - twoFormHeat hRic t f)
  rw [← he]
  abel

theorem twoFormHeatDerivative_laplacian (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) :
    twoFormHeatDerivative hRic t ht f =
      -smoothTwoFormToL2
        (smoothHodgeLaplacian hRic (twoFormHeatSection hRic t ht f) : SmoothL2TwoForm o) := by
  let w := twoFormHeatSection hRic t ht f
  have he : (⟨smoothTwoFormToL2 (w : SmoothL2TwoForm o),
      smoothTwoForm_mem_hodgeDomain hRic w⟩ : twoFormHodgeDomain hRic) =
      ⟨twoFormHeat hRic t f, twoFormHeat_mem_hodgeDomain hRic t ht f⟩ :=
    Subtype.ext (twoFormHeatSection_L2 hRic t ht f)
  have hg := twoFormHodgeGenerator_smooth hRic w
  rw [he] at hg
  rw [twoFormHeatDerivative_generator, hg]

theorem twoFormHeat_geometric_equation (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) :
    HasDerivAt (fun s : ℝ => twoFormHeat hRic s.toNNReal f)
      (-smoothTwoFormToL2
        (smoothHodgeLaplacian hRic (twoFormHeatSection hRic t ht f) : SmoothL2TwoForm o))
      (t : ℝ) := by
  have hd := twoFormHeat_hasDerivAt hRic t ht f
  rw [twoFormHeatDerivative_laplacian] at hd
  exact hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ordinary connection traces in degrees one and two cancel in the
four-dimensional de Rham supertrace. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatTwoFormConnectionMatrix_trace (A : Mat4) :
    (heatTwoFormConnectionMatrix A).trace = 0 := by
  rw [heatTwoFormConnectionMatrix_infinitesimal]
  simp [twoFormInfinitesimalMatrix, Matrix.trace, Matrix.diag, Fin.sum_univ_succ]

theorem heatTwoFormConnectionMatrix_square_trace (A : Mat4) (hA : Aᵀ = -A) :
    (heatTwoFormConnectionMatrix A * heatTwoFormConnectionMatrix A).trace =
      2 * (A * A).trace := by
  have h := twoFormInfinitesimalMatrix_euler_trace (twoFormExtract A)
  rw [twoFormMatrix_extract A hA] at h
  rw [heatTwoFormConnectionMatrix_infinitesimal]
  linarith only [h]

theorem heatTwoFormConnectionMatrix_product_trace (A B : Mat4)
    (hA : Aᵀ = -A) (hB : Bᵀ = -B) :
    (heatTwoFormConnectionMatrix A * heatTwoFormConnectionMatrix B).trace =
      2 * (A * B).trace := by
  have hAB : (A + B)ᵀ = -(A + B) := by
    rw [Matrix.transpose_add, hA, hB, neg_add]
  have h := heatTwoFormConnectionMatrix_square_trace (A + B) hAB
  have hm : heatTwoFormConnectionMatrix (A + B) =
      heatTwoFormConnectionMatrix A + heatTwoFormConnectionMatrix B :=
    heatConnectionMatrixLinear.map_add A B
  rw [hm] at h
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add] at h
  rw [heatTwoFormConnectionMatrix_square_trace A hA,
    heatTwoFormConnectionMatrix_square_trace B hB,
    Matrix.trace_mul_comm (heatTwoFormConnectionMatrix B) (heatTwoFormConnectionMatrix A),
    Matrix.trace_mul_comm B A] at h
  linarith only [h]

theorem heatFour_skew_trace (A : Mat4) (hA : Aᵀ = -A) : A.trace = 0 := by
  have h := congrArg Matrix.trace hA
  rw [Matrix.trace_transpose, Matrix.trace_neg] at h
  linarith only [h]

theorem heatOneConnectionZero_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → Mat4) (V : Mat4) (x : FourSpace)
    (hA : ∀ i, (A i x).trace = 0)
    (hD : ∀ i j, (matrixPartial (A i) j x).trace = 0) :
    (fourHeatOneConnectionZero a b A V x).trace =
      V.trace - ∑ i, ∑ j, a i j * (A j x * A i x).trace := by
  change (V + (∑ i, b i • A i x) -
    ∑ i, ∑ j, a i j • (matrixPartial (A i) j x + A j x * A i x)).trace = _
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
    hA, hD, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]

theorem heatTwoConnectionZero_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6) (x : FourSpace)
    (hA : ∀ i, (A i x).trace = 0)
    (hD : ∀ i j, (heatSixPartial (A i) j x).trace = 0) :
    (fourHeatConnectionZero a b A V x).trace =
      V.trace - ∑ i, ∑ j, a i j * (A j x * A i x).trace := by
  change (V + (∑ i, b i • A i x) -
    ∑ i, ∑ j, a i j • (heatSixPartial (A i) j x + A j x * A i x)).trace = _
  simp only [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
    hA, hD, smul_eq_mul, mul_zero, Finset.sum_const_zero, zero_add, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact normal amplitude satisfies Green's identity against
every actual smooth two-form on one fixed geometric neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_weighted_inner_sum (ρ : ℝ) (u v : TwoFormFour) :
    ρ * inner ℝ u v = ∑ k : Fin 6, ρ * u k * v k := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.compact_green_near
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ (a : FourSpace → TwoFormFour), ContDiff ℝ 2 a →
      HasCompactSupport a → tsupport a ⊆ ball 0 r → ∀ v : smoothTwoForms o,
      (∫ x, frameExponentialJacobian g o e x *
        inner ℝ (a x) (heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic v).val x)) =
      ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (heatNormalOperatorAmplitude E a x) (heatNormalTwoFormValue o c D.point v.val x) := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hn := D.green_regular_near.and (E.connection_operator_near.and
    ((D.actual_bundle_operator_uniform_near he hRic).and
      (hp.and (ball_mem_nhds (0 : FourSpace) D.radius_pos))))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro a ha hc hs v
  let u := fun x k => a x k
  let w := fun x k => heatNormalTwoFormValue o c D.point v.val x k
  have hu (k : Fin 6) : ContDiff ℝ 2 (fun x => u x k) :=
    (contDiff_piLp (p := 2)).mp ha k
  have hsc (k : Fin 6) : tsupport (fun x => u x k) ⊆ ball 0 r :=
    (heatAmplitude_component_support a k).trans hs
  have hcc (k : Fin 6) : HasCompactSupport (fun x => u x k) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (heatAmplitude_component_support a k)
  have hw (x : FourSpace) (hx : x ∈ ball 0 r) (k : Fin 6) :
      ContDiffAt ℝ 2 (fun y => w y k) x := by
    have h := heatNormalTwoFormValue_contDiffAt 2 v.property c D.point x
      (hball hx).2.2.2.1 (D.in_chart x (hball hx).2.2.2.2)
    exact (contDiffAt_piLp (p := 2)).mp h k
  have hop (x : FourSpace) (k : Fin 6) : heatNormalOperatorAmplitude E a x k =
      fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) u x k :=
    E.compact_operator_eq (ball 0 r) (fun y hy => (hball hy).2.1) a ha hs x k
  have htest (x : FourSpace) : frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic v).val x) =
      ∑ k : Fin 6, frameExponentialJacobian g o e x * u x k *
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) w x k := by
    rw [heat_weighted_inner_sum]
    by_cases hx : x ∈ ball 0 r
    · apply Finset.sum_congr rfl
      intro k _
      have hactual := (hball hx).2.2.1 v (hball hx).2.2.2.2 k
      have hconv := heatNormalConnectionOperator_eq D w x
        (fun i k l => ((hball hx).1.1 i k l).differentiableAt one_ne_zero) (hw x hx) k
      rw [← hconv] at hactual
      rw [hactual]
    · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      have hzk (k : Fin 6) : u x k = 0 := by change a x k = 0; rw [hz]; rfl
      simp only [hz, PiLp.zero_apply, hzk, mul_zero, zero_mul, Finset.sum_const_zero]
  have hg := fourHeatCovariantOperator_compact_adjoint
    (heatTwoFormConnection g c D.point) (fun x => (heatNormalMetric g o e x)⁻¹)
    (frameExponentialJacobian g o e) (heatNormalPotential g c D.point) u w (ball 0 r)
    hu hcc hsc hw (fun x hx => (hball hx).1.1) (fun x hx => (hball hx).1.2.1)
    (fun x hx => (hball hx).1.2.2.1) (fun x hx => (hball hx).1.2.2.2.1.ne')
    (fun x hx => (hball hx).1.2.2.2.2)
    (fun _ _ i => heatTwoFormConnectionMatrix_skew _)
    (fun x _ i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun x hx => D.potential_symmetric x (hball hx).2.2.2.2)
  calc
    _ = ∫ x, ∑ k : Fin 6, frameExponentialJacobian g o e x * u x k *
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) w x k := by
      apply integral_congr_ae
      exact Eventually.of_forall htest
    _ = _ := hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heat_weighted_inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hop]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact component-integral pairing for compact normal amplitudes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalAmplitudeL2_pairing_sum
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : SmoothL2TwoForm o) :
    inner ℝ (heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothTwoFormToL2 v) =
      (normalizedChartFactor g).toReal * ∑ k : Fin 6, ∫ x,
        a x k * (frameExponentialJacobian g o e x *
          heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val x k) := by
  let f := fun k x => frameExponentialJacobian g o e x *
    heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val x k
  have hV : ContinuousOn (heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val)
      C.source := by
    intro x hx
    exact (heatNormalTwoFormValue_contDiffAt 2 (v : smoothTwoForms o).property c D.point x
      (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx))).continuousAt.continuousWithinAt
  have hf (k : Fin 6) : ContinuousOn (f k) C.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      ((EuclideanSpace.proj k).continuous.comp_continuousOn hV)
  have hi (k : Fin 6) : Integrable (fun x => a x k * f k x) := by
    have hak := ((contDiff_piLp (p := 2)).mp ha k).continuous
    have hck : HasCompactSupport (fun x => a x k) :=
      hc.of_isClosed_subset (isClosed_tsupport _) (heatAmplitude_component_support a k)
    have hfk (x : FourSpace) (hx : x ∈ tsupport (fun y => a y k)) : ContinuousAt (f k) x :=
      (hf k).continuousAt (C.open_source.mem_nhds (hs (heatAmplitude_component_support a k hx)))
    simpa only [mul_comm] using fourHeat_local_product_integrable (f k) (fun x => a x k) hak hck hfk
  have hpair := heatNormalAmplitudeL2_pairing_normal D C hE hCt hP hD a ha hc hs v
  apply hpair.trans
  congr 1
  calc
    _ = ∫ x, ∑ k : Fin 6, a x k * f k x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [PiLp.inner_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      change frameExponentialJacobian g o e x *
        (heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val x k * a x k) = _
      dsimp only [f]
      ring
    _ = _ := integral_finsetSum _ (fun k _ => hi k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual compact one-form amplitudes satisfy the geometric Green identity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatOneAmplitude_component_support (a : FourSpace → FourSpace) (k : Fin 4) :
    tsupport (fun x => a x k) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  contrapose! hx
  apply Function.notMem_support.mpr
  rw [Function.notMem_support.mp hx]
  rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.compact_operator_eq
    (E : HeatNormalOneExtension D) (U : Set FourSpace)
    (hU : ∀ x ∈ U, ∀ u : FourSpace → Fin 4 → ℝ,
      (∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) → ∀ k,
      fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x) u x k =
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4))) u x k)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a)
    (hs : tsupport a ⊆ U) (x : FourSpace) (k : Fin 4) :
    heatNormalOneOperatorAmplitude E a x k =
      fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4)))
        (fun y l => a y l) x k := by
  by_cases hx : x ∈ U
  · exact hU x hx (fun y l => a y l)
      (fun l => ((contDiff_piLp (p := 2)).mp ha l).contDiffAt) k
  · have hz : ∀ l, (fun y => a y l) =ᶠ[𝓝 x] (fun _ => 0) := by
      intro l
      have hn : x ∉ tsupport a := fun h => hx (hs h)
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hn] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy]
      rfl
    change fourHeatOneOperator _ _ _ _ _ x k = _
    rw [fourHeatOneOperator_zero_of_locally_zero _ _ _ _ hz,
      fourHeatOneCovariantOperator_zero_of_locally_zero _ _ _ _ hz]


end

section

theorem heat_one_weighted_inner_sum (ρ : ℝ) (u v : FourSpace) :
    ρ * inner ℝ u v = ∑ k : Fin 4, ρ * u k * v k := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.compact_green_near
    (E : HeatNormalOneExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ (a : FourSpace → FourSpace), ContDiff ℝ 2 a →
      HasCompactSupport a → tsupport a ⊆ ball 0 r → ∀ v : smoothCovariantFields M 1,
      (∫ x, frameExponentialJacobian g o e x *
        inner ℝ (a x) (heatNormalOneValue c D.point (smoothOneFormHodgeLaplacian (o := o) v) x)) =
      ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (heatNormalOneOperatorAmplitude E a x) (heatNormalOneValue c D.point v x) := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hn := D.oneGreen_regular_near.and (E.connection_operator_near.and
    ((D.actual_one_operator_uniform_near he hRic).and
      (hp.and (ball_mem_nhds (0 : FourSpace) D.radius_pos))))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro a ha hc hs v
  let u := fun x k => a x k
  let w := fun x k => heatNormalOneFormValue c D.point v x k
  have hu (k : Fin 4) : ContDiff ℝ 2 (fun x => u x k) :=
    (contDiff_piLp (p := 2)).mp ha k
  have hsc (k : Fin 4) : tsupport (fun x => u x k) ⊆ ball 0 r :=
    (heatOneAmplitude_component_support a k).trans hs
  have hcc (k : Fin 4) : HasCompactSupport (fun x => u x k) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (heatOneAmplitude_component_support a k)
  have hw (x : FourSpace) (hx : x ∈ ball 0 r) (k : Fin 4) :
      ContDiffAt ℝ 2 (fun y => w y k) x := by
    exact heatNormalOneFormValue_regular 2 c D.point v x
      (hball hx).2.2.2.1 (D.in_chart x (hball hx).2.2.2.2) k
  have hop (x : FourSpace) (k : Fin 4) : heatNormalOneOperatorAmplitude E a x k =
      fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4))) u x k :=
    E.compact_operator_eq (ball 0 r) (fun y hy => (hball hy).2.1) a ha hs x k
  have htest (x : FourSpace) : frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalOneValue c D.point (smoothOneFormHodgeLaplacian (o := o) v) x) =
      ∑ k : Fin 4, frameExponentialJacobian g o e x * u x k *
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4))) w x k := by
    rw [heat_one_weighted_inner_sum]
    by_cases hx : x ∈ ball 0 r
    · apply Finset.sum_congr rfl
      intro k _
      have hactual := (hball hx).2.2.1 v k
      have hconv := fourHeatOneCovariantOperator_eq
        (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalFrameConnection g c D.point) ((3 : ℝ) • (1 : Mat4)) w x
        (fun i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
        (fun i k l => ((hball hx).1.1 i k l).differentiableAt one_ne_zero) (hw x hx) k
      unfold heatNormalOneFirst heatNormalOneZero at hactual
      rw [← hconv] at hactual
      rw [hactual]
      rfl
    · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      have hzk (k : Fin 4) : u x k = 0 := by change a x k = 0; rw [hz]; rfl
      simp only [hz, PiLp.zero_apply, hzk, mul_zero, zero_mul, Finset.sum_const_zero]
  have hg := fourHeatOneCovariantOperator_compact_adjoint
    (heatNormalFrameConnection g c D.point) (fun x => (heatNormalMetric g o e x)⁻¹)
    (frameExponentialJacobian g o e) ((fun _ : FourSpace => (3 : ℝ) • (1 : Mat4))) u w (ball 0 r)
    hu hcc hsc hw (fun x hx => (hball hx).1.1) (fun x hx => (hball hx).1.2.1)
    (fun x hx => (hball hx).1.2.2.1) (fun x hx => (hball hx).1.2.2.2.ne')
    (fun _ _ _ _ => continuousAt_const)
    (fun x hx i => D.connection_skew x (hball hx).2.2.2.2 i)
    (fun x _ i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun _ _ k l => by simp [Matrix.one_apply, eq_comm])
  calc
    _ = ∫ x, ∑ k : Fin 4, frameExponentialJacobian g o e x * u x k *
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4))) w x k := by
      apply integral_congr_ae
      exact Eventually.of_forall htest
    _ = _ := hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heat_one_weighted_inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hop]
      change _ = _ * _ * w x k
      ring


end
end PositiveEinsteinFour.Geometry
end


section

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCutoffParametrix_joint_contDiffAt (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (z : ℝ × FourSpace) (ht : 0 < z.1)
    (k l : Fin 4) :
    ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => heatNormalOneCutoffParametrix E χ w.1 w.2 k l) z := by
  have hu (m : Fin 4) : ContDiff ℝ 2 (fun x => E.amplitude m x k l) :=
    (E.amplitude_regular m (by omega) k l).of_le (by norm_num)
  exact ((hχ.comp contDiff_snd).contDiffAt).mul
    ((fourHeatGaussian_joint_contDiffAt z ht).mul
      (fourHeatPolynomial_joint_contDiff _ hu).contDiffAt)

theorem heatNormalOneTimeColumn_joint_continuousOn (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 4) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalOneTimeColumn E χ z.1 l z.2)
      (Ioi 0 ×ˢ univ) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro k
  exact (hχ.comp continuous_snd).continuousOn.mul
    (fourHeatGaussianPolynomialTime_continuousOn _
      (fun m => (E.amplitude_regular m (by omega) k l).continuous))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact Gaussian-free column and its uniform density-weighted bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalPolynomialColumn (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 6) (x : FourSpace) : TwoFormFour :=
  WithLp.toLp 2 (fun k => χ x * fourHeatPolynomial (fun m y => E.amplitude m y k l) t x)

theorem heatNormalPolynomialColumn_continuous (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 6) :
    Continuous (fun z : ℝ × FourSpace => heatNormalPolynomialColumn E χ z.1 l z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  exact (hχ.comp continuous_snd).mul
    (fourHeatPolynomial_joint_continuous _
      (fun m => (E.amplitude_regular m (by omega) k l).continuous))

theorem heatNormalCutoffColumn_gaussian (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) (x : FourSpace) :
    heatNormalCutoffColumn E χ t l x =
      fourHeatGaussian t x • heatNormalPolynomialColumn E χ t l x := by
  apply WithLp.ofLp_injective 2
  funext k
  change χ x * (fourHeatGaussian t x * _) = fourHeatGaussian t x * (χ x * _)
  unfold fourHeatBundlePolynomial fourHeatPolynomial
  ring

theorem heatNormalPolynomialColumn_weight_bound (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ) (l : Fin 6) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      frameExponentialJacobian g o e x * ‖heatNormalPolynomialColumn E χ t l x‖ ^ 2 ≤ B := by
  let W := fun z : ℝ × FourSpace => frameExponentialJacobian g o e z.2 *
    ‖heatNormalPolynomialColumn E χ z.1 l z.2‖ ^ 2
  have hW : Continuous W := ((frameExponentialJacobian_continuous g o e).comp continuous_snd).mul
    ((heatNormalPolynomialColumn_continuous E χ hχ l).norm.pow 2)
  obtain ⟨B, hb⟩ := (isCompact_Icc.prod hc).bddAbove_image hW.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hb ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left _ _)
  · have hzero : heatNormalPolynomialColumn E χ t l x = 0 := by
      apply WithLp.ofLp_injective 2
      funext k
      change χ x * _ = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    rw [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact le_max_right _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual compact kernel and its residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCutoffColumn_joint_continuousOn (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (l : Fin 6) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalCutoffColumn E χ z.1 l z.2)
      (Ioi 0 ×ˢ univ) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro k z hz
  exact (heatNormalCutoffParametrix_joint_contDiffAt E χ hχ z hz.1 k l).continuousAt.continuousWithinAt

theorem heatNormalOperatorColumn_joint_continuousOn (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (l : Fin 6) :
    ContinuousOn (fun z : ℝ × FourSpace =>
      heatNormalOperatorAmplitude E (heatNormalCutoffColumn E χ z.1 l) z.2)
      (Ioi 0 ×ˢ univ) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro k z hz
  exact (fourHeatBundleOperator_joint_continuousAt E.base.a E.base.b E.B E.C
    (fun w k => heatNormalCutoffParametrix E χ w.1 w.2 k l) z
    (fun i j => (E.base.a_regular i j).continuous.continuousAt)
    (fun i => (E.base.b_regular i).continuous.continuousAt)
    (fun i k l => (E.B_regular i k l).continuous.continuousAt)
    (fun k l => (E.C_regular k l).continuous.continuousAt)
    (fun k => heatNormalCutoffParametrix_joint_contDiffAt E χ hχ z hz.1 k l) k).continuousWithinAt

theorem heatNormalResidualColumn_joint_continuousOn (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (l : Fin 6) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalResidualColumn E χ z.1 l z.2)
      (Ioi 0 ×ˢ univ) :=
  (heatNormalTimeColumn_joint_continuousOn E χ hχ.continuous l).add
    (heatNormalOperatorColumn_joint_continuousOn E χ hχ l)

end
end PositiveEinsteinFour.Geometry
end


section

/-! At the radial center, derivatives of the scalar metric weights do
not contribute to the quadratic connection trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_trace_product_expansion (H A B : HeatMat6) :
    (H * A * B).trace = ∑ k, ∑ l, ∑ q, H k l * (A l q * B q k) := by
  calc
    _ = (H * (A * B)).trace := congrArg Matrix.trace (Matrix.mul_assoc H A B)
    _ = _ := by simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.mul_sum]

theorem heat_trace_product_regular (H : HeatMat6) (A B : FourSpace → HeatMat6)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun x => A x k l) 0)
    (hB : ∀ k l, ContDiffAt ℝ 2 (fun x => B x k l) 0) :
    ContDiffAt ℝ 2 (fun x => (H * A x * B x).trace) 0 := by
  simp_rw [heat_trace_product_expansion]
  exact ContDiffAt.sum (fun k _ => ContDiffAt.sum (fun l _ =>
    ContDiffAt.sum (fun q _ => contDiffAt_const.mul ((hA l q).mul (hB q k)))))

theorem heat_trace_product_partial_zero (H : HeatMat6) (A B : FourSpace → HeatMat6)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun x => A x k l) 0)
    (hB : ∀ k l, ContDiffAt ℝ 2 (fun x => B x k l) 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (i : Fin 4) :
    partialDeriv (fun x => (H * A x * B x).trace) i 0 = 0 := by
  have hreg (k l q : Fin 6) : ContDiffAt ℝ 2
      (fun x => H k l * (A x l q * B x q k)) 0 :=
    contDiffAt_const.mul ((hA l q).mul (hB q k))
  simp_rw [heat_trace_product_expansion]
  rw [heat_partial_finite_sum _ 0 (fun k =>
    (ContDiffAt.sum (fun l _ => ContDiffAt.sum (fun q _ => hreg k l q))).differentiableAt
      (by norm_num)) i]
  simp_rw [heat_partial_finite_sum _ 0 (fun l =>
    (ContDiffAt.sum (fun q _ => hreg _ l q)).differentiableAt (by norm_num)) i]
  simp_rw [heat_partial_finite_sum _ 0 (fun q => (hreg _ _ q).differentiableAt (by norm_num)) i]
  simp_rw [fourHeat_partial_const_mul]
  have hp (k l q : Fin 6) : partialDeriv (fun x => A x l q * B x q k) i 0 = 0 := by
    rw [scalar_partial_product _ _ 0 ((hA l q).differentiableAt (by norm_num))
      ((hB q k).differentiableAt (by norm_num)) i]
    simp only [hA0, hB0, Matrix.zero_apply, mul_zero, zero_mul, add_zero]
  simp only [hp, mul_zero, Finset.sum_const_zero]

theorem heat_weighted_trace_second_zero (H : HeatMat6) (a : FourSpace → ℝ)
    (A B : FourSpace → HeatMat6) (ha : ContDiffAt ℝ 2 a 0)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun x => A x k l) 0)
    (hB : ∀ k l, ContDiffAt ℝ 2 (fun x => B x k l) 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun x => a x * (H * A x * B x).trace) i) j 0 =
      a 0 * (H * (heatSixPartial A i 0 * heatSixPartial B j 0 +
        heatSixPartial A j 0 * heatSixPartial B i 0)).trace := by
  rw [scalar_partial_second_product_at a _ 0 ha (heat_trace_product_regular H A B hA hB) i j,
    heat_trace_product_partial_zero H A B hA hB hA0 hB0,
    heat_trace_product_partial_zero H A B hA hB hA0 hB0,
    heat_trace_product_second_zero H A B hA hB hA0 hB0]
  simp only [hA0, hB0, Matrix.trace_zero, mul_zero, add_zero, zero_add]

theorem heat_weighted_trace_partial_zero (H : HeatMat6) (a : FourSpace → ℝ)
    (A B : FourSpace → HeatMat6) (ha : ContDiffAt ℝ 2 a 0)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun x => A x k l) 0)
    (hB : ∀ k l, ContDiffAt ℝ 2 (fun x => B x k l) 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (i : Fin 4) :
    partialDeriv (fun x => a x * (H * A x * B x).trace) i 0 = 0 := by
  rw [scalar_partial_product a _ 0 (ha.differentiableAt (by norm_num))
    ((heat_trace_product_regular H A B hA hB).differentiableAt (by norm_num)) i,
    heat_trace_product_partial_zero H A B hA hB hA0 hB0]
  simp only [hA0, hB0, Matrix.trace_zero, mul_zero, add_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.quadratic_zero (D : HeatNormalFrameData g o c e)
    (a : FourSpace → Mat4) : heatNormalConnectionQuadratic (D := D) a 0 = 0 := by
  simp only [heatNormalConnectionQuadratic, D.twoForm_connection_zero,
    Matrix.trace_zero, mul_zero, Finset.sum_const_zero]

theorem HeatNormalFrameData.quadratic_partial_zero (D : HeatNormalFrameData g o c e)
    (a : FourSpace → Mat4) (ha : ∀ r s, ContDiffAt ℝ 2 (fun x => a x r s) 0)
    (i : Fin 4) : partialDeriv (heatNormalConnectionQuadratic (D := D) a) i 0 = 0 := by
  have hA (r : Fin 4) (k l : Fin 6) :
      ContDiffAt ℝ 2 (fun x => heatTwoFormConnection g c D.point r x k l) 0 :=
    (D.twoForm_connection_regular r k l).of_le (by norm_num)
  have hr (r s : Fin 4) : ContDiffAt ℝ 2 (fun x => a x r s *
      (twoFormHodgeMatrix * heatTwoFormConnection g c D.point s x *
        heatTwoFormConnection g c D.point r x).trace) 0 :=
    (ha r s).mul (heat_trace_product_regular _ _ _ (hA s) (hA r))
  unfold heatNormalConnectionQuadratic
  rw [heat_partial_finite_sum _ 0 (fun r =>
    (ContDiffAt.sum (fun s _ => hr r s)).differentiableAt (by norm_num)) i]
  simp_rw [heat_partial_finite_sum _ 0 (fun s => (hr _ s).differentiableAt (by norm_num)) i]
  simp_rw [heat_weighted_trace_partial_zero _ _ _ _ (ha _ _) (hA _) (hA _)
    (D.twoForm_connection_zero _) (D.twoForm_connection_zero _) i]
  simp only [Finset.sum_const_zero]

theorem HeatNormalFrameData.quadratic_second (D : HeatNormalFrameData g o c e)
    (a : FourSpace → Mat4) (ha : ∀ r s, ContDiffAt ℝ 2 (fun x => a x r s) 0)
    (ha0 : a 0 = 1) (i : Fin 4) :
    partialDeriv (partialDeriv (heatNormalConnectionQuadratic (D := D) a) i) i 0 =
      ∑ r, (twoFormHodgeMatrix *
        (heatSixPartial (heatTwoFormConnection g c D.point r) i 0 *
          heatSixPartial (heatTwoFormConnection g c D.point r) i 0 +
        heatSixPartial (heatTwoFormConnection g c D.point r) i 0 *
          heatSixPartial (heatTwoFormConnection g c D.point r) i 0)).trace := by
  have hA (r : Fin 4) (k l : Fin 6) :
      ContDiffAt ℝ 2 (fun x => heatTwoFormConnection g c D.point r x k l) 0 :=
    (D.twoForm_connection_regular r k l).of_le (by norm_num)
  have hr (r s : Fin 4) : ContDiffAt ℝ 2 (fun x => a x r s *
      (twoFormHodgeMatrix * heatTwoFormConnection g c D.point s x *
        heatTwoFormConnection g c D.point r x).trace) 0 :=
    (ha r s).mul (heat_trace_product_regular _ _ _ (hA s) (hA r))
  unfold heatNormalConnectionQuadratic
  rw [heat_partial_second_finite_sum _ 0 (fun r => ContDiffAt.sum (fun s _ => hr r s)) i i]
  simp_rw [heat_partial_second_finite_sum _ 0 (fun s => hr _ s) i i]
  simp_rw [heat_weighted_trace_second_zero _ _ _ _ (ha _ _) (hA _) (hA _)
    (D.twoForm_connection_zero _) (D.twoForm_connection_zero _) i i]
  simp only [ha0, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration of the genuine one-form diagonal recovers the spectral heat trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

omit [PreconnectedSpace M] in
theorem oneFormEigenSection_norm_integral (i : OneFormEigenIndex hRic d) :
    (∫ x, covariantFieldNormSq g (oneFormEigenSection hRic d i).val x ∂normalizedVolume g) = 1 := by
  rw [← smoothOneFormL2Pairing_self (o := o), ← smoothOneFormL2Linear_inner,
    oneFormEigenSection_L2, real_inner_self_eq_norm_sq,
    (oneFormEigenvector_orthonormal hRic d).1 i, one_pow]

omit [PreconnectedSpace M] in
theorem oneFormEigenSection_norm_nonneg (i : OneFormEigenIndex hRic d) (x : M) :
    0 ≤ covariantFieldNormSq g (oneFormEigenSection hRic d i).val x := by
  rw [show x = (frameAt g x).base from rfl, covariantFieldNormSq_eq_frame _ (frameAt g x),
    oneForm_squareNorm]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem oneFormHeatDiagonal_integrable (t : ℝ≥0) (ht : 0 < t) :
    Integrable (oneFormHeatDiagonal hRic d t) (normalizedVolume g) := by
  have hi (i : OneFormEigenIndex hRic d) : Integrable
      (fun x => oneFormHeatWeight hRic d t i *
        covariantFieldNormSq g (oneFormEigenSection hRic d i).val x) (normalizedVolume g) :=
    (((oneFormEigenSection hRic d i).property.continuous_normSq (g := g)).const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Summable (fun i => ∫ x, ‖oneFormHeatWeight hRic d t i *
      covariantFieldNormSq g (oneFormEigenSection hRic d i).val x‖ ∂normalizedVolume g) := by
    apply (oneFormHeat_weight_summable hRic d t ht).congr
    intro i
    have hn (x : M) : ‖oneFormHeatWeight hRic d t i *
        covariantFieldNormSq g (oneFormEigenSection hRic d i).val x‖ =
        oneFormHeatWeight hRic d t i *
          covariantFieldNormSq g (oneFormEigenSection hRic d i).val x :=
      Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (oneFormEigenSection_norm_nonneg hRic d i x))
    simp_rw [hn]
    rw [integral_const_mul, oneFormEigenSection_norm_integral, mul_one]
  exact scalar_integrable_series hi hs (fun x => (oneFormHeatDiagonal_summable hRic d t ht x).hasSum)

omit [PreconnectedSpace M] in
theorem oneFormHeatDiagonal_integral (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, oneFormHeatDiagonal hRic d t x ∂normalizedVolume g) = oneFormHeatTrace hRic d t := by
  have hi (i : OneFormEigenIndex hRic d) : Integrable
      (fun x => oneFormHeatWeight hRic d t i *
        covariantFieldNormSq g (oneFormEigenSection hRic d i).val x) (normalizedVolume g) :=
    (((oneFormEigenSection hRic d i).property.continuous_normSq (g := g)).const_mul _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Summable (fun i => ∫ x, ‖oneFormHeatWeight hRic d t i *
      covariantFieldNormSq g (oneFormEigenSection hRic d i).val x‖ ∂normalizedVolume g) := by
    apply (oneFormHeat_weight_summable hRic d t ht).congr
    intro i
    have hn (x : M) : ‖oneFormHeatWeight hRic d t i *
        covariantFieldNormSq g (oneFormEigenSection hRic d i).val x‖ =
        oneFormHeatWeight hRic d t i *
          covariantFieldNormSq g (oneFormEigenSection hRic d i).val x :=
      Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le
        (oneFormEigenSection_norm_nonneg hRic d i x))
    simp_rw [hn]
    rw [integral_const_mul, oneFormEigenSection_norm_integral, mul_one]
  unfold oneFormHeatDiagonal oneFormHeatTrace
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  apply tsum_congr
  intro i
  rw [integral_const_mul, oneFormEigenSection_norm_integral, mul_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real-time notation for the genuine one-form heat diagonal and columns. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped ContDiff Manifold _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}
variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormHeatRealColumn (t : ℝ) (e : FrameBundle g) (l : Fin 4) : OneFormL2 o :=
  if ht : 0 < t then oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht) e l else 0

theorem oneFormHeatRealColumn_pos (t : ℝ) (ht : 0 < t) (e : FrameBundle g) (l : Fin 4) :
    oneFormHeatRealColumn hRic d t e l =
      oneFormHeatFrameColumn hRic d t.toNNReal (Real.toNNReal_pos.mpr ht) e l :=
  dite_eq_left ht

def oneFormHeatRealDiagonal (t : ℝ) (x : M) : ℝ :=
  if 0 < t then oneFormHeatDiagonal hRic d t.toNNReal x else 0

theorem oneFormHeatRealDiagonal_columns (t : ℝ) (ht : 0 < t) (e : FrameBundle g) :
    oneFormHeatRealDiagonal hRic d (t + t) e.base =
      ∑ l : Fin 4, ‖oneFormHeatRealColumn hRic d t e l‖ ^ 2 := by
  have hhalf : (t + t).toNNReal / 2 = t.toNNReal := by
    rw [Real.toNNReal_add ht.le ht.le]
    exact add_self_div_two t.toNNReal
  simp only [oneFormHeatRealDiagonal, ite_eq_left (add_pos ht ht),
    oneFormHeatDiagonal_columns hRic d _ (Real.toNNReal_pos.mpr (add_pos ht ht)) e,
    hhalf, oneFormHeatRealColumn_pos hRic d t ht e]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Energy uniqueness for the actual nonnegative Hodge heat generator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_zero_solution (hRic : RicciThree g) (T : ℝ) (hT : 0 ≤ T)
    (u : ℝ → TwoFormL2 o) (hc : ContinuousOn u (Icc 0 T)) (h0 : u 0 = 0)
    (hu : ∀ t ∈ Ioo 0 T, ∃ h : u t ∈ twoFormHodgeDomain hRic,
      HasDerivAt u (-twoFormHodgeGenerator hRic ⟨u t, h⟩) t) :
    ∀ t ∈ Icc 0 T, u t = 0 := by
  let E := fun t => inner ℝ (u t) (u t)
  have hEc : ContinuousOn E (Icc 0 T) := hc.inner hc
  have hEd (t : ℝ) (ht : t ∈ interior (Icc 0 T)) :
      ∃ a : ℝ, HasDerivAt E a t ∧ a ≤ 0 := by
    rw [interior_Icc] at ht
    obtain ⟨h, hd⟩ := hu t ht
    refine ⟨_, hd.inner ℝ hd, ?_⟩
    rw [inner_neg_right, inner_neg_left, real_inner_comm (u t)]
    have hn := twoFormHodgeGenerator_nonneg hRic (⟨u t, h⟩ : twoFormHodgeDomain hRic)
    change 0 ≤ inner ℝ (twoFormHodgeGenerator hRic ⟨u t, h⟩) (u t) at hn
    rw [real_inner_comm] at hn
    linarith only [hn]
  have hmono : AntitoneOn E (Icc 0 T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hEc
      (fun t ht => (hEd t ht).choose_spec.1.differentiableAt.differentiableWithinAt)
      (fun t ht => (hEd t ht).choose_spec.1.deriv ▸ (hEd t ht).choose_spec.2)
  intro t ht
  have he := hmono (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩) ht ht.1
  change inner ℝ (u t) (u t) ≤ inner ℝ (u 0) (u 0) at he
  rw [h0, inner_zero_left] at he
  exact inner_self_eq_zero.mp (le_antisymm he (real_inner_self_nonneg (x := u t)))

theorem twoFormHeat_evolution_unique (hRic : RicciThree g) (T : ℝ) (hT : 0 ≤ T)
    (f : TwoFormL2 o) (u : ℝ → TwoFormL2 o) (hc : ContinuousOn u (Icc 0 T)) (h0 : u 0 = f)
    (hu : ∀ t ∈ Ioo 0 T, ∃ h : u t ∈ twoFormHodgeDomain hRic,
      HasDerivAt u (-twoFormHodgeGenerator hRic ⟨u t, h⟩) t) :
    ∀ t ∈ Icc 0 T, u t = twoFormHeat hRic t.toNNReal f := by
  have hv : Continuous (fun t : ℝ => twoFormHeat hRic t.toNNReal f) :=
    (twoFormHeat_continuous hRic f).comp continuous_real_toNNReal
  have hz : u 0 - twoFormHeat hRic (0 : ℝ).toNNReal f = 0 := by
    rw [h0]
    simp only [Real.toNNReal_zero, twoFormHeat_zero, sub_self]
  have hzero := twoFormHeat_zero_solution hRic T hT
    (fun t => u t - twoFormHeat hRic t.toNNReal f) (hc.sub hv.continuousOn) hz (by
      intro t ht
      obtain ⟨h, hd⟩ := hu t ht
      have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht.1
      have he : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.1.le
      have hh := twoFormHeat_hasDerivAt hRic t.toNNReal ht' f
      rw [he, twoFormHeatDerivative_generator] at hh
      let v : twoFormHodgeDomain hRic :=
        ⟨twoFormHeat hRic t.toNNReal f, twoFormHeat_mem_hodgeDomain hRic t.toNNReal ht' f⟩
      have hm : u t - twoFormHeat hRic t.toNNReal f ∈ twoFormHodgeDomain hRic :=
        (twoFormHodgeDomain hRic).sub_mem h v.property
      refine ⟨hm, ?_⟩
      have hgen : twoFormHodgeGenerator hRic
          ⟨u t - twoFormHeat hRic t.toNNReal f, hm⟩ =
          twoFormHodgeGenerator hRic ⟨u t, h⟩ - twoFormHodgeGenerator hRic v :=
        (twoFormHodgeGenerator hRic).map_sub ⟨u t, h⟩ v
      convert hd.sub hh using 1
      rw [hgen]
      abel)
  intro t ht
  exact sub_eq_zero.mp (hzero t ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Trace and actual coordinate differentiation commute for the two
connection representations used in the de Rham heat operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatFourTrace_partial (A : FourSpace → Mat4) (x : FourSpace)
    (hA : ∀ k, DifferentiableAt ℝ (fun y => A y k k) x) (i : Fin 4) :
    partialDeriv (fun y => (A y).trace) i x = (matrixPartial A i x).trace := by
  unfold Matrix.trace Matrix.diag
  exact heat_partial_finite_sum (fun k y => A y k k) x hA i

theorem heatSixTrace_partial (A : FourSpace → HeatMat6) (x : FourSpace)
    (hA : ∀ k, DifferentiableAt ℝ (fun y => A y k k) x) (i : Fin 4) :
    partialDeriv (fun y => (A y).trace) i x = (heatSixPartial A i x).trace := by
  unfold Matrix.trace Matrix.diag
  exact heat_partial_finite_sum (fun k y => A y k k) x hA i

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.oneConnection_partial_trace (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ Metric.ball 0 D.radius) (i j : Fin 4)
    (hd : ∀ k, DifferentiableAt ℝ (fun y => heatNormalFrameConnection g c D.point i y k k) x) :
    (matrixPartial (heatNormalFrameConnection g c D.point i) j x).trace = 0 := by
  rw [← heatFourTrace_partial _ x hd j]
  have hz : (fun y => (heatNormalFrameConnection g c D.point i y).trace) =ᶠ[𝓝 x]
      fun _ => 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact heatFour_skew_trace _ (D.connection_skew y hy i)
  rw [fourHeat_partial_germ hz j]
  simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]

theorem HeatNormalFrameData.twoConnection_partial_trace (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (i j : Fin 4)
    (hd : ∀ k, DifferentiableAt ℝ (fun y => heatTwoFormConnection g c D.point i y k k) x) :
    (heatSixPartial (heatTwoFormConnection g c D.point i) j x).trace = 0 := by
  rw [← heatSixTrace_partial _ x hd j]
  have hz : (fun y => (heatTwoFormConnection g c D.point i y).trace) = fun _ => 0 :=
    funext (fun _ => heatTwoFormConnectionMatrix_trace _)
  rw [hz]
  simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The source of the first radial amplitude has a signed trace equal
to the leading scalar amplitude times the quadratic connection term. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatBundleOperator_leading (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (U : FourSpace → ℝ)
    (x : FourSpace) (k l : Fin 6) :
    fourHeatBundleOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k =
      (if k = l then 1 else 0) * fourHeatLocalOperator a b 0 U x +
        (∑ i, B i k l * partialDeriv U i x) + U x * C k l := by
  have hf (q : Fin 6) : (fun y => U y * (if q = l then 1 else 0)) =
      (fun y => (if q = l then 1 else 0) * U y) := by funext y; ring
  unfold fourHeatBundleOperator fourHeatBundleFirst fourHeatBundleZero
  simp_rw [hf, fourHeatLocalOperator_const_mul, fourHeat_partial_const_mul]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem fourHeat_leading_signed_source (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (U : FourSpace → ℝ) (x : FourSpace)
    (hB : ∀ i, (twoFormHodgeMatrix * B i).trace = 0) :
    (twoFormHodgeMatrix * (show HeatMat6 from fun k l =>
      -fourHeatBundleOperator a b B C
        (fun y q => U y * (if q = l then 1 else 0)) x k)).trace =
      -U x * (twoFormHodgeMatrix * C).trace := by
  have hm : (show HeatMat6 from fun k l =>
      -fourHeatBundleOperator a b B C
        (fun y q => U y * (if q = l then 1 else 0)) x k) =
      -(fourHeatLocalOperator a b 0 U x • (1 : HeatMat6) +
        (∑ i, partialDeriv U i x • B i) + U x • C) := by
    ext k l
    rw [fourHeatBundleOperator_leading]
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sum_apply, smul_eq_mul]
    have hs : (∑ i, B i k l * partialDeriv U i x) =
        ∑ i, partialDeriv U i x * B i k l := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring
  rw [hm]
  simp only [Matrix.mul_neg, Matrix.mul_add, Matrix.mul_sum, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_neg, Matrix.trace_add, Matrix.trace_sum,
    Matrix.trace_smul, twoFormHodgeMatrix_trace, hB, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, zero_add]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalBundleExtension.firstSource (E : HeatNormalBundleExtension D)
    (x : FourSpace) : HeatMat6 := fun k l =>
  -fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
    (fun y q => E.base.U y * (if q = l then 1 else 0)) x k

theorem HeatNormalBundleExtension.firstSource_regular (E : HeatNormalBundleExtension D)
    (k l : Fin 6) : ContDiff ℝ 2 (fun x => E.firstSource x k l) := by
  apply ContDiff.neg
  apply fourHeatBundleOperator_contDiff 2 E.base.a E.base.b E.B E.C
  · intro i j
    exact (E.base.a_regular i j).of_le (by norm_num)
  · intro i
    exact (E.base.b_regular i).of_le (by norm_num)
  · intro i a b
    exact (E.B_regular i a b).of_le (by norm_num)
  · intro a b
    exact (E.C_regular a b).of_le (by norm_num)
  · intro q
    exact (E.base.U_regular.of_le (by norm_num)).mul contDiff_const

theorem HeatNormalBundleExtension.B_signed_near (E : HeatNormalBundleExtension D) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i, (twoFormHodgeMatrix * E.B x i).trace = 0 := by
  filter_upwards [E.B_near] with x hx
  intro i
  rw [hx]
  simp only [heatNormalBundleFirst, fourHeatConnectionFirst, Matrix.mul_smul,
    Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum,
    heatTwoFormConnectionMatrix_signed_trace, heatTwoFormConnection, smul_eq_mul,
    mul_zero, Finset.sum_const_zero]

theorem HeatNormalBundleExtension.firstSource_signed_near (E : HeatNormalBundleExtension D) :
    (fun x => (twoFormHodgeMatrix * E.firstSource x).trace) =ᶠ[𝓝 0]
      (fun x => E.base.U x * heatNormalConnectionQuadratic (D := D) E.base.a x) := by
  filter_upwards [E.B_signed_near, E.C_signed_near] with x hB hC
  change (twoFormHodgeMatrix * (show HeatMat6 from fun k l =>
    -fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
      (fun y q => E.base.U y * (if q = l then 1 else 0)) x k)).trace = _
  rw [fourHeat_leading_signed_source _ _ _ _ _ x hB, hC]
  ring

theorem HeatNormalBundleExtension.first_amplitude_signed_radial
    (E : HeatNormalBundleExtension D) (x : FourSpace) :
    (twoFormHodgeMatrix * E.amplitude 1 x).trace =
      fourHeatWeightedRadialAverage 0 E.base.U
        (fun y => (twoFormHodgeMatrix * E.firstSource y).trace) x := by
  change (twoFormHodgeMatrix * (show HeatMat6 from fun k l =>
    fourHeatWeightedRadialAverage 0 E.base.U (fun y => E.firstSource y k l) x)).trace = _
  apply heatSignedTrace_weightedRadial
  · exact E.base.U_regular.continuous
  · exact continuous_pi (fun k => continuous_pi (fun l => (E.firstSource_regular k l).continuous))
  · exact fun y => (E.base.U_pos y).ne'

end
end PositiveEinsteinFour.Geometry
end


section

/-! Gaussian concentration gives the weighted square-integral growth t⁻². -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCutoffColumn_square_integral_bound (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ) (l : Fin 6) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1,
      (∫ x, frameExponentialJacobian g o e x * ‖heatNormalCutoffColumn E χ t l x‖ ^ 2) ≤ C / t ^ 2 := by
  obtain ⟨B, hB, hb⟩ := heatNormalPolynomialColumn_weight_bound E χ hχ.continuous hc l
  refine ⟨B / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro t ht
  have hpt (x : FourSpace) : frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn E χ t l x‖ ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [heatNormalCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      _ = (frameExponentialJacobian g o e x * ‖heatNormalPolynomialColumn E χ t l x‖ ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb t ⟨ht.1.le, ht.2⟩ x) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hm : Continuous (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn E χ t l x‖ ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((heatNormalCutoffColumn_regular E χ hχ t l).continuous.norm.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn E χ t l x‖ ^ 2) :=
    hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hpt x)
  calc
    _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hpt
    _ = _ := by
      rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact C4 normal amplitude and its actual coefficient image lie
in the global L2 space, and the former belongs to the Hodge generator domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalHodgeImage (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : TwoFormL2 o :=
  heatNormalAmplitudeL2 D C hCt hP hD (heatNormalOperatorAmplitude E a)
    (heatNormalOperatorAmplitude_regular E a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOperatorAmplitude_support E a))
    ((heatNormalOperatorAmplitude_support E a).trans hs)

theorem HeatNormalBundleExtension.compact_hodge_domain_near
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ (C : OpenPartialHomeomorph FourSpace M)
      (_hE : EqOn C (frameExponential g o e) C.source)
      (hCt : C.target ⊆ (chartAt FourSpace c).source)
      (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
      (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ C.source), tsupport a ⊆ Metric.ball 0 r →
      ∃ hf : heatNormalAmplitudeL2 D C hCt hP hD a (ha.of_le (by norm_num)) hc hs ∈
          twoFormHodgeDomain hRic,
        twoFormHodgeGenerator hRic ⟨heatNormalAmplitudeL2 D C hCt hP hD a
          (ha.of_le (by norm_num)) hc hs, hf⟩ = heatNormalHodgeImage E C hCt hP hD a ha hc hs := by
  obtain ⟨r, hr, hgreen⟩ := E.compact_green_near he hRic
  refine ⟨r, hr, ?_⟩
  intro C hE hCt hP hD a ha hc hs hsmall
  apply twoFormHodgeDomain_of_distribution hRic
  intro v
  have hleft := heatNormalAmplitudeL2_pairing_normal D C hE hCt hP hD a
    (ha.of_le (by norm_num)) hc hs (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)
  have hright := heatNormalAmplitudeL2_pairing_normal D C hE hCt hP hD
    (heatNormalOperatorAmplitude E a) (heatNormalOperatorAmplitude_regular E a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOperatorAmplitude_support E a))
    ((heatNormalOperatorAmplitude_support E a).trans hs) (v : SmoothL2TwoForm o)
  exact hleft.trans ((congrArg ((normalizedChartFactor g).toReal * ·)
    (hgreen a (ha.of_le (by norm_num)) hc hsmall v)).trans hright.symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact component-integral pairing for compact normal amplitudes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneAmplitudeL2_pairing_sum
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : smoothCovariantFields M 1) :
    inner ℝ (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothOneFormL2Linear v) =
      (normalizedChartFactor g).toReal * ∑ k : Fin 4, ∫ x,
        a x k * (frameExponentialJacobian g o e x *
          heatNormalOneValue c D.point v x k) := by
  let f := fun k x => frameExponentialJacobian g o e x *
    heatNormalOneValue c D.point v x k
  have hV : ContinuousOn (heatNormalOneValue c D.point v)
      C.source := by
    intro x hx
    have hv : ContDiffAt ℝ 2 (heatNormalOneValue c D.point v) x := by
      apply (contDiffAt_piLp (p := 2)).mpr
      intro k
      exact heatNormalOneFormValue_regular 2 c D.point v x
        (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx)) k
    exact hv.continuousAt.continuousWithinAt
  have hf (k : Fin 4) : ContinuousOn (f k) C.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      ((EuclideanSpace.proj k).continuous.comp_continuousOn hV)
  have hi (k : Fin 4) : Integrable (fun x => a x k * f k x) := by
    have hak := ((contDiff_piLp (p := 2)).mp ha k).continuous
    have hck : HasCompactSupport (fun x => a x k) :=
      hc.of_isClosed_subset (isClosed_tsupport _) (heatOneAmplitude_component_support a k)
    have hfk (x : FourSpace) (hx : x ∈ tsupport (fun y => a y k)) : ContinuousAt (f k) x :=
      (hf k).continuousAt (C.open_source.mem_nhds (hs (heatOneAmplitude_component_support a k hx)))
    simpa only [mul_comm] using fourHeat_local_product_integrable (f k) (fun x => a x k) hak hck hfk
  have hpair := heatNormalOneAmplitudeL2_pairing_normal D C hE hCt hP hD a ha hc hs v
  apply hpair.trans
  congr 1
  calc
    _ = ∫ x, ∑ k : Fin 4, a x k * f k x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [PiLp.inner_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      change frameExponentialJacobian g o e x *
        (heatNormalOneValue c D.point v x k * a x k) = _
      dsimp only [f]
      ring
    _ = _ := integral_finsetSum _ (fun k _ => hi k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 image of the compact one-form coefficient operator,
with its distributional identity against every smooth test section. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalOneHodgeImage (E : HeatNormalOneExtension D)
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : OneFormL2 o :=
  heatNormalOneAmplitudeL2 D C hCt hP hD (heatNormalOneOperatorAmplitude E a)
    (heatNormalOneOperatorAmplitude_regular E a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneOperatorAmplitude_support E a))
    ((heatNormalOneOperatorAmplitude_support E a).trans hs)

theorem HeatNormalOneExtension.compact_operator_pairing_near
    (E : HeatNormalOneExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ (C : OpenPartialHomeomorph FourSpace M)
      (_hE : EqOn C (frameExponential g o e) C.source)
      (hCt : C.target ⊆ (chartAt FourSpace c).source)
      (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
      (a : FourSpace → FourSpace) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ C.source), tsupport a ⊆ Metric.ball 0 r →
      ∀ v : smoothCovariantFields M 1,
        inner ℝ (heatNormalOneAmplitudeL2 D C hCt hP hD a (ha.of_le (by norm_num)) hc hs)
          (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (heatNormalOneHodgeImage E C hCt hP hD a ha hc hs)
          (smoothOneFormL2Linear v) := by
  obtain ⟨r, hr, hgreen⟩ := E.compact_green_near he hRic
  refine ⟨r, hr, ?_⟩
  intro C hE hCt hP hD a ha hc hs hsmall v
  have hleft := heatNormalOneAmplitudeL2_pairing_normal D C hE hCt hP hD a
    (ha.of_le (by norm_num)) hc hs (smoothOneFormHodgeLaplacian (o := o) v)
  have hright := heatNormalOneAmplitudeL2_pairing_normal D C hE hCt hP hD
    (heatNormalOneOperatorAmplitude E a) (heatNormalOneOperatorAmplitude_regular E a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneOperatorAmplitude_support E a))
    ((heatNormalOneOperatorAmplitude_support E a).trans hs) v
  exact hleft.trans ((congrArg ((normalizedChartFactor g).toReal * ·)
    (hgreen a (ha.of_le (by norm_num)) hc hsmall v)).trans hright.symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact Gaussian-free column and its uniform density-weighted bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalOnePolynomialColumn (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 4) (x : FourSpace) : FourSpace :=
  WithLp.toLp 2 (fun k => χ x * fourHeatPolynomial (fun m y => E.amplitude m y k l) t x)

theorem heatNormalOnePolynomialColumn_continuous (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 4) :
    Continuous (fun z : ℝ × FourSpace => heatNormalOnePolynomialColumn E χ z.1 l z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  exact (hχ.comp continuous_snd).mul
    (fourHeatPolynomial_joint_continuous _
      (fun m => (E.amplitude_regular m (by omega) k l).continuous))

theorem heatNormalOneCutoffColumn_gaussian (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) (x : FourSpace) :
    heatNormalOneCutoffColumn E χ t l x =
      fourHeatGaussian t x • heatNormalOnePolynomialColumn E χ t l x := by
  apply WithLp.ofLp_injective 2
  funext k
  change χ x * (fourHeatGaussian t x * _) = fourHeatGaussian t x * (χ x * _)
  unfold fourHeatOnePolynomial fourHeatPolynomial
  ring

theorem heatNormalOnePolynomialColumn_weight_bound (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ) (l : Fin 4) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      frameExponentialJacobian g o e x * ‖heatNormalOnePolynomialColumn E χ t l x‖ ^ 2 ≤ B := by
  let W := fun z : ℝ × FourSpace => frameExponentialJacobian g o e z.2 *
    ‖heatNormalOnePolynomialColumn E χ z.1 l z.2‖ ^ 2
  have hW : Continuous W := ((frameExponentialJacobian_continuous g o e).comp continuous_snd).mul
    ((heatNormalOnePolynomialColumn_continuous E χ hχ l).norm.pow 2)
  obtain ⟨B, hb⟩ := (isCompact_Icc.prod hc).bddAbove_image hW.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hb ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left _ _)
  · have hzero : heatNormalOnePolynomialColumn E χ t l x = 0 := by
      apply WithLp.ofLp_injective 2
      funext k
      change χ x * _ = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    rw [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact le_max_right _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual compact kernel and its residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCutoffColumn_joint_continuousOn (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (l : Fin 4) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalOneCutoffColumn E χ z.1 l z.2)
      (Ioi 0 ×ˢ univ) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro k z hz
  exact (heatNormalOneCutoffParametrix_joint_contDiffAt E χ hχ z hz.1 k l).continuousAt.continuousWithinAt

theorem heatNormalOneOperatorColumn_joint_continuousOn (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (l : Fin 4) :
    ContinuousOn (fun z : ℝ × FourSpace =>
      heatNormalOneOperatorAmplitude E (heatNormalOneCutoffColumn E χ z.1 l) z.2)
      (Ioi 0 ×ˢ univ) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro k z hz
  exact (fourHeatOneOperator_joint_continuousAt E.base.a E.base.b E.B E.C
    (fun w k => heatNormalOneCutoffParametrix E χ w.1 w.2 k l) z
    (fun i j => (E.base.a_regular i j).continuous.continuousAt)
    (fun i => (E.base.b_regular i).continuous.continuousAt)
    (fun i k l => (E.B_regular i k l).continuous.continuousAt)
    (fun k l => (E.C_regular k l).continuous.continuousAt)
    (fun k => heatNormalOneCutoffParametrix_joint_contDiffAt E χ hχ z hz.1 k l) k).continuousWithinAt

theorem heatNormalOneResidualColumn_joint_continuousOn (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (l : Fin 4) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalOneResidualColumn E χ z.1 l z.2)
      (Ioi 0 ×ˢ univ) :=
  (heatNormalOneTimeColumn_joint_continuousOn E χ hχ.continuous l).add
    (heatNormalOneOperatorColumn_joint_continuousOn E χ hχ l)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weak time differentiation of the actual global parametrix, with its
derivative represented by the constructed global L2 time column. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalGlobalParametrixColumn_weak_deriv (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (ht : 0 < t) (l : Fin 6)
    (v : SmoothL2TwoForm o) :
    HasDerivAt (fun s => inner ℝ (heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs s l)
        (smoothTwoFormToL2 v))
      (inner ℝ (heatNormalGlobalTimeColumn E C hCt hP hD χ hχ hc hs t l)
        (smoothTwoFormToL2 v)) t := by
  let f := fun k x => frameExponentialJacobian g o e x *
    heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val x k
  have hV : ContinuousOn (heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val)
      C.source := by
    intro x hx
    exact (heatNormalTwoFormValue_contDiffAt 2 (v : smoothTwoForms o).property c D.point x
      (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx))).continuousAt.continuousWithinAt
  have hf (k : Fin 6) : ContinuousOn (f k) C.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      ((EuclideanSpace.proj k).continuous.comp_continuousOn hV)
  have hχf (k : Fin 6) : Continuous (fun x => χ x * f k x) :=
    heat_continuous_mul_of_tsupport_subset hχ.continuous C.open_source (hf k) hs
  have hd := (HasDerivAt.sum (u := Finset.univ) fun k _ =>
    heatNormalCutoffParametrix_pairing_deriv E χ (f k) (hχf k) hc t ht k l).const_mul
      (normalizedChartFactor g).toReal
  have hfun : (fun s => inner ℝ (heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs s l)
      (smoothTwoFormToL2 v)) = fun s => (normalizedChartFactor g).toReal *
        ∑ k : Fin 6, ∫ x, heatNormalCutoffParametrix E χ s x k l * f k x := by
    funext s
    exact heatNormalAmplitudeL2_pairing_sum C hE hCt hP hD (heatNormalCutoffColumn E χ s l)
      (heatNormalCutoffColumn_regular E χ hχ s l)
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E χ s l))
      ((heatNormalCutoffColumn_support E χ s l).trans hs) v
  have hval : inner ℝ (heatNormalGlobalTimeColumn E C hCt hP hD χ hχ hc hs t l)
      (smoothTwoFormToL2 v) = (normalizedChartFactor g).toReal *
        ∑ k : Fin 6, ∫ x, deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t * f k x := by
    have hpair := heatNormalAmplitudeL2_pairing_sum C hE hCt hP hD (heatNormalTimeColumn E χ t l)
      (heatNormalTimeColumn_regular E χ hχ t l)
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalTimeColumn_support E χ t l))
      ((heatNormalTimeColumn_support E χ t l).trans hs) v
    exact hpair.trans (congrArg ((normalizedChartFactor g).toReal * ·)
      (Finset.sum_congr rfl fun k _ => integral_congr_ae (Eventually.of_forall fun x =>
        congrArg (· * f k x) (heatNormalTimeColumn_component E χ t ht l k x))))
  simp only [Finset.sum_apply] at hd
  rw [← hfun, ← hval] at hd
  exact hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity throughout the common normal ball, with the actual
operator and no additional small-support neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.compact_green (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ ball 0 r) (v : smoothTwoForms o) :
    (∫ x, frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalTwoFormValue o c N.frameData.point (smoothHodgeLaplacian hRic v).val x)) =
    ∫ x, frameExponentialJacobian g o e x *
      inner ℝ (heatNormalOperatorAmplitude N.extension a x)
        (heatNormalTwoFormValue o c N.frameData.point v.val x) := by
  let u := fun x k => a x k
  let w := fun x k => heatNormalTwoFormValue o c N.frameData.point v.val x k
  have hu (k : Fin 6) : ContDiff ℝ 2 (fun x => u x k) :=
    (contDiff_piLp (p := 2)).mp ha k
  have hsc (k : Fin 6) : tsupport (fun x => u x k) ⊆ ball 0 r :=
    (heatAmplitude_component_support a k).trans hs
  have hcc (k : Fin 6) : HasCompactSupport (fun x => u x k) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (heatAmplitude_component_support a k)
  have hw (x : FourSpace) (hx : x ∈ ball 0 r) (k : Fin 6) :
      ContDiffAt ℝ 2 (fun y => w y k) x := by
    have h := heatNormalTwoFormValue_contDiffAt 2 v.property c N.frameData.point x
      (N.point_regular x hx) (N.frameData.in_chart x (ball_subset_ball N.radius_le hx))
    exact (contDiffAt_piLp (p := 2)).mp h k
  have hop (x : FourSpace) (k : Fin 6) : heatNormalOperatorAmplitude N.extension a x k =
      fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatTwoFormConnection g c N.frameData.point) (heatNormalPotential g c N.frameData.point x) u x k :=
    N.extension.compact_operator_eq (ball 0 r) (fun y hy => N.connection_operator y hy) a ha hs x k
  have htest (x : FourSpace) : frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalTwoFormValue o c N.frameData.point (smoothHodgeLaplacian hRic v).val x) =
      ∑ k : Fin 6, frameExponentialJacobian g o e x * u x k *
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c N.frameData.point) (heatNormalPotential g c N.frameData.point x) w x k := by
    rw [heat_weighted_inner_sum]
    by_cases hx : x ∈ ball 0 r
    · apply Finset.sum_congr rfl
      intro k _
      have hactual := N.actual_bundle_operator hRic x hx v k
      have hconv := heatNormalConnectionOperator_eq N.frameData w x
        (fun i k l => ((N.green_regular x hx).1 i k l).differentiableAt one_ne_zero) (hw x hx) k
      rw [← hconv] at hactual
      rw [hactual]
    · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      have hzk (k : Fin 6) : u x k = 0 := by change a x k = 0; rw [hz]; rfl
      simp only [hz, PiLp.zero_apply, hzk, mul_zero, zero_mul, Finset.sum_const_zero]
  have hg := fourHeatCovariantOperator_compact_adjoint
    (heatTwoFormConnection g c N.frameData.point) (fun x => (heatNormalMetric g o e x)⁻¹)
    (frameExponentialJacobian g o e) (heatNormalPotential g c N.frameData.point) u w (ball 0 r)
    hu hcc hsc hw (fun x hx => (N.green_regular x hx).1) (fun x hx => (N.green_regular x hx).2.1)
    (fun x hx => (N.green_regular x hx).2.2.1) (fun x hx => (N.green_regular x hx).2.2.2.1.ne')
    (fun x hx => (N.green_regular x hx).2.2.2.2)
    (fun _ _ i => heatTwoFormConnectionMatrix_skew _)
    (fun x _ i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun x hx => N.frameData.potential_symmetric x (ball_subset_ball N.radius_le hx))
  calc
    _ = ∫ x, ∑ k : Fin 6, frameExponentialJacobian g o e x * u x k *
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c N.frameData.point) (heatNormalPotential g c N.frameData.point x) w x k := by
      apply integral_congr_ae
      exact Eventually.of_forall htest
    _ = _ := hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heat_weighted_inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hop]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common density-weighted polynomial bound for the actual nearby
normal-frame columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilyPolynomialColumn (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 6) (z : HeatRadialFrameSpace) : TwoFormFour :=
  WithLp.toLp 2 (fun k => χ z.1 *
    fourHeatPolynomial (fun m x => E.amplitude m (x, z.2) k l) t z.1)

theorem heatFamilyPolynomialColumn_continuous (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 6) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyPolynomialColumn E χ z.1 l z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  exact (hχ.comp (continuous_fst.comp continuous_snd)).mul
    (heatFamilyPolynomial_continuous _ (fun m => (E.amplitude_regular m (by omega) k l).continuous))

theorem heatFamilyPolynomial_weight_bound (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x l,
      (E.U (x, q) ^ 2)⁻¹ * ‖heatFamilyPolynomialColumn E χ t l (x, q)‖ ^ 2 ≤ B := by
  have hb (l : Fin 6) : ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      (E.U (x, q) ^ 2)⁻¹ * ‖heatFamilyPolynomialColumn E χ t l (x, q)‖ ^ 2 ≤ B := by
    let W := fun z : ℝ × HeatRadialFrameSpace => (E.U z.2 ^ 2)⁻¹ *
      ‖heatFamilyPolynomialColumn E χ z.1 l z.2‖ ^ 2
    have hW : Continuous W :=
      (((E.U_regular.continuous.comp continuous_snd).pow 2).inv₀
        (fun z => pow_ne_zero 2 (E.U_pos z.2).ne')).mul
        ((heatFamilyPolynomialColumn_continuous E χ hχ l).norm.pow 2)
    obtain ⟨B, hB⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image hW.continuousOn
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro q hq t ht x
    by_cases hx : x ∈ tsupport χ
    · exact (hB ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
    · have hz : heatFamilyPolynomialColumn E χ t l (x, q) = 0 := by
        apply WithLp.ofLp_injective 2
        funext k
        change χ x * _ = 0
        rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
      rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      exact le_max_right _ _
  choose B hB hb using hb
  refine ⟨∑ l, B l, Finset.sum_nonneg (fun l _ => hB l), ?_⟩
  intro q hq t ht x l
  exact (hb l q hq t ht x).trans (Finset.single_le_sum (fun a _ => hB a) (Finset.mem_univ l))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.polynomialColumn_family (N : HeatCommonNormalMember g o c E r e)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) (x : FourSpace) :
    heatNormalPolynomialColumn N.extension χ t l x =
      heatFamilyPolynomialColumn E χ t l (x, frameCoordinateState g c e) := by
  apply WithLp.ofLp_injective 2
  funext k
  change χ x * fourHeatPolynomial _ t x = χ x * fourHeatPolynomial _ t x
  have hu : (fun (m : Fin 4) y => N.extension.amplitude m y k l) =
      (fun (m : Fin 4) y => E.amplitude m (y, frameCoordinateState g c e) k l) := by
    funext m y
    exact congrArg (fun f : FourSpace → HeatMat6 => f y k l) (N.amplitude_family m (by omega))
  rw [hu]


theorem heatUniformPolynomial_weight_bound (E : HeatFamilySmoothCoefficients) (r : ℝ)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonNormalMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Icc (0 : ℝ) 1, ∀ x l,
      frameExponentialJacobian g o e x * ‖heatNormalPolynomialColumn N.extension χ t l x‖ ^ 2 ≤ B := by
  obtain ⟨B, hB, hb⟩ := heatFamilyPolynomial_weight_bound E χ hχ hc K hK
  refine ⟨B, hB, ?_⟩
  intro e N hq t ht x l
  by_cases hx : x ∈ tsupport χ
  · have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.metric_pos x (hχs hx)))
    rw [← (N.actual x (hχs hx)).2.2.2.2, N.U_family] at hh
    rw [eq_inv_of_mul_eq_one_right hh, N.polynomialColumn_family]
    exact hb _ hq t ht x l
  · have hz : heatNormalPolynomialColumn N.extension χ t l x = 0 := by
      apply WithLp.ofLp_injective 2
      funext k
      change χ x * _ = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact hB

end
end PositiveEinsteinFour.Geometry
end


section

/-! The de Rham heat density has the Euler index as its integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

omit [PreconnectedSpace M] in
theorem scalarHeatDiagonal_integrable (t : ℝ≥0) (ht : 0 < t) :
    Integrable (scalarHeatDiagonal g o d t ht) (normalizedVolume g) := by
  have hc := (scalarHeatKernel_continuous g o d t ht).comp (continuous_id.prodMk continuous_id)
  change Continuous (fun x : M => scalarHeatKernel g o d t ht x x) at hc
  simp_rw [scalarHeatKernel_diagonal] at hc
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [PreconnectedSpace M] in
theorem twoFormHeatDiagonal_integrable (t : ℝ≥0) (ht : 0 < t) :
    Integrable (fun x => twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x))
      (normalizedVolume g) := by
  let F := fun (i : TwoFormEigenIndex (o := o) hRic) (x : M) =>
    ‖(twoFormHeatSection hRic (t / 2) (half_pos ht) (twoFormEigenvector hRic i)).val x‖ ^ 2
  have hi (i : TwoFormEigenIndex (o := o) hRic) : Integrable (F i) (normalizedVolume g) :=
    ((smoothTwoForm_norm_continuous _).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hs : Summable (fun i => ∫ x, ‖F i x‖ ∂normalizedVolume g) := by
    apply (twoFormHeat_weight_square_summable (o := o) hRic (t / 2) (half_pos ht)).congr
    intro i
    simp only [F, Real.norm_eq_abs, abs_sq]
    exact (twoFormHeatSection_eigen_integral hRic (t / 2) (half_pos ht) i).symm
  apply scalar_integrable_series hi hs
  intro x
  rw [twoFormHeatKernel_diagonal_trace]
  exact (twoFormHeatSection_pointwise_square_summable hRic (t / 2) (half_pos ht) x).hasSum

def hodgeHeatDensity (t : ℝ≥0) (ht : 0 < t) (x : M) : ℝ :=
  2 * scalarHeatDiagonal g o d t ht x - 2 * oneFormHeatDiagonal hRic d t x +
    twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x)

theorem hodgeHeatDensity_integrable (t : ℝ≥0) (ht : 0 < t) :
    Integrable (hodgeHeatDensity hRic d t ht) (normalizedVolume g) :=
  (((scalarHeatDiagonal_integrable d t ht).const_mul 2).sub
    ((oneFormHeatDiagonal_integrable hRic d t ht).const_mul 2)).add
      (twoFormHeatDiagonal_integrable hRic t ht)

theorem hodgeHeatDensity_integral (t : ℝ≥0) (ht : 0 < t) :
    (∫ x, hodgeHeatDensity hRic d t ht x ∂normalizedVolume g) =
      (hodgeComplexEuler g o : ℝ) := by
  have h0 := (scalarHeatDiagonal_integrable d t ht).const_mul 2
  have h1 := (oneFormHeatDiagonal_integrable hRic d t ht).const_mul 2
  have h2 := twoFormHeatDiagonal_integrable (o := o) hRic t ht
  have he : (∫ x, hodgeHeatDensity hRic d t ht x ∂normalizedVolume g) =
      ((∫ x, 2 * scalarHeatDiagonal g o d t ht x ∂normalizedVolume g) -
        ∫ x, 2 * oneFormHeatDiagonal hRic d t x ∂normalizedVolume g) +
        ∫ x, twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x) ∂normalizedVolume g := by
    exact (integral_add (h0.sub h1) h2).trans
      (congrArg (· + ∫ x, twoFormFiberTrace (twoFormHeatKernel (o := o) hRic t ht x x)
        ∂normalizedVolume g) (integral_sub h0 h1))
  rw [he, integral_const_mul, integral_const_mul, scalarHeatDiagonal_integral g o d t ht,
    oneFormHeatDiagonal_integral hRic d t ht, twoFormHeatKernel_trace_integral hRic t ht]
  exact hodgeHeat_supertrace hRic d t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed Hessian of the actual first heat amplitude at the center.
Only the curvature-square contribution survives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_partial_second_germ {f h : FourSpace → ℝ} {x : FourSpace}
    (he : f =ᶠ[𝓝 x] h) (i j : Fin 4) :
    partialDeriv (partialDeriv f i) j x = partialDeriv (partialDeriv h i) j x := by
  have hp : partialDeriv f i =ᶠ[𝓝 x] partialDeriv h i :=
    he.eventuallyEq_nhds.mono (fun _ h => fourHeat_partial_germ h i)
  exact fourHeat_partial_germ hp j

theorem fourHeatWeightedRadialAverage_second_of_vanishing_jet
    (m : ℕ) (U F Q : FourSpace → ℝ) (hU : ContDiff ℝ 2 U) (hF : ContDiff ℝ 2 F)
    (hU0 : ∀ x, U x ≠ 0) (hU1 : U 0 = 1)
    (hQ : (fun x => F x / U x) =ᶠ[𝓝 0] Q)
    (hQ0 : Q 0 = 0) (hQ1 : ∀ i, partialDeriv Q i 0 = 0) (i j : Fin 4) :
    partialDeriv (partialDeriv (fourHeatWeightedRadialAverage m U F) i) j 0 =
      partialDeriv (partialDeriv Q i) j 0 / (m + 3 : ℝ) := by
  have hv : F 0 / U 0 = Q 0 := hQ.self_of_nhds
  rw [fourHeatWeightedRadialAverage_second_zero m U F hU hF hU0,
    hv, hQ0, fourHeat_partial_germ hQ j, fourHeat_partial_germ hQ i,
    hQ1 j, hQ1 i, heat_partial_second_germ hQ i j, hU1]
  simp only [zero_div, mul_zero, zero_add, one_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.quadratic_second_curvature
    {f : OrthonormalFrame g c} (D : HeatNormalFrameData g o c ⟨c, f⟩)
    (a : FourSpace → Mat4) (ha : ∀ r s, ContDiffAt ℝ 2 (fun x => a x r s) 0)
    (ha0 : a 0 = 1) (i : Fin 4) :
    partialDeriv (partialDeriv (heatNormalConnectionQuadratic (D := D) a) i) i 0 =
      (1 / 2 : ℝ) * ∑ r, (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i r *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i r).trace := by
  rw [D.quadratic_second a ha ha0 i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hm : heatSixPartial (heatTwoFormConnection g c D.point r) i 0 =
      (1 / 2 : ℝ) • twoFormConnectionCurvatureMatrix
        (twoFormMetricCurvatureTensor g ⟨c, f⟩) i r := by
    ext k l
    exact D.twoForm_connection_half_curvature i r k l
  rw [hm]
  simp only [Matrix.mul_add, Matrix.trace_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  ring

theorem HeatNormalBundleExtension.first_amplitude_signed_second
    {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}
    (E : HeatNormalBundleExtension D) (i : Fin 4) :
    partialDeriv (partialDeriv (fun x => (twoFormHodgeMatrix * E.amplitude 1 x).trace) i) i 0 =
      (1 / 6 : ℝ) * ∑ r, (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i r *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i r).trace := by
  let F := fun x => (twoFormHodgeMatrix * E.firstSource x).trace
  let Q := heatNormalConnectionQuadratic (D := D) E.base.a
  have hF : ContDiff ℝ 2 F := by
    exact heatSignedTraceLinear.toContinuousLinearMap.contDiff.comp
      (contDiff_pi.mpr (fun k => contDiff_pi.mpr (fun l => E.firstSource_regular k l)))
  have hU : ContDiff ℝ 2 E.base.U := E.base.U_regular.of_le (by norm_num)
  have hU0 : ∀ x, E.base.U x ≠ 0 := fun x => (E.base.U_pos x).ne'
  have hU1 : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o ⟨c, f⟩)
  have hQ : (fun x => F x / E.base.U x) =ᶠ[𝓝 0] Q := by
    filter_upwards [E.firstSource_signed_near] with x hx
    change (twoFormHodgeMatrix * E.firstSource x).trace / E.base.U x = Q x
    rw [hx]
    exact mul_div_cancel_left₀ _ (hU0 x)
  have ha (r s : Fin 4) : ContDiffAt ℝ 2 (fun x => E.base.a x r s) 0 :=
    ((E.base.a_regular r s).of_le (by norm_num)).contDiffAt
  have ha0 : E.base.a 0 = 1 := by
    rw [E.base.a_near.self_of_nhds]
    change (heatNormalMetric g o ⟨c, f⟩ 0)⁻¹ = 1
    rw [heatNormalMetric_zero]
    simp
  have he : (fun x => (twoFormHodgeMatrix * E.amplitude 1 x).trace) =
      fourHeatWeightedRadialAverage 0 E.base.U F :=
    funext E.first_amplitude_signed_radial
  rw [he, fourHeatWeightedRadialAverage_second_of_vanishing_jet 0 E.base.U F Q hU hF hU0 hU1 hQ
    (D.quadratic_zero E.base.a) (D.quadratic_partial_zero E.base.a ha) i i,
    D.quadratic_second_curvature E.base.a ha ha0 i]
  norm_num
  ring

theorem HeatNormalBundleExtension.first_amplitude_signed_partial
    {D : HeatNormalFrameData g o c e} (E : HeatNormalBundleExtension D) (i : Fin 4) :
    partialDeriv (fun x => (twoFormHodgeMatrix * E.amplitude 1 x).trace) i 0 = 0 := by
  let F := fun x => (twoFormHodgeMatrix * E.firstSource x).trace
  let Q := heatNormalConnectionQuadratic (D := D) E.base.a
  have hF : ContDiff ℝ 2 F :=
    heatSignedTraceLinear.toContinuousLinearMap.contDiff.comp
      (contDiff_pi.mpr (fun k => contDiff_pi.mpr (fun l => E.firstSource_regular k l)))
  have hU : ContDiff ℝ 2 E.base.U := E.base.U_regular.of_le (by norm_num)
  have hU0 : ∀ x, E.base.U x ≠ 0 := fun x => (E.base.U_pos x).ne'
  have hQ : (fun x => F x / E.base.U x) =ᶠ[𝓝 0] Q := by
    filter_upwards [E.firstSource_signed_near] with x hx
    change (twoFormHodgeMatrix * E.firstSource x).trace / E.base.U x = Q x
    rw [hx]
    exact mul_div_cancel_left₀ _ (hU0 x)
  have hv : F 0 / E.base.U 0 = 0 := hQ.self_of_nhds.trans (D.quadratic_zero E.base.a)
  have hp : partialDeriv (fun x => F x / E.base.U x) i 0 = 0 :=
    (fourHeat_partial_germ hQ i).trans (D.quadratic_partial_zero E.base.a
      (fun r s => ((E.base.a_regular r s).of_le (by norm_num)).contDiffAt) i)
  have he : (fun x => (twoFormHodgeMatrix * E.amplitude 1 x).trace) =
      fourHeatWeightedRadialAverage 0 E.base.U F := funext E.first_amplitude_signed_radial
  rw [he, fourHeatWeightedRadialAverage_partial_zero 0 E.base.U F hU hF hU0 i, hv, hp]
  simp only [zero_div, mul_zero, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual zeroth-order coefficient has zero alternating degree trace.
This is a geometric identity on a neighborhood, not a heat assumption. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.bundleOne_trace_relation_near
    (D : HeatNormalFrameData g o c e) (hRic : RicciThree g) :
    (fun x => (heatNormalBundleZero D x).trace) =ᶠ[𝓝 0]
      fun x => 2 * (heatNormalOneZero D x).trace := by
  have hd₁ : ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i k l,
      DifferentiableAt ℝ (fun y => heatNormalFrameConnection g c D.point i y k l) x :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun k => eventually_all.mpr (fun l =>
      ((D.connection_regular i k l).eventually (by norm_num)).mono
        (fun _ h => h.differentiableAt (by norm_num)))))
  have hd₂ : ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i k l,
      DifferentiableAt ℝ (fun y => heatTwoFormConnection g c D.point i y k l) x :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun k => eventually_all.mpr (fun l =>
      ((D.twoForm_connection_regular i k l).eventually (by norm_num)).mono
        (fun _ h => h.differentiableAt (by norm_num)))))
  filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos, hd₁, hd₂] with x hx h₁ h₂
  have hquad : (∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
      (heatTwoFormConnection g c D.point j x * heatTwoFormConnection g c D.point i x).trace) =
      2 * ∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        (heatNormalFrameConnection g c D.point j x * heatNormalFrameConnection g c D.point i x).trace := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [heatTwoFormConnection, heatTwoFormConnection,
      heatTwoFormConnectionMatrix_product_trace _ _ (D.connection_skew x hx j) (D.connection_skew x hx i)]
    ring
  rw [heatNormalBundleZero, heatTwoConnectionZero_trace _ _ _ _ x
    (fun i => heatTwoFormConnectionMatrix_trace _)
    (fun i j => D.twoConnection_partial_trace x i j (fun k => h₂ i k k)),
    heatNormalOneZero, heatOneConnectionZero_trace _ _ _ _ x
    (fun i => heatFour_skew_trace _ (D.connection_skew x hx i))
    (fun i j => D.oneConnection_partial_trace x hx i j (fun k => h₁ i k k))]
  rw [D.potential_as_actual x hx, actual_twoFormPotential_trace hRic, hquad]
  norm_num [Matrix.trace_smul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Gaussian concentration gives the weighted square-integral growth t⁻². -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCutoffColumn_square_integral_bound (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ) (l : Fin 4) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1,
      (∫ x, frameExponentialJacobian g o e x * ‖heatNormalOneCutoffColumn E χ t l x‖ ^ 2) ≤ C / t ^ 2 := by
  obtain ⟨B, hB, hb⟩ := heatNormalOnePolynomialColumn_weight_bound E χ hχ.continuous hc l
  refine ⟨B / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro t ht
  have hpt (x : FourSpace) : frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn E χ t l x‖ ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [heatNormalOneCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      _ = (frameExponentialJacobian g o e x * ‖heatNormalOnePolynomialColumn E χ t l x‖ ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb t ⟨ht.1.le, ht.2⟩ x) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hm : Continuous (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn E χ t l x‖ ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((heatNormalOneCutoffColumn_regular E χ (by exact hχ) t l).continuous.norm.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn E χ t l x‖ ^ 2) :=
    hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hpt x)
  calc
    _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hpt
    _ = _ := by
      rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weak time differentiation of the actual global parametrix, with its
derivative represented by the constructed global L2 time column. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneGlobalColumn_weak_deriv (E : HeatNormalOneExtension D)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (ht : 0 < t) (l : Fin 4)
    (v : smoothCovariantFields M 1) :
    HasDerivAt (fun s => inner ℝ (heatNormalOneGlobalColumn E C hCt hP hD χ hχ hc hs s l)
        (smoothOneFormL2Linear v))
      (inner ℝ (heatNormalOneGlobalTimeColumn E C hCt hP hD χ (hχ.of_le (by norm_num)) hc hs t l)
        (smoothOneFormL2Linear v)) t := by
  let f := fun k x => frameExponentialJacobian g o e x *
    heatNormalOneValue c D.point v x k
  have hV : ContinuousOn (heatNormalOneValue c D.point v)
      C.source := by
    intro x hx
    have hv : ContDiffAt ℝ 2 (heatNormalOneValue c D.point v) x := by
      apply (contDiffAt_piLp (p := 2)).mpr
      intro k
      exact heatNormalOneFormValue_regular 2 c D.point v x
        (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx)) k
    exact hv.continuousAt.continuousWithinAt
  have hf (k : Fin 4) : ContinuousOn (f k) C.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      ((EuclideanSpace.proj k).continuous.comp_continuousOn hV)
  have hχf (k : Fin 4) : Continuous (fun x => χ x * f k x) :=
    heat_continuous_mul_of_tsupport_subset hχ.continuous C.open_source (hf k) hs
  have hd := (HasDerivAt.sum (u := Finset.univ) fun k _ =>
    heatNormalOneCutoffParametrix_pairing_deriv E χ (f k) (hχf k) hc t ht k l).const_mul
      (normalizedChartFactor g).toReal
  have hfun : (fun s => inner ℝ (heatNormalOneGlobalColumn E C hCt hP hD χ hχ hc hs s l)
      (smoothOneFormL2Linear v)) = fun s => (normalizedChartFactor g).toReal *
        ∑ k : Fin 4, ∫ x, heatNormalOneCutoffParametrix E χ s x k l * f k x := by
    funext s
    exact heatNormalOneAmplitudeL2_pairing_sum C hE hCt hP hD (heatNormalOneCutoffColumn E χ s l)
      ((heatNormalOneCutoffColumn_regular E χ hχ s l).of_le (by norm_num))
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneCutoffColumn_support E χ s l))
      ((heatNormalOneCutoffColumn_support E χ s l).trans hs) v
  have hval : inner ℝ (heatNormalOneGlobalTimeColumn E C hCt hP hD χ (hχ.of_le (by norm_num)) hc hs t l)
      (smoothOneFormL2Linear v) = (normalizedChartFactor g).toReal *
        ∑ k : Fin 4, ∫ x, deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t * f k x := by
    have hpair := heatNormalOneAmplitudeL2_pairing_sum C hE hCt hP hD (heatNormalOneTimeColumn E χ t l)
      (heatNormalOneTimeColumn_regular E χ (hχ.of_le (by norm_num)) t l)
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneTimeColumn_support E χ t l))
      ((heatNormalOneTimeColumn_support E χ t l).trans hs) v
    exact hpair.trans (congrArg ((normalizedChartFactor g).toReal * ·)
      (Finset.sum_congr rfl fun k _ => integral_congr_ae (Eventually.of_forall fun x =>
        congrArg (· * f k x) (heatNormalOneTimeColumn_component E χ t ht l k x))))
  simp only [Finset.sum_apply] at hd
  rw [← hfun, ← hval] at hd
  exact hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constructed compact parametrix columns, including their precise
probability-measure normalization, belong to the actual Hodge domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.parametrix_domain_near
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ (C : OpenPartialHomeomorph FourSpace M)
      (_hE : EqOn C (frameExponential g o e) C.source)
      (hCt : C.target ⊆ (chartAt FourSpace c).source)
      (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
      (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ)
      (hs : tsupport χ ⊆ C.source), tsupport χ ⊆ Metric.ball 0 r → ∀ (t : ℝ) (l : Fin 6),
      ∃ hf : heatNormalGlobalParametrixColumn E C hCt hP hD χ
          (hχ.of_le (by norm_num)) hc hs t l ∈ twoFormHodgeDomain hRic,
        twoFormHodgeGenerator hRic ⟨heatNormalGlobalParametrixColumn E C hCt hP hD χ
          (hχ.of_le (by norm_num)) hc hs t l, hf⟩ =
          heatNormalHodgeImage E C hCt hP hD (heatNormalCutoffColumn E χ t l)
            (heatNormalCutoffColumn_regular_four E χ hχ t l)
            (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E χ t l))
            ((heatNormalCutoffColumn_support E χ t l).trans hs) := by
  obtain ⟨r, hr, hdomain⟩ := E.compact_hodge_domain_near he hRic
  refine ⟨r, hr, ?_⟩
  intro C hE hCt hP hD χ hχ hc hs hsmall t l
  exact hdomain C hE hCt hP hD (heatNormalCutoffColumn E χ t l)
    (heatNormalCutoffColumn_regular_four E χ hχ t l)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E χ t l))
    ((heatNormalCutoffColumn_support E χ t l).trans hs)
    ((heatNormalCutoffColumn_support E χ t l).trans hsmall)

theorem heatNormalizedParametrixColumn_domain
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 6)
    (hf : heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs t l ∈ twoFormHodgeDomain hRic) :
    ∃ hn : heatNormalizedParametrixColumn E C hCt hP hD χ hχ hc hs t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨heatNormalizedParametrixColumn E C hCt hP hD χ hχ hc hs t l, hn⟩ =
        ((normalizedChartFactor g).toReal)⁻¹ • twoFormHodgeGenerator hRic
          ⟨heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs t l, hf⟩ := by
  have hn := (twoFormHodgeDomain hRic).smul_mem ((normalizedChartFactor g).toReal)⁻¹ hf
  refine ⟨hn, ?_⟩
  exact (twoFormHodgeGenerator hRic).map_smul ((normalizedChartFactor g).toReal)⁻¹
    ⟨heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs t l, hf⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual Hodge-domain membership for compact amplitudes throughout the
common normal ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.compact_hodge_domain (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 N.frameData.point C.source) (hD : C.source ⊆ Metric.ball 0 N.frameData.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (hsmall : tsupport a ⊆ Metric.ball 0 r) :
    ∃ hf : heatNormalAmplitudeL2 N.frameData C hCt hP hD a (ha.of_le (by norm_num)) hc hs ∈
        twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨heatNormalAmplitudeL2 N.frameData C hCt hP hD a
        (ha.of_le (by norm_num)) hc hs, hf⟩ = heatNormalHodgeImage N.extension C hCt hP hD a ha hc hs := by
  apply twoFormHodgeDomain_of_distribution hRic
  intro v
  have hleft := heatNormalAmplitudeL2_pairing_normal N.frameData C hE hCt hP hD a
    (ha.of_le (by norm_num)) hc hs (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)
  have hright := heatNormalAmplitudeL2_pairing_normal N.frameData C hE hCt hP hD
    (heatNormalOperatorAmplitude N.extension a) (heatNormalOperatorAmplitude_regular N.extension a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOperatorAmplitude_support N.extension a))
    ((heatNormalOperatorAmplitude_support N.extension a).trans hs) (v : SmoothL2TwoForm o)
  exact hleft.trans ((congrArg ((normalizedChartFactor g).toReal * ·)
    (N.compact_green hRic a (ha.of_le (by norm_num)) hc hsmall v)).trans hright.symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The common leading amplitude has a vanishing first Euler source
for the actual scalar, one-form and two-form heat operators. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem fourHeatOneOperator_leading (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (U : FourSpace → ℝ)
    (x : FourSpace) (k l : Fin 4) :
    fourHeatOneOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k =
      (if k = l then 1 else 0) * fourHeatLocalOperator a b 0 U x +
        (∑ i, B i k l * partialDeriv U i x) + U x * C k l := by
  have hf (q : Fin 4) : (fun y => U y * (if q = l then 1 else 0)) =
      (fun y => (if q = l then 1 else 0) * U y) := by funext y; ring
  unfold fourHeatOneOperator fourHeatOneFirst fourHeatOneZero
  simp_rw [hf, fourHeatLocalOperator_const_mul, fourHeat_partial_const_mul]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem heatOneLeadingSource_trace (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (U : FourSpace → ℝ) (x : FourSpace)
    (hB : ∀ i, (B i).trace = 0) :
    (show Mat4 from fun k l => -fourHeatOneOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k).trace =
      -4 * fourHeatLocalOperator a b 0 U x - U x * C.trace := by
  have hm : (show Mat4 from fun k l => -fourHeatOneOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k) =
      -(fourHeatLocalOperator a b 0 U x • (1 : Mat4) +
        (∑ i, partialDeriv U i x • B i) + U x • C) := by
    ext k l
    rw [fourHeatOneOperator_leading]
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sum_apply, smul_eq_mul]
    have hs : (∑ i, B i k l * partialDeriv U i x) =
        ∑ i, partialDeriv U i x * B i k l := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring
  rw [hm]
  simp only [Matrix.trace_neg, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
    hB, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]
  norm_num
  ring

theorem heatTwoLeadingSource_trace (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (U : FourSpace → ℝ) (x : FourSpace)
    (hB : ∀ i, (B i).trace = 0) :
    (show HeatMat6 from fun k l => -fourHeatBundleOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k).trace =
      -6 * fourHeatLocalOperator a b 0 U x - U x * C.trace := by
  have hm : (show HeatMat6 from fun k l => -fourHeatBundleOperator a b B C
      (fun y q => U y * (if q = l then 1 else 0)) x k) =
      -(fourHeatLocalOperator a b 0 U x • (1 : HeatMat6) +
        (∑ i, partialDeriv U i x • B i) + U x • C) := by
    ext k l
    rw [fourHeatBundleOperator_leading]
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.sum_apply, smul_eq_mul]
    have hs : (∑ i, B i k l * partialDeriv U i x) =
        ∑ i, partialDeriv U i x * B i k l := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring
  rw [hm]
  simp only [Matrix.trace_neg, Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul,
    hB, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]
  norm_num
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalBundleExtension.oneCompanion (E : HeatNormalBundleExtension D) :
    HeatNormalOneExtension D :=
  { Classical.choice (exists_heatNormalOneExtension D) with base := E.base }

def HeatNormalOneExtension.firstSource (E : HeatNormalOneExtension D) (x : FourSpace) : Mat4 :=
  fun k l => -fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
    (fun y q => E.base.U y * (if q = l then 1 else 0)) x k

theorem HeatNormalOneExtension.firstSource_regular (E : HeatNormalOneExtension D)
    (k l : Fin 4) : ContDiff ℝ 2 (fun x => E.firstSource x k l) := by
  apply ContDiff.neg
  apply fourHeatOneOperator_contDiff 2 E.base.a E.base.b E.B E.C
  · intro i j
    exact (E.base.a_regular i j).of_le (by norm_num)
  · intro i
    exact (E.base.b_regular i).of_le (by norm_num)
  · intro i a b
    exact (E.B_regular i a b).of_le (by norm_num)
  · intro a b
    exact (E.C_regular a b).of_le (by norm_num)
  · intro q
    exact (E.base.U_regular.of_le (by norm_num)).mul contDiff_const

theorem HeatNormalBundleExtension.B_trace_near (E : HeatNormalBundleExtension D) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i, (E.B x i).trace = 0 := by
  filter_upwards [E.B_near] with x hx
  intro i
  rw [hx]
  simp only [heatNormalBundleFirst, fourHeatConnectionFirst, Matrix.trace_smul,
    Matrix.trace_sum, heatTwoFormConnection, heatTwoFormConnectionMatrix_trace,
    smul_eq_mul, mul_zero, Finset.sum_const_zero]

theorem HeatNormalOneExtension.B_trace_near (E : HeatNormalOneExtension D) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i, (E.B x i).trace = 0 := by
  filter_upwards [E.B_near, Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx hb
  intro i
  rw [hx]
  simp only [heatNormalOneFirst, fourHeatOneConnectionFirst, Matrix.trace_smul, Matrix.trace_sum]
  simp only [heatFour_skew_trace _ (D.connection_skew x hb _), smul_eq_mul,
    mul_zero, Finset.sum_const_zero]

def HeatNormalBundleExtension.eulerFirstSource (E : HeatNormalBundleExtension D) (x : FourSpace) : ℝ :=
  2 * (-fourHeatLocalOperator (E.base.a x) (E.base.b x) 0 E.base.U x) -
    2 * (E.oneCompanion.firstSource x).trace + (E.firstSource x).trace

theorem HeatNormalBundleExtension.eulerFirstSource_zero_near
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) :
    E.eulerFirstSource =ᶠ[𝓝 0] fun _ => 0 := by
  have hC : (fun x => (E.C x).trace) =ᶠ[𝓝 0] fun x => 2 * (E.oneCompanion.C x).trace := by
    filter_upwards [E.C_near, E.oneCompanion.C_near, D.bundleOne_trace_relation_near hRic]
      with x h₂ h₁ h
    rwa [h₂, h₁]
  filter_upwards [E.B_trace_near, E.oneCompanion.B_trace_near, hC] with x h₂ h₁ h
  change 2 * (-fourHeatLocalOperator (E.base.a x) (E.base.b x) 0 E.base.U x) -
    2 * (show Mat4 from fun k l => -fourHeatOneOperator _ _ _ _
      (fun y q => E.base.U y * (if q = l then 1 else 0)) x k).trace +
    (show HeatMat6 from fun k l => -fourHeatBundleOperator _ _ _ _
      (fun y q => E.base.U y * (if q = l then 1 else 0)) x k).trace = 0
  rw [heatOneLeadingSource_trace _ _ _ _ _ x h₁, heatTwoLeadingSource_trace _ _ _ _ _ x h₂, h]
  rw [show E.oneCompanion.base = E.base from rfl]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single genuine normal chart and compact cutoff for the time-dependent
parametrix. Its existence simultaneously enforces the domain and residual bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

structure HeatNormalParametrixData (D : HeatNormalFrameData g o c e) where
  chart : OpenPartialHomeomorph FourSpace M
  exponential : EqOn chart (frameExponential g o e) chart.source
  in_chart : chart.target ⊆ (chartAt FourSpace c).source
  point_regular : ContDiffOn ℝ 2 D.point chart.source
  inside_radius : chart.source ⊆ ball 0 D.radius
  cutoff : FourSpace → ℝ
  cutoff_regular : ContDiff ℝ 4 cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ chart.source
  cutoff_zero : cutoff 0 = 1

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.column (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalGlobalParametrixColumn E P.chart P.in_chart P.point_regular P.inside_radius
    P.cutoff (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact P.cutoff_support t l

def HeatNormalParametrixData.normalizedColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalizedParametrixColumn E P.chart P.in_chart P.point_regular P.inside_radius
    P.cutoff (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact P.cutoff_support t l

def HeatNormalParametrixData.operatorColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalHodgeImage E P.chart P.in_chart P.point_regular P.inside_radius
    (heatNormalCutoffColumn E P.cutoff t l)
    (heatNormalCutoffColumn_regular_four E P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support E P.cutoff t l))
    ((heatNormalCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)

theorem HeatNormalParametrixData.normalized_initial (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (l : Fin 6) (v : SmoothL2TwoForm o) :
    Filter.Tendsto (fun t => inner ℝ (P.normalizedColumn E t l) (smoothTwoFormToL2 v))
      (nhdsWithin 0 (Ioi 0)) (nhds (twoFormFrameValue o (v : smoothTwoForms o).val e l)) :=
  heatNormalizedParametrixColumn_initial E he P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius P.cutoff (P.cutoff_regular.of_le (by norm_num))
    P.cutoff_compact P.cutoff_support P.cutoff_zero l v

theorem exists_heatNormalParametrixData (E : HeatNormalBundleExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) (hepos : e ∈ o.positive) :
    ∃ P : HeatNormalParametrixData D,
      (∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
        twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l) ∧
      ∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x k l,
        |deriv (fun s => heatNormalCutoffParametrix E P.cutoff s x k l) t +
          fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
            (fun y q => heatNormalCutoffParametrix E P.cutoff t y q l) x k| ≤ B * t := by
  obtain ⟨r₀, C, hr₀, hC, hE, _hInv, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  obtain ⟨rd, hrd, hdomain⟩ := E.parametrix_domain_near he hRic
  obtain ⟨rb, hrb, hbound⟩ := heatNormalCutoffParametrix_bound_of_support E hRic hepos
  let R := min r₀ (min rd rb)
  have hR : 0 < R := lt_min hr₀ (lt_min hrd hrb)
  let χ : FourSpace → ℝ := heatNormalChartBump R hR
  have hsR : tsupport χ ⊆ ball 0 R := by
    rw [(heatNormalChartBump R hR).tsupport_eq]
    exact closedBall_subset_ball (by change R / 2 < R; linarith)
  have hR₀ : R ≤ r₀ := min_le_left _ _
  have hRd : R ≤ rd := (min_le_right _ _).trans (min_le_left _ _)
  have hRb : R ≤ rb := (min_le_right _ _).trans (min_le_right _ _)
  have hsC : tsupport χ ⊆ C.source := by
    rw [hC]
    exact hsR.trans (ball_subset_ball hR₀)
  let P : HeatNormalParametrixData D := {
    chart := C
    exponential := hE
    in_chart := hCt
    point_regular := hP.of_le (by norm_num)
    inside_radius := hD
    cutoff := χ
    cutoff_regular := (heatNormalChartBump R hR).contDiff
    cutoff_compact := (heatNormalChartBump R hR).hasCompactSupport
    cutoff_support := hsC
    cutoff_zero := (heatNormalChartBump R hR).one_of_mem_closedBall
      (mem_closedBall_self (by change 0 ≤ R / 4; positivity)) }
  refine ⟨P, ?_, ?_⟩
  · intro t l
    exact hdomain C hE hCt P.point_regular hD χ P.cutoff_regular P.cutoff_compact
      hsC (hsR.trans (ball_subset_ball hRd)) t l
  · apply hbound χ (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact
      (hsR.trans (ball_subset_ball hRb))
    · intro x
      rw [abs_of_nonneg (heatNormalChartBump R hR).nonneg]
      exact (heatNormalChartBump R hR).le_one
    · exact div_pos hR (by norm_num : (0 : ℝ) < 4)
    · intro x hx
      exact (heatNormalChartBump R hR).one_of_mem_closedBall (ball_subset_closedBall hx)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal-frame signed polynomial and its first jet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatSignedGram_contDiff (A B : FourSpace → HeatMat6)
    (hA : ∀ i j, ContDiff ℝ 2 (fun x => A x i j))
    (hB : ∀ i j, ContDiff ℝ 2 (fun x => B x i j)) :
    ContDiff ℝ 2 (fun x => heatSignedGram (A x) (B x)) := by
  simp only [heatSignedGram, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  apply contDiff_const.mul
  apply ContDiff.sum
  intro k _
  exact (hA k j).mul (hB k i)

theorem fourHeat_fderiv_zero_of_partial (f : FourSpace → ℝ)
    (h : ∀ i, partialDeriv f i 0 = 0) : fderiv ℝ f 0 = 0 := by
  ext x
  have hx : (∑ i, x i • coordinateVector i) = x := sum_coordinateVector (WithLp.ofLp x)
  conv_lhs => rw [← hx, map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ i, x i * partialDeriv f i 0) = 0
  simp only [h, mul_zero, Finset.sum_const_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalBundleExtension.signedFirst (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  frameExponentialJacobian g o e x * χ x ^ 2 * E.base.U x *
    (twoFormHodgeMatrix * E.amplitude 1 x).trace

def HeatNormalBundleExtension.signedTail (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) : ℝ :=
  frameExponentialJacobian g o e x * χ x ^ 2 *
    (2 * E.base.U x * (twoFormHodgeMatrix * E.amplitude 2 x).trace +
      heatSignedGram (E.amplitude 1 x) (E.amplitude 1 x) +
      t * (2 * E.base.U x * (twoFormHodgeMatrix * E.amplitude 3 x).trace +
        2 * heatSignedGram (E.amplitude 1 x) (E.amplitude 2 x)) +
      t ^ 2 * (2 * heatSignedGram (E.amplitude 1 x) (E.amplitude 3 x) +
        heatSignedGram (E.amplitude 2 x) (E.amplitude 2 x)) +
      t ^ 3 * (2 * heatSignedGram (E.amplitude 2 x) (E.amplitude 3 x)) +
      t ^ 4 * heatSignedGram (E.amplitude 3 x) (E.amplitude 3 x))

theorem HeatNormalBundleExtension.signed_amplitude_regular (E : HeatNormalBundleExtension D)
    (m : ℕ) (hm : m ≤ 3) :
    ContDiff ℝ 2 (fun x => (twoFormHodgeMatrix * E.amplitude m x).trace) :=
  heatSignedTraceLinear.toContinuousLinearMap.contDiff.comp
    (contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
      (E.amplitude_regular m hm i j).of_le (by norm_num))))

theorem HeatNormalBundleExtension.signedFirst_continuous (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) : Continuous (E.signedFirst χ) :=
  (((frameExponentialJacobian_continuous g o e).mul (hχ.pow 2)).mul
    E.base.U_regular.continuous).mul (E.signed_amplitude_regular 1 (by norm_num)).continuous

theorem HeatNormalBundleExtension.signedFirst_regular (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiffAt ℝ 2 χ 0) : ContDiffAt ℝ 2 (E.signedFirst χ) 0 :=
  ((((frameExponentialJacobian_smoothAt_zero g o e).of_le (by norm_num)).mul
    (hχ.pow 2)).mul (E.base.U_regular.of_le (by norm_num)).contDiffAt).mul
      (E.signed_amplitude_regular 1 (by norm_num)).contDiffAt

theorem HeatNormalBundleExtension.signedFirst_compact (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : HasCompactSupport χ) : HasCompactSupport (E.signedFirst χ) := by
  apply hχ.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hx (by simp [HeatNormalBundleExtension.signedFirst, hz])

theorem HeatNormalBundleExtension.signedFirst_zero (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (he : e.base ∈ (chartAt FourSpace c).source) : E.signedFirst χ 0 = 0 := by
  simp [HeatNormalBundleExtension.signedFirst, E.first_amplitude_signed_trace he]

theorem HeatNormalBundleExtension.signedFirst_fderiv_zero (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiffAt ℝ 2 χ 0)
    (he : e.base ∈ (chartAt FourSpace c).source) : fderiv ℝ (E.signedFirst χ) 0 = 0 := by
  apply fourHeat_fderiv_zero_of_partial
  intro i
  change partialDeriv (fun x =>
    (frameExponentialJacobian g o e x * χ x ^ 2 * E.base.U x) *
      (twoFormHodgeMatrix * E.amplitude 1 x).trace) i 0 = 0
  rw [scalar_partial_product]
  · rw [E.first_amplitude_signed_trace he, E.first_amplitude_signed_partial]
    ring
  · exact ((((frameExponentialJacobian_smoothAt_zero g o e).of_le (by norm_num : (2 : ℕ∞ω) ≤ ∞)).mul
      (hχ.pow 2)).mul
        (E.base.U_regular.of_le (by norm_num)).contDiffAt).differentiableAt (by norm_num)
  · exact (E.signed_amplitude_regular 1 (by norm_num)).differentiable two_ne_zero 0

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed second transport coefficient is the actual signature
curvature polynomial. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatMatrixScalarOperator_signed_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : FourSpace → HeatMat6) (x : FourSpace)
    (hA : ∀ k l, ContDiffAt ℝ 2 (fun y => A y k l) x) :
    (twoFormHodgeMatrix * heatMatrixScalarOperator a b A x).trace =
      fourHeatLocalOperator a b 0 (fun y => (twoFormHodgeMatrix * A y).trace) x := by
  have hm : heatMatrixScalarOperator a b A x =
      -(∑ i, ∑ j, a i j • heatSixPartial (heatSixPartial A i) j x) +
        ∑ i, b i • heatSixPartial A i x := by
    ext k l
    simp only [heatMatrixScalarOperator, fourHeatLocalOperator, Matrix.add_apply,
      Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, heatSixPartial,
      smul_eq_mul, zero_mul, add_zero]
  rw [hm]
  change heatSignedTraceLinear (-(∑ i, ∑ j, a i j • heatSixPartial (heatSixPartial A i) j x) +
    ∑ i, b i • heatSixPartial A i x) = _
  simp only [map_add, map_neg, map_sum, map_smul, smul_eq_mul]
  have hp (i : Fin 4) : heatSignedTraceLinear (heatSixPartial A i x) =
      partialDeriv (fun y => (twoFormHodgeMatrix * A y).trace) i x :=
    (heatSignedTrace_partial A x (fun k l => (hA k l).differentiableAt (by norm_num)) i).symm
  have hpp (i j : Fin 4) : heatSignedTraceLinear (heatSixPartial (heatSixPartial A i) j x) =
      partialDeriv (partialDeriv (fun y => (twoFormHodgeMatrix * A y).trace) i) j x :=
    (heatSignedTrace_second A x hA i j).symm
  simp only [hp, hpp, fourHeatLocalOperator, zero_mul, add_zero]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}

theorem HeatNormalBundleExtension.first_amplitude_signed_scalar
    (E : HeatNormalBundleExtension D) :
    (twoFormHodgeMatrix * heatMatrixScalarOperator (E.base.a 0) (E.base.b 0)
      (E.amplitude 1) 0).trace =
      -(1 / 6 : ℝ) * ∑ i, ∑ j, (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j).trace := by
  rw [heatMatrixScalarOperator_signed_trace _ _ _ 0
    (fun k l => ((E.amplitude_regular 1 (by norm_num) k l).of_le (by norm_num)).contDiffAt)]
  have ha : E.base.a 0 = 1 := by
    rw [E.base.a_near.self_of_nhds]
    change (heatNormalMetric g o ⟨c, f⟩ 0)⁻¹ = 1
    rw [heatNormalMetric_zero]
    simp
  rw [ha]
  unfold fourHeatLocalOperator
  simp only [E.first_amplitude_signed_partial, mul_zero, Finset.sum_const_zero, add_zero,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp_rw [E.first_amplitude_signed_second, ← Finset.mul_sum]
  ring

theorem HeatNormalBundleExtension.second_amplitude_signature_polynomial
    (E : HeatNormalBundleExtension D) :
    (twoFormHodgeMatrix * E.amplitude 2 0).trace =
      (twoFormHodgeMatrix * twoFormPotentialMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) *
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩)).trace / 2 +
      (∑ i, ∑ j, (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j).trace) / 12 := by
  have h := E.second_amplitude_signed_trace (mem_chart_source FourSpace c)
  rw [E.first_amplitude_signed_scalar] at h
  linarith

theorem HeatNormalBundleExtension.second_amplitude_signature_density
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) :
    (twoFormHodgeMatrix * E.amplitude 2 0).trace / (16 * Real.pi ^ 2) =
      curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩) := by
  rw [E.second_amplitude_signature_polynomial]
  exact actual_hodgeSignatureTracePolynomial hRic ⟨c, f⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual radial integral preserves the Euler source cancellation,
so the first alternating heat coefficient vanishes near the center. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.first_amplitude_trace_radial
    (E : HeatNormalOneExtension D) (x : FourSpace) :
    (E.amplitude 1 x).trace =
      fourHeatWeightedRadialAverage 0 E.base.U (fun y => (E.firstSource y).trace) x := by
  change (∑ k : Fin 4, fourHeatWeightedRadialAverage 0 E.base.U
      (fun y => E.firstSource y k k) x) = _
  exact (fourHeatWeightedRadialAverage_sum 0 E.base.U
    (fun k y => E.firstSource y k k) E.base.U_regular.continuous
    (fun k => (E.firstSource_regular k k).continuous) (fun y => (E.base.U_pos y).ne') x).symm

theorem HeatNormalBundleExtension.first_amplitude_trace_radial
    (E : HeatNormalBundleExtension D) (x : FourSpace) :
    (E.amplitude 1 x).trace =
      fourHeatWeightedRadialAverage 0 E.base.U (fun y => (E.firstSource y).trace) x := by
  change (∑ k : Fin 6, fourHeatWeightedRadialAverage 0 E.base.U
      (fun y => E.firstSource y k k) x) = _
  exact (fourHeatWeightedRadialAverage_sum 0 E.base.U
    (fun k y => E.firstSource y k k) E.base.U_regular.continuous
    (fun k => (E.firstSource_regular k k).continuous) (fun y => (E.base.U_pos y).ne') x).symm

def HeatNormalBundleExtension.eulerFirstAmplitude (E : HeatNormalBundleExtension D)
    (x : FourSpace) : ℝ :=
  2 * fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 1 x -
    2 * (E.oneCompanion.amplitude 1 x).trace + (E.amplitude 1 x).trace

theorem HeatNormalBundleExtension.eulerFirstAmplitude_radial
    (E : HeatNormalBundleExtension D) (x : FourSpace) :
    E.eulerFirstAmplitude x = fourHeatWeightedRadialAverage 0 E.base.U E.eulerFirstSource x := by
  let F := fun y => -fourHeatLocalOperator (E.base.a y) (E.base.b y) 0 E.base.U y
  let G := fun y => (E.oneCompanion.firstSource y).trace
  let H := fun y => (E.firstSource y).trace
  have hU := E.base.U_regular.continuous
  have hU0 (y : FourSpace) := (E.base.U_pos y).ne'
  have hF : Continuous F := by
    have hr : ContDiff ℝ 1 F := (fourHeatLocalOperator_contDiff 1 E.base.a E.base.b (fun _ => 0) E.base.U
      (fun i j => (E.base.a_regular i j).of_le (by norm_num))
      (fun i => (E.base.b_regular i).of_le (by norm_num)) contDiff_const
      (E.base.U_regular.of_le (by norm_num))).neg
    exact hr.continuous
  have hG : Continuous G :=
    continuous_finsetSum _ (fun k _ => (E.oneCompanion.firstSource_regular k k).continuous)
  have hH : Continuous H :=
    continuous_finsetSum _ (fun k _ => (E.firstSource_regular k k).continuous)
  rw [eulerFirstAmplitude, E.oneCompanion.first_amplitude_trace_radial, E.first_amplitude_trace_radial]
  change 2 * fourHeatWeightedRadialAverage 0 E.base.U F x -
    2 * fourHeatWeightedRadialAverage 0 E.base.U G x +
      fourHeatWeightedRadialAverage 0 E.base.U H x = _
  have heq : E.eulerFirstSource = (fun y => 2 * F y + (-2) * G y + H y) := by
    funext y
    dsimp only [HeatNormalBundleExtension.eulerFirstSource, F, G, H]
    ring
  rw [heq]
  rw [fourHeatWeightedRadialAverage_add 0 E.base.U (fun y => 2 * F y + (-2) * G y) H hU
    ((continuous_const.mul hF).add (continuous_const.mul hG)) hH hU0 x,
    fourHeatWeightedRadialAverage_add 0 E.base.U (fun y => 2 * F y) (fun y => (-2) * G y) hU
      (continuous_const.mul hF) (continuous_const.mul hG) hU0 x,
    fourHeatWeightedRadialAverage_const_mul, fourHeatWeightedRadialAverage_const_mul]
  ring

theorem HeatNormalBundleExtension.eulerFirstAmplitude_zero_near
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) :
    E.eulerFirstAmplitude =ᶠ[𝓝 0] fun _ => 0 := by
  have h := fourHeatWeightedRadialAverage_zero_germ 0 E.base.U E.eulerFirstSource
    (E.eulerFirstSource_zero_near hRic)
  filter_upwards [h] with x hx
  rw [E.eulerFirstAmplitude_radial]
  exact hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first signed coefficient is a joint C2 family, with a uniform
quadratic zero at every actual normal center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilySignedFirst (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (z : HeatRadialFrameSpace) : ℝ :=
  χ z.1 ^ 2 / E.U z * (twoFormHodgeMatrix * E.amplitude 1 z).trace

theorem heatFamilySignedFirst_regular (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) : ContDiff ℝ 2 (heatFamilySignedFirst E χ) := by
  have hA : ContDiff ℝ 2 (fun z => (twoFormHodgeMatrix * E.amplitude 1 z).trace) :=
    heatSignedTraceLinear.toContinuousLinearMap.contDiff.comp
      (contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
        (E.amplitude_regular 1 (by omega) i j).of_le (by norm_num))))
  exact (((hχ.comp contDiff_fst).pow 2).div (E.U_regular.of_le (by norm_num))
    (fun z => (E.U_pos z).ne')).mul hA

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.signedFirst_family (N : HeatCommonNormalMember g o c E r e)
    (χ : FourSpace → ℝ) (hχs : tsupport χ ⊆ ball 0 r) (x : FourSpace) :
    N.extension.signedFirst χ x = heatFamilySignedFirst E χ (x, frameCoordinateState g c e) := by
  by_cases hx : x ∈ tsupport χ
  · have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.metric_pos x (hχs hx)))
    rw [← (N.actual x (hχs hx)).2.2.2.2, N.U_family] at hh
    unfold HeatNormalBundleExtension.signedFirst heatFamilySignedFirst
    rw [eq_inv_of_mul_eq_one_right hh, N.U_family, N.amplitude_family 1 (by omega)]
    dsimp only
    field_simp
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [HeatNormalBundleExtension.signedFirst, heatFamilySignedFirst,
      hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_div]

theorem heatUniformSignedFirst_quadratic (E : HeatFamilySmoothCoefficients) (r : ℝ) (hr : 0 < r)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hχs : tsupport χ ⊆ ball 0 r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonNormalMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ x, ‖N.extension.signedFirst χ x‖ ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := heatFamily_quadratic_bound (heatFamilySignedFirst E χ)
    (heatFamilySignedFirst_regular E χ hχ) r K hK
  refine ⟨C, hC, ?_⟩
  intro e N hq x
  have hec : e.base ∈ (chartAt FourSpace c).source := by
    simpa only [frameExponential_zero] using N.exponential_source 0 (mem_ball_self hr)
  have hfun : (fun y => heatFamilySignedFirst E χ (y, frameCoordinateState g c e)) =
      N.extension.signedFirst χ := by
    funext y
    exact (N.signedFirst_family χ hχs y).symm
  by_cases hx : x ∈ closedBall (0 : FourSpace) r
  · rw [← hfun]
    apply hb _ hq _ _ x hx
    · exact (congrFun hfun 0).trans (N.extension.signedFirst_zero χ hec)
    · rw [hfun]
      exact N.extension.signedFirst_fderiv_zero χ hχ.contDiffAt hec
  · have hxs : x ∉ tsupport χ := fun hs => hx (ball_subset_closedBall (hχs hs))
    have hz := image_eq_zero_of_notMem_tsupport hxs
    simp only [HeatNormalBundleExtension.signedFirst, hz, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, norm_zero]
    positivity

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform normal-frame amplitude bound gives an actual global L2
bound. The moving-frame tensor norm is computed using its orthogonality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalAmplitudeTensor_norm_sq
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (f : FrameBundle g) (hf : f.base ∈ C.target) :
    ‖heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs f‖ ^ 2 =
      2 * ‖a (C.symm f.base)‖ ^ 2 := by
  let x := C.symm f.base
  have hx : x ∈ C.source := C.map_target hf
  have hxb := hD hx
  have hbase : (D.point x).1 = chartAt FourSpace c f.base := by
    rw [D.exponential x hxb, ← hE hx, C.right_inv hf]
  have hF := frameChartMatrix_normalizes g c f (hCt hf)
  rw [← hbase] at hF
  have hi : (D.point x).2⁻¹ * (D.point x).2 = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (heatNormalFrame_matrix_nondegenerate D hxb))
  have hback : frameTensor (D.point x).2 (heatNormalCoordinateTensor D a x) = twoFormTensor (a x) := by
    unfold heatNormalCoordinateTensor
    rw [← frameTensor_mul, hi, frameTensor_one]
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f)
    : TwoTensorEuclidean) (WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f)) = _
  rw [heat_euclideanTensor_inner, heatNormalFrameTensorLift, ite_eq_left hf]
  change frameTensorPairing
    (frameTensor (frameChartMatrix g c f) (frameTensor (D.point x).2⁻¹ (twoFormTensor (a x))))
    (frameTensor (frameChartMatrix g c f) (heatNormalCoordinateTensor D a x)) = _
  rw [heat_normal_frame_pairing _ _ _ (D.orthonormal x hxb) hF, hback,
    twoFormTensor_pairing, real_inner_self_eq_norm_sq]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

theorem heatNormalAmplitudeL2_norm_le
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, ‖a x‖ ≤ B) :
    ‖heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs‖ ≤ 2 * B := by
  apply (twoFormFromContinuousTensor_norm_le _).trans
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro f
  by_cases hf : f.base ∈ C.target
  · have heq := heatNormalAmplitudeTensor_norm_sq C hE hCt hP hD a ha hc hs f hf
    have hba := hb (C.symm f.base)
    nlinarith [norm_nonneg (a (C.symm f.base)),
      norm_nonneg (heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs f)]
  · have hz : heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs f = 0 := by
      change WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f) = _
      simp only [heatNormalFrameTensorLift, ite_eq_right hf]
      rfl
    rw [hz, norm_zero]
    positivity

end
end PositiveEinsteinFour.Geometry
end


section

/-! One genuine chart and cutoff for the actual one-form weak heat equation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.oneColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatNormalOneGlobalColumn E P.chart P.in_chart P.point_regular P.inside_radius
    P.cutoff P.cutoff_regular P.cutoff_compact P.cutoff_support t l

def HeatNormalParametrixData.oneTimeColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatNormalOneGlobalTimeColumn E P.chart P.in_chart P.point_regular P.inside_radius
    P.cutoff (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact P.cutoff_support t l

def HeatNormalParametrixData.oneOperatorColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatNormalOneHodgeImage E P.chart P.in_chart P.point_regular P.inside_radius
    (heatNormalOneCutoffColumn E P.cutoff t l)
    (heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support E P.cutoff t l))
    ((heatNormalOneCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)

def HeatNormalParametrixData.oneResidual (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  P.oneTimeColumn E t l + P.oneOperatorColumn E t l

theorem exists_heatNormalOneWeakData (E : HeatNormalOneExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) :
    ∃ P : HeatNormalParametrixData D, ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v) := by
  obtain ⟨r₀, C, hr₀, hC, hE, _hInv, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  obtain ⟨rd, hrd, hpair⟩ := E.compact_operator_pairing_near he hRic
  let R := min r₀ rd
  have hR : 0 < R := lt_min hr₀ hrd
  let χ : FourSpace → ℝ := heatNormalChartBump R hR
  have hsR : tsupport χ ⊆ ball 0 R := by
    rw [(heatNormalChartBump R hR).tsupport_eq]
    exact closedBall_subset_ball (by change R / 2 < R; linarith)
  have hsC : tsupport χ ⊆ C.source := by
    rw [hC]
    exact hsR.trans (ball_subset_ball (min_le_left _ _))
  let P : HeatNormalParametrixData D := {
    chart := C
    exponential := hE
    in_chart := hCt
    point_regular := hP.of_le (by norm_num)
    inside_radius := hD
    cutoff := χ
    cutoff_regular := (heatNormalChartBump R hR).contDiff
    cutoff_compact := (heatNormalChartBump R hR).hasCompactSupport
    cutoff_support := hsC
    cutoff_zero := (heatNormalChartBump R hR).one_of_mem_closedBall
      (mem_closedBall_self (by change 0 ≤ R / 4; positivity)) }
  refine ⟨P, ?_⟩
  intro t l v
  exact hpair C hE hCt P.point_regular hD (heatNormalOneCutoffColumn E χ t l)
    (heatNormalOneCutoffColumn_regular E χ P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support E χ t l))
    ((heatNormalOneCutoffColumn_support E χ t l).trans hsC)
    ((heatNormalOneCutoffColumn_support E χ t l).trans
      (hsR.trans (ball_subset_ball (min_le_right _ _)))) v

theorem HeatNormalParametrixData.oneWeakEvolution
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (t : ℝ) (ht : 0 < t) (l : Fin 4) (v : smoothCovariantFields M 1) :
    HasDerivAt (fun s => inner ℝ (P.oneColumn E s l) (smoothOneFormL2Linear v))
      (inner ℝ (P.oneResidual E t l) (smoothOneFormL2Linear v) -
        inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v))) t := by
  have hd := heatNormalOneGlobalColumn_weak_deriv E P.chart P.exponential
    P.in_chart P.point_regular P.inside_radius P.cutoff P.cutoff_regular
    P.cutoff_compact P.cutoff_support t ht l v
  have hr : inner ℝ (P.oneResidual E t l) (smoothOneFormL2Linear v) -
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
      inner ℝ (P.oneTimeColumn E t l) (smoothOneFormL2Linear v) := by
    rw [HeatNormalParametrixData.oneResidual, inner_add_left, hpair]
    ring
  rw [hr]
  exact hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuity and a compact uniform bound for the higher signed terms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.signedTail_continuous (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : ℝ × FourSpace => E.signedTail χ z.1 z.2) := by
  have hJ := (frameExponentialJacobian_continuous g o e).comp
    (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hU := E.base.U_regular.continuous.comp
    (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hS (m : ℕ) (hm : m ≤ 3) := (E.signed_amplitude_regular m hm).continuous.comp
    (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hG (m n : ℕ) (hm : m ≤ 3) (hn : n ≤ 3) :=
    (heatSignedGram_contDiff (E.amplitude m) (E.amplitude n)
      (fun i j => (E.amplitude_regular m hm i j).of_le (by norm_num))
      (fun i j => (E.amplitude_regular n hn i j).of_le (by norm_num))).continuous.comp
      (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have h2 := hS 2 (by norm_num)
  have h3 := hS 3 (by norm_num)
  have h11 := hG 1 1 (by norm_num) (by norm_num)
  have h12 := hG 1 2 (by norm_num) (by norm_num)
  have h13 := hG 1 3 (by norm_num) (by norm_num)
  have h22 := hG 2 2 (by norm_num) (by norm_num)
  have h23 := hG 2 3 (by norm_num) (by norm_num)
  have h33 := hG 3 3 (by norm_num) (by norm_num)
  have htwo : Continuous (fun _ : ℝ × FourSpace => (2 : ℝ)) := continuous_const
  have h0 := ((htwo.mul hU).mul h2).add h11
  have h1 := ((htwo.mul hU).mul h3).add (htwo.mul h12)
  have ht2 := (htwo.mul h13).add h22
  unfold HeatNormalBundleExtension.signedTail
  exact (hJ.mul ((hχ.comp continuous_snd).pow 2)).mul
    ((((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul ht2)).add
      ((continuous_fst.pow 3).mul (htwo.mul h23))).add
        ((continuous_fst.pow 4).mul h33))

theorem HeatNormalBundleExtension.signedTail_bound (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖E.signedTail χ t x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hc).exists_bound_of_continuousOn
    (E.signedTail_continuous χ hχ).continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport χ
  · exact (hB (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [HeatNormalBundleExtension.signedTail, hz, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, norm_zero]
    exact le_max_right _ _

theorem HeatNormalBundleExtension.signedTail_zero (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : χ 0 = 1) :
    E.signedTail χ 0 0 = 2 * (twoFormHodgeMatrix * E.amplitude 2 0).trace +
      heatSignedGram (E.amplitude 1 0) (E.amplitude 1 0) := by
  have hU : E.base.U 0 = 1 := E.base.U_near.self_of_nhds.trans
    (heatNormalLeadingAmplitude_zero g o e)
  simp [HeatNormalBundleExtension.signedTail, frameExponentialJacobian_zero, hχ, hU]

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual normal chart and compact scalar cutoff. All functions have
the four derivatives required by the finite Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

structure HeatScalarChartData (D : HeatNormalFrameData g o c e) where
  extension : HeatNormalExtension 10 g o e
  chart : OpenPartialHomeomorph FourSpace M
  exponential : EqOn chart (frameExponential g o e) chart.source
  in_chart : chart.target ⊆ (chartAt FourSpace c).source
  point_regular : ContDiffOn ℝ 4 D.point chart.source
  inverse_regular : ContMDiffOn I4 I4 4 chart.symm chart.target
  inside_radius : chart.source ⊆ ball 0 D.radius
  cutoff : FourSpace → ℝ
  cutoff_regular : ContDiff ℝ 4 cutoff
  cutoff_compact : HasCompactSupport cutoff
  cutoff_support : tsupport cutoff ⊆ chart.source
  cutoff_zero : cutoff 0 = 1

theorem exists_heatScalarChartData (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) : Nonempty (HeatScalarChartData D) := by
  obtain ⟨E⟩ := exists_heatNormalExtension 10 g o e
  obtain ⟨r, C, hr, hC, hE, hI, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  let χ := heatNormalChartBump r hr
  have hs : tsupport χ ⊆ C.source := by
    rw [hC, χ.tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  exact ⟨{
    extension := E
    chart := C
    exponential := hE
    in_chart := hCt
    point_regular := hP
    inverse_regular := hI
    inside_radius := hD
    cutoff := χ
    cutoff_regular := χ.contDiff
    cutoff_compact := χ.hasCompactSupport
    cutoff_support := hs
    cutoff_zero := χ.one_of_mem_closedBall
      (mem_closedBall_self (by change 0 ≤ r / 4; positivity)) }⟩

variable {D : HeatNormalFrameData g o c e}

def HeatScalarChartData.function (P : HeatScalarChartData D) (t : ℝ) : M → ℝ :=
  heatNormalScalarLift P.chart (P.extension.scalarCutoff P.cutoff t)

theorem HeatScalarChartData.function_regular (P : HeatScalarChartData D) (t : ℝ) :
    ContMDiff I4 𝓘(ℝ, ℝ) 4 (P.function t) :=
  heatNormalScalarLift_regular P.chart _ P.inverse_regular
    (P.extension.scalarCutoff_regular P.cutoff P.cutoff_regular t)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (P.extension.scalarCutoff_support P.cutoff t))
    ((P.extension.scalarCutoff_support P.cutoff t).trans P.cutoff_support)

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def HeatScalarChartData.column (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) :=
  scalarFiniteValueL2 g (P.function t) (P.function_regular t)

def HeatScalarChartData.laplacianColumn (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) :=
  scalarFiniteLaplacianL2 g (P.function t) (P.function_regular t)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The common normal ball and fixed bump define actual compact
parametrix data, with the actual Hodge generator identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

def HeatCommonNormalMember.parametrixData (N : HeatCommonNormalMember g o c E r e)
    (hr : 0 < r) : HeatNormalParametrixData N.frameData := by
  let C := N.chart.restrOpen (ball 0 r) isOpen_ball
  have hs : C.source = ball 0 r := inter_eq_right.mpr N.ball_source
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ C.source := by
    rw [hs, (heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  exact {
    chart := C
    exponential := fun x hx => N.exponential hx.1
    in_chart := fun y hy => N.target_chart hy.1
    point_regular := fun x hx => (N.point_regular x (hs ▸ hx)).contDiffWithinAt
    inside_radius := fun x hx => ball_subset_ball N.radius_le (hs ▸ hx)
    cutoff := χ
    cutoff_regular := (heatNormalChartBump r hr).contDiff
    cutoff_compact := (heatNormalChartBump r hr).hasCompactSupport
    cutoff_support := hχs
    cutoff_zero := (heatNormalChartBump r hr).one_of_mem_closedBall
      (mem_closedBall_self (by change 0 ≤ r / 4; positivity)) }

theorem HeatCommonNormalMember.parametrixData_cutoff (N : HeatCommonNormalMember g o c E r e)
    (hr : 0 < r) : (N.parametrixData hr).cutoff = heatNormalChartBump r hr := rfl

theorem HeatCommonNormalMember.parametrixData_source (N : HeatCommonNormalMember g o c E r e)
    (hr : 0 < r) : (N.parametrixData hr).chart.source = ball 0 r :=
  inter_eq_right.mpr N.ball_source

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatCommonNormalMember.parametrixData_generator (N : HeatCommonNormalMember g o c E r e)
    (hr : 0 < r) (hRic : RicciThree g) (t : ℝ) (l : Fin 6) :
    ∃ hf : (N.parametrixData hr).column N.extension t l ∈ twoFormHodgeDomain hRic,
      twoFormHodgeGenerator hRic ⟨(N.parametrixData hr).column N.extension t l, hf⟩ =
        (N.parametrixData hr).operatorColumn N.extension t l := by
  let P := N.parametrixData hr
  apply N.compact_hodge_domain hRic P.chart P.exponential P.in_chart P.point_regular P.inside_radius
    (heatNormalCutoffColumn N.extension P.cutoff t l)
    (heatNormalCutoffColumn_regular_four N.extension P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support N.extension P.cutoff t l))
    ((heatNormalCutoffColumn_support N.extension P.cutoff t l).trans P.cutoff_support)
  rw [← N.parametrixData_source hr]
  exact (heatNormalCutoffColumn_support N.extension P.cutoff t l).trans P.cutoff_support

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local transport amplitudes are independent of the chosen extensions.
This permits the common smooth family to supply the one-form companion. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology
noncomputable section

theorem fourHeatWeightedRadialAverage_congr_germ (m : ℕ) (U F G : FourSpace → ℝ)
    (h : F =ᶠ[𝓝 0] G) :
    fourHeatWeightedRadialAverage m U F =ᶠ[𝓝 0] fourHeatWeightedRadialAverage m U G := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp h
  filter_upwards [ball_mem_nhds (0 : FourSpace) hr] with x hx
  unfold fourHeatWeightedRadialAverage fourHeatRadialAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
  have hn : ‖s • x‖ ≤ ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs'.1]
    exact mul_le_of_le_one_left (norm_nonneg x) hs'.2
  have hm : s • x ∈ ball (0 : FourSpace) r := by
    rw [mem_ball, dist_zero_right]
    exact hn.trans_lt (by simpa only [mem_ball, dist_zero_right] using hx)
  change s ^ m * (F (s • x) / U (s • x)) = s ^ m * (G (s • x) / U (s • x))
  rw [hball hm]

theorem fourHeatOneCoefficient_congr_germ (m : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ) (U : FourSpace → ℝ)
    (B B' : FourSpace → Fin 4 → Mat4) (C C' : FourSpace → Mat4)
    (hB : B =ᶠ[𝓝 0] B') (hC : C =ᶠ[𝓝 0] C') :
    fourHeatOneCoefficient a b B C U m =ᶠ[𝓝 0] fourHeatOneCoefficient a b B' C' U m := by
  induction m with
  | zero => exact Eventually.of_forall fun _ => rfl
  | succ m ih =>
    have hs (k l : Fin 4) :
        (fun x => -fourHeatOneOperator (a x) (b x) (B x) (C x)
          (fun y q => fourHeatOneCoefficient a b B C U m y q l) x k) =ᶠ[𝓝 0]
        (fun x => -fourHeatOneOperator (a x) (b x) (B' x) (C' x)
          (fun y q => fourHeatOneCoefficient a b B' C' U m y q l) x k) := by
      filter_upwards [hB, hC, ih.eventuallyEq_nhds] with x hBx hCx hx
      rw [hBx, hCx]
      congr 1
      exact fourHeatOneOperator_germ _ _ _ _ (fun q =>
        hx.mono fun y hy => congrArg (fun A : Mat4 => A q l) hy) k
    have h := eventually_all.mpr (fun k => eventually_all.mpr (fun l =>
      fourHeatWeightedRadialAverage_congr_germ m U _ _ (hs k l)))
    filter_upwards [h] with x hx
    funext k l
    exact hx k l

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.amplitude_companion_germ (A : HeatNormalOneExtension D)
    (E : HeatNormalBundleExtension D) (hbase : A.base = E.base) (m : ℕ) :
    A.amplitude m =ᶠ[𝓝 0] E.oneCompanion.amplitude m := by
  have h := fourHeatOneCoefficient_congr_germ m E.base.a E.base.b E.base.U
    A.B E.oneCompanion.B A.C E.oneCompanion.C
    (A.B_near.trans E.oneCompanion.B_near.symm) (A.C_near.trans E.oneCompanion.C_near.symm)
  change fourHeatOneCoefficient A.base.a A.base.b A.B A.C A.base.U m =ᶠ[𝓝 0]
    fourHeatOneCoefficient E.base.a E.base.b E.oneCompanion.B E.oneCompanion.C E.base.U m
  simpa only [hbase] using h

theorem HeatNormalOneExtension.eulerFirst_zero_near (A : HeatNormalOneExtension D)
    (E : HeatNormalBundleExtension D) (hbase : A.base = E.base) (hRic : RicciThree g) :
    (fun x => 2 * fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 1 x -
      2 * (A.amplitude 1 x).trace + (E.amplitude 1 x).trace) =ᶠ[𝓝 0] fun _ => 0 := by
  filter_upwards [A.amplitude_companion_germ E hbase 1, E.eulerFirstAmplitude_zero_near hRic]
    with x hx he
  simpa only [hx, HeatNormalBundleExtension.eulerFirstAmplitude] using he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar differentiation commutes with the finite fiber traces in the
Euler combination of the first transport amplitudes. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem fourHeatLocalOperator_zero (a : Mat4) (b : Fin 4 → ℝ) (c : ℝ) (x : FourSpace) :
    fourHeatLocalOperator a b c (fun _ => 0) x = 0 := by
  simpa only [zero_mul] using fourHeatLocalOperator_const_mul a b c 0 (fun _ => 0) x

theorem fourHeatLocalOperator_finite_sum {ι : Type*} [Fintype ι]
    (a : Mat4) (b : Fin 4 → ℝ) (c : ℝ) (F : ι → FourSpace → ℝ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (x : FourSpace) :
    fourHeatLocalOperator a b c (fun y => ∑ i, F i y) x =
      ∑ i, fourHeatLocalOperator a b c (F i) x := by
  classical
  have hsum (s : Finset ι) :
      fourHeatLocalOperator a b c (fun y => ∑ i ∈ s, F i y) x =
        ∑ i ∈ s, fourHeatLocalOperator a b c (F i) x := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using fourHeatLocalOperator_zero a b c x
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [fourHeatLocalOperator_add a b c (F i) (fun y => ∑ j ∈ s, F j y)
        (hF i) (ContDiff.sum (fun j _ => hF j)) x, ih]
  exact hsum Finset.univ

def heatOneMatrixScalarOperator (a : Mat4) (b : Fin 4 → ℝ)
    (A : FourSpace → Mat4) (x : FourSpace) : Mat4 :=
  fun k l => fourHeatLocalOperator a b 0 (fun y => A y k l) x

theorem heatOneMatrixScalarOperator_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : FourSpace → Mat4) (hA : ∀ k, ContDiff ℝ 2 (fun y => A y k k)) (x : FourSpace) :
    (heatOneMatrixScalarOperator a b A x).trace =
      fourHeatLocalOperator a b 0 (fun y => (A y).trace) x :=
  (fourHeatLocalOperator_finite_sum a b 0 (fun k y => A y k k) hA x).symm

theorem heatMatrixScalarOperator_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : FourSpace → HeatMat6) (hA : ∀ k, ContDiff ℝ 2 (fun y => A y k k)) (x : FourSpace) :
    (heatMatrixScalarOperator a b A x).trace =
      fourHeatLocalOperator a b 0 (fun y => (A y).trace) x :=
  (fourHeatLocalOperator_finite_sum a b 0 (fun k y => A y k k) hA x).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.eulerFirst_scalar_operator_zero
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) :
    2 * fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0
        (fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 1) 0 -
      2 * (heatOneMatrixScalarOperator (E.base.a 0) (E.base.b 0) (E.oneCompanion.amplitude 1) 0).trace +
      (heatMatrixScalarOperator (E.base.a 0) (E.base.b 0) (E.amplitude 1) 0).trace = 0 := by
  let F := fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 1
  let G := fun y => (E.oneCompanion.amplitude 1 y).trace
  let H := fun y => (E.amplitude 1 y).trace
  have hF : ContDiff ℝ 2 F := fourHeatCoefficient_contDiff 1 2 _ _ _ _
    (fun i j => (E.base.a_regular i j).of_le (by norm_num))
    (fun i => (E.base.b_regular i).of_le (by norm_num)) contDiff_const
    (E.base.U_regular.of_le (by norm_num)) (fun y => (E.base.U_pos y).ne')
  have hG : ContDiff ℝ 2 G := ContDiff.sum (fun k _ =>
    (E.oneCompanion.amplitude_regular 1 (by norm_num) k k).of_le (by norm_num))
  have hH : ContDiff ℝ 2 H := ContDiff.sum (fun k _ =>
    (E.amplitude_regular 1 (by norm_num) k k).of_le (by norm_num))
  have hz := fourHeatLocalOperator_germ (E.base.a 0) (E.base.b 0) 0
    (E.eulerFirstAmplitude_zero_near hRic)
  have heq : E.eulerFirstAmplitude = (fun y => 2 * F y + (-2) * G y + H y) := by
    funext y
    change 2 * F y - 2 * G y + H y = _
    ring
  rw [heq, fourHeatLocalOperator_add _ _ _ _ _ ((contDiff_const.mul hF).add (contDiff_const.mul hG)) hH,
    fourHeatLocalOperator_add _ _ _ _ _ (contDiff_const.mul hF) (contDiff_const.mul hG),
    fourHeatLocalOperator_const_mul, fourHeatLocalOperator_const_mul] at hz
  have hz0 : fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 (fun _ => 0) 0 = 0 := by
    exact fourHeatLocalOperator_zero _ _ _ _
  rw [hz0] at hz
  rw [heatOneMatrixScalarOperator_trace _ _ _
    (fun k => (E.oneCompanion.amplitude_regular 1 (by norm_num) k k).of_le (by norm_num)),
    heatMatrixScalarOperator_trace _ _ _
    (fun k => (E.amplitude_regular 1 (by norm_num) k k).of_le (by norm_num))]
  change 2 * fourHeatLocalOperator _ _ _ F 0 - 2 * fourHeatLocalOperator _ _ _ G 0 +
    fourHeatLocalOperator _ _ _ H 0 = 0
  linarith only [hz]

end
end PositiveEinsteinFour.Geometry
end


section

/-! All remaining signed polynomial coefficients have one compact bound
across the actual normal family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilySignedTail (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) : ℝ :=
  (E.U z ^ 2)⁻¹ * χ z.1 ^ 2 *
    (2 * E.U z * (twoFormHodgeMatrix * E.amplitude 2 z).trace +
      heatSignedGram (E.amplitude 1 z) (E.amplitude 1 z) +
      t * (2 * E.U z * (twoFormHodgeMatrix * E.amplitude 3 z).trace +
        2 * heatSignedGram (E.amplitude 1 z) (E.amplitude 2 z)) +
      t ^ 2 * (2 * heatSignedGram (E.amplitude 1 z) (E.amplitude 3 z) +
        heatSignedGram (E.amplitude 2 z) (E.amplitude 2 z)) +
      t ^ 3 * (2 * heatSignedGram (E.amplitude 2 z) (E.amplitude 3 z)) +
      t ^ 4 * heatSignedGram (E.amplitude 3 z) (E.amplitude 3 z))

theorem heatFamilySignedTail_continuous (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilySignedTail E χ z.1 z.2) := by
  have hU := E.U_regular.continuous.comp
    (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have hS (m : ℕ) (hm : m ≤ 3) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      (twoFormHodgeMatrix * E.amplitude m z.2).trace) := by
    have h := heatSignedTraceLinear.toContinuousLinearMap.continuous.comp
      (continuous_pi (fun i => continuous_pi (fun j => (E.amplitude_regular m hm i j).continuous)))
    exact h.comp continuous_snd
  have hG (m n : ℕ) (hm : m ≤ 3) (hn : n ≤ 3) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      heatSignedGram (E.amplitude m z.2) (E.amplitude n z.2)) := by
    simp only [heatSignedGram, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply continuous_const.mul
    apply continuous_finsetSum
    intro k _
    exact ((E.amplitude_regular m hm k j).continuous.comp continuous_snd).mul
      ((E.amplitude_regular n hn k i).continuous.comp continuous_snd)
  have hJ := (hU.pow 2).inv₀ (fun z => pow_ne_zero 2 (E.U_pos z.2).ne')
  have htwo : Continuous (fun _ : ℝ × HeatRadialFrameSpace => (2 : ℝ)) := continuous_const
  have h0 := ((htwo.mul hU).mul (hS 2 (by omega))).add (hG 1 1 (by omega) (by omega))
  have h1 := ((htwo.mul hU).mul (hS 3 (by omega))).add (htwo.mul (hG 1 2 (by omega) (by omega)))
  have h2 := (htwo.mul (hG 1 3 (by omega) (by omega))).add (hG 2 2 (by omega) (by omega))
  exact (hJ.mul ((hχ.comp (continuous_fst.comp continuous_snd)).pow 2)).mul
    ((((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul h2)).add
      ((continuous_fst.pow 3).mul (htwo.mul (hG 2 3 (by omega) (by omega))))).add
        ((continuous_fst.pow 4).mul (hG 3 3 (by omega) (by omega))))

theorem heatFamilySignedTail_bound (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      ‖heatFamilySignedTail E χ t (x, q)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image
    (heatFamilySignedTail_continuous E χ hχ).norm.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro q hq t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hB ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
  · simp only [heatFamilySignedTail, image_eq_zero_of_notMem_tsupport hx,
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, norm_zero]
    exact le_max_right _ _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.signedTail_family (N : HeatCommonNormalMember g o c E r e)
    (χ : FourSpace → ℝ) (hχs : tsupport χ ⊆ ball 0 r) (t : ℝ) (x : FourSpace) :
    N.extension.signedTail χ t x = heatFamilySignedTail E χ t (x, frameCoordinateState g c e) := by
  by_cases hx : x ∈ tsupport χ
  · have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.metric_pos x (hχs hx)))
    rw [← (N.actual x (hχs hx)).2.2.2.2, N.U_family] at hh
    unfold HeatNormalBundleExtension.signedTail heatFamilySignedTail
    rw [eq_inv_of_mul_eq_one_right hh, N.U_family, N.amplitude_family 1 (by omega),
      N.amplitude_family 2 (by omega), N.amplitude_family 3 (by omega)]
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [HeatNormalBundleExtension.signedTail, heatFamilySignedTail,
      hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact norm integral for the actual compact normal amplitude, obtained
by smooth approximation inside the genuine two-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance heatNormalExactCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance heatNormalExactProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem heatNormalAmplitudeTensor_L2_realization
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) :
    twoFormTensorL2 (heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ
        (heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs) := by
  apply heatNormalTensor_L2_realization C hCt (heatNormalCoordinateTensor D a)
    (heatNormalCoordinateTensor_continuousOn D C hP hD a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCoordinateTensor_support D a))
    ((heatNormalCoordinateTensor_support D a).trans hs)
  intro z i j
  apply twoTensor_frame_skew
  intro k l
  exact congrArg (fun A : Mat4 => A k l) (twoFormMatrix_skew (a z))

theorem heatNormalAmplitudeL2_norm_sq_integral
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) :
    ‖heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs‖ ^ 2 =
      (normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ‖a x‖ ^ 2 := by
  let F := heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs
  let ψ := fun x => ‖a x‖ ^ 2
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have hz : a x = 0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    change ‖a x‖ ^ 2 = 0
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := (ha.continuous.norm.pow 2).continuousOn
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hs)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (f : FrameBundle g) : ‖F f‖ ^ 2 = 2 * heatNormalScalarLift C ψ f.base := by
    by_cases hf : f.base ∈ C.target
    · rw [heatNormalAmplitudeTensor_norm_sq C hE hCt hP hD a ha hc hs f hf,
        heatNormalScalarLift_on_target C ψ hf]
    · have hz : F f = 0 := by
        change WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f) = _
        simp only [heatNormalFrameTensorLift, ite_eq_right hf]
        rfl
      rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      simp only [heatNormalScalarLift, ite_eq_right hf, mul_zero]
  have hex : twoFormTensorL2 (heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs) =
      ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F :=
    heatNormalAmplitudeTensor_L2_realization C hCt hP hD a ha hc hs
  have hcalc : 2 * ‖heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs‖ ^ 2 =
      2 * ((normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ‖a x‖ ^ 2) := by
    calc
      _ = ‖ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F‖ ^ 2 := by
        rw [← hex, twoFormTensorL2_norm_sq]
      _ = ∫ f, ‖F f‖ ^ 2 ∂canonicalFrameMeasure g o := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F] with f hf
        rw [hf, real_inner_self_eq_norm_sq]
      _ = 2 * ∫ y, heatNormalScalarLift C ψ y ∂normalizedVolume g := by
        simp_rw [heq]
        rw [integral_const_mul, canonicalFrameMeasure_integral_base g o _ hLi]
      _ = _ := by
        rw [heatNormalScalarLift_integral D C hE hCt hP hD ψ (hψs.trans hs)]
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! An actual quadratic integral bound for the global normal amplitude.
This keeps Gaussian spatial concentration, unlike the uniform norm bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem heatNormalAmplitudeL2_norm_sq_le_integral
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) :
    ‖heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs‖ ^ 2 ≤
      2 * (normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ‖a x‖ ^ 2 := by
  let F := heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs
  let ψ := fun x => ‖a x‖ ^ 2
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have hz : a x = 0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    change ‖a x‖ ^ 2 = 0
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := (ha.continuous.norm.pow 2).continuousOn
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hs)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (f : FrameBundle g) : ‖F f‖ ^ 2 = 2 * heatNormalScalarLift C ψ f.base := by
    by_cases hf : f.base ∈ C.target
    · rw [heatNormalAmplitudeTensor_norm_sq C hE hCt hP hD a ha hc hs f hf,
        heatNormalScalarLift_on_target C ψ hf]
    · have hz : F f = 0 := by
        change WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f) = _
        simp only [heatNormalFrameTensorLift, ite_eq_right hf]
        rfl
      rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      simp only [heatNormalScalarLift, ite_eq_right hf, mul_zero]
  have hn := twoFormFromTensorL2_norm_le
    (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F)
  calc
    _ ≤ ‖ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F‖ ^ 2 := by
      change ‖twoFormFromTensorL2 (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F)‖ ^ 2 ≤ _
      nlinarith [norm_nonneg (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F),
        norm_nonneg (twoFormFromTensorL2 (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F))]
    _ = ∫ f, ‖F f‖ ^ 2 ∂canonicalFrameMeasure g o := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F] with f hf
      rw [hf, real_inner_self_eq_norm_sq]
    _ = 2 * ∫ y, heatNormalScalarLift C ψ y ∂normalizedVolume g := by
      simp_rw [heq]
      rw [integral_const_mul, canonicalFrameMeasure_integral_base g o _ hLi]
    _ = _ := by
      rw [heatNormalScalarLift_integral D C hE hCt hP hD ψ (hψs.trans hs)]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual global residual retains the local cancellation and has
an L2 bound of order t for the constructed chart and cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.timeColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalGlobalTimeColumn E P.chart P.in_chart P.point_regular P.inside_radius
    P.cutoff (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact P.cutoff_support t l

def HeatNormalParametrixData.residual (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalAmplitudeL2 D P.chart P.in_chart P.point_regular P.inside_radius
    (heatNormalResidualColumn E P.cutoff t l)
    (heatNormalResidualColumn_regular E P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalResidualColumn_support E P.cutoff t l))
    ((heatNormalResidualColumn_support E P.cutoff t l).trans P.cutoff_support)

theorem HeatNormalParametrixData.residual_eq (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) :
    P.residual E t l = P.timeColumn E t l + P.operatorColumn E t l := by
  exact heatNormalAmplitudeL2_add P.chart P.in_chart P.point_regular P.inside_radius
    (heatNormalTimeColumn E P.cutoff t l)
    (heatNormalOperatorAmplitude E (heatNormalCutoffColumn E P.cutoff t l))
    (heatNormalTimeColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (heatNormalOperatorAmplitude_regular E _ (heatNormalCutoffColumn_regular_four E P.cutoff P.cutoff_regular t l))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalTimeColumn_support E P.cutoff t l))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      ((heatNormalOperatorAmplitude_support E _).trans (heatNormalCutoffColumn_support E P.cutoff t l)))
    ((heatNormalTimeColumn_support E P.cutoff t l).trans P.cutoff_support)
    (((heatNormalOperatorAmplitude_support E _).trans
      (heatNormalCutoffColumn_support E P.cutoff t l)).trans P.cutoff_support)

theorem HeatNormalParametrixData.residual_norm_le (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (ht : 0 < t) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ x k l, |deriv (fun s => heatNormalCutoffParametrix E P.cutoff s x k l) t +
      fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalCutoffParametrix E P.cutoff t y q l) x k| ≤ B * t)
    (l : Fin 6) : ‖P.residual E t l‖ ≤ (6 * B) * t := by
  have hn := heatNormalAmplitudeL2_norm_le P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius (heatNormalResidualColumn E P.cutoff t l)
    (heatNormalResidualColumn_regular E P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalResidualColumn_support E P.cutoff t l))
    ((heatNormalResidualColumn_support E P.cutoff t l).trans P.cutoff_support)
    (3 * (B * t)) (by positivity) (heatNormalResidualColumn_bound E P.cutoff t ht B hB h l)
  exact hn.trans_eq (by ring)

theorem exists_heatNormalGlobalResidual (E : HeatNormalBundleExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) (hepos : e ∈ o.positive) :
    ∃ P : HeatNormalParametrixData D,
      (∀ t l, ∃ hf : P.column E t l ∈ twoFormHodgeDomain hRic,
        twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l) ∧
      ∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t := by
  obtain ⟨P, hP, B, hB, hb⟩ := exists_heatNormalParametrixData E he hRic hepos
  exact ⟨P, hP, 6 * B, by positivity,
    fun t ht l => P.residual_norm_le E t ht.1 B hB (hb t ht) l⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal one-form parametrix tends to the correctly normalized delta. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneCutoffParametrix_initial_local {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    {D : HeatNormalFrameData g o c e} (E : HeatNormalOneExtension D)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1) (k l : Fin 4) :
    Tendsto (fun t => ∫ x, heatNormalOneCutoffParametrix E χ t x k l * f x)
      (𝓝[Ioi 0] 0) (𝓝 ((if k = l then 1 else 0) * f 0)) := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => (χ x * f x) * E.amplitude m x k l
  have hu (m : Fin 4) : Continuous (u m) :=
    hχf.mul (E.amplitude_regular m (by omega) k l).continuous
  have huc (m : Fin 4) : HasCompactSupport (u m) := (hχc.mul_right).mul_right
  have hb (m : Fin 4) : ∃ C : ℝ, ∀ x, ‖u m x‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((huc m).isCompact_range (hu m)).bddAbove_image
      continuous_norm.continuousOn
    exact ⟨C, fun x => hC (mem_image_of_mem _ (mem_range_self x))⟩
  choose C hC using hb
  have h := fourHeatPolynomial_approximate_identity u hu C hC
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hzero : u 0 0 = (if k = l then 1 else 0) * f 0 := by
    change (χ 0 * f 0) * E.amplitude 0 0 k l = _
    rw [hχ0, E.amplitude_zero, hU]
    simp only [one_smul, Matrix.one_apply, one_mul]
    ring
  rw [hzero] at h
  apply h.congr'
  exact Eventually.of_forall fun t => by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [heatNormalOneCutoffParametrix, heatNormalOneParametrix,
        fourHeatOnePolynomial, fourHeatPolynomial, u]
      ring


variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.one_initial (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (v : smoothCovariantFields M 1) (l : Fin 4) :
    Tendsto (fun t => inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear v))
      (𝓝[Ioi 0] 0) (𝓝 ((normalizedChartFactor g).toReal * heatNormalOneValue c D.point v 0 l)) := by
  let f := fun k x => frameExponentialJacobian g o e x * heatNormalOneValue c D.point v x k
  have hf (k : Fin 4) : ContinuousOn (f k) P.chart.source := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    exact (frameExponentialJacobian_continuous g o e).continuousAt.mul
      (heatNormalOneFormValue_regular 2 c D.point v x
        (P.point_regular.contDiffAt (P.chart.open_source.mem_nhds hx))
        (D.in_chart x (P.inside_radius hx)) k).continuousAt
  have hχf (k : Fin 4) : Continuous (fun x => P.cutoff x * f k x) :=
    heat_continuous_mul_of_tsupport_subset P.cutoff_regular.continuous P.chart.open_source
      (hf k) P.cutoff_support
  have h := (tendsto_finsetSum Finset.univ fun k _ =>
    heatNormalOneCutoffParametrix_initial_local E P.cutoff (f k) (hχf k)
      P.cutoff_compact P.cutoff_zero k l).const_mul (normalizedChartFactor g).toReal
  have hz : (∑ k : Fin 4, (if k = l then 1 else 0) * f k 0) = heatNormalOneValue c D.point v 0 l := by
    simp [f, frameExponentialJacobian_zero]
  rw [hz] at h
  apply h.congr'
  exact Eventually.of_forall fun t => (heatNormalOneAmplitudeL2_pairing_sum
    P.chart P.exponential P.in_chart P.point_regular P.inside_radius
    (heatNormalOneCutoffColumn E P.cutoff t l)
    ((heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l).of_le (by norm_num))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support E P.cutoff t l))
    ((heatNormalOneCutoffColumn_support E P.cutoff t l).trans P.cutoff_support) v).symm

def HeatNormalParametrixData.oneNormalizedColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  ((normalizedChartFactor g).toReal)⁻¹ • P.oneColumn E t l

theorem HeatNormalParametrixData.one_normalized_initial (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (v : smoothCovariantFields M 1) (l : Fin 4) :
    Tendsto (fun t => inner ℝ (P.oneNormalizedColumn E t l) (smoothOneFormL2Linear v))
      (𝓝[Ioi 0] 0) (𝓝 (covariantFieldFramed g v.val e ![l])) := by
  have hv : heatNormalOneValue c D.point v 0 l = covariantFieldFramed g v.val e ![l] := by
    change frameTensor (D.point 0).2 (covariantFieldCoordinates v.val c (D.point 0).1) ![l] = _
    rw [D.initial]
    exact (congrFun (heat_covariantField_chart g v.val c e he) ![l]).symm
  have h := (P.one_initial E v l).const_mul ((normalizedChartFactor g).toReal)⁻¹
  rw [hv, ← mul_assoc, inv_mul_cancel₀ (normalizedChartFactor_toReal_pos g).ne', one_mul] at h
  simpa only [HeatNormalParametrixData.oneNormalizedColumn, real_inner_smul_left] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two coefficients that survive the signed Gaussian limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeat_second_partial_eq_fderiv (f : FourSpace → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (i j : Fin 4) :
    partialDeriv (partialDeriv f i) j 0 =
      fderiv ℝ (fderiv ℝ f) 0 (coordinateVector j) (coordinateVector i) := by
  let L := ContinuousLinearMap.apply ℝ ℝ (coordinateVector i)
  have hd := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  exact congrArg (fun K : FourSpace →L[ℝ] ℝ => K (coordinateVector j))
    (L.hasFDerivAt.comp 0 hd).fderiv

theorem heatSignedGram_scalar_sub (a : ℝ) (V : HeatMat6)
    (hV : Vᵀ = V) (htrace : (twoFormHodgeMatrix * V).trace = 0) :
    heatSignedGram (a • 1 - V) (a • 1 - V) = (twoFormHodgeMatrix * V * V).trace := by
  unfold heatSignedGram
  rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, hV]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul,
    twoFormHodgeMatrix_trace, htrace, mul_zero, sub_zero, zero_sub, neg_neg]
  exact congrArg Matrix.trace (Matrix.mul_assoc twoFormHodgeMatrix V V).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

omit [T3Space M] [CompactSpace M] in
theorem heat_actual_potential_symmetric (e : FrameBundle g) :
    (twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e))ᵀ =
      twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) := by
  have hR : ∀ i j k l, twoFormMetricCurvatureTensor g e ![k,l,i,j] =
      twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    intro i j k l
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame) i j k l
  simp only [twoFormPotentialMatrix, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, twoFormCurvatureMatrix_symmetric _ hR]

theorem HeatNormalBundleExtension.first_amplitude_signed_gram
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source) :
    heatSignedGram (E.amplitude 1 0) (E.amplitude 1 0) =
      (twoFormHodgeMatrix * twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace := by
  rw [E.first_amplitude_intrinsic_center he]
  exact heatSignedGram_scalar_sub _ _ (heat_actual_potential_symmetric e)
    (heat_actual_potential_signed_trace e)

theorem HeatNormalBundleExtension.signedFirst_second (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiffAt ℝ 2 χ 0) (hχ0 : χ 0 = 1)
    (he : e.base ∈ (chartAt FourSpace c).source) (i : Fin 4) :
    partialDeriv (partialDeriv (E.signedFirst χ) i) i 0 =
      partialDeriv (partialDeriv (fun x => (twoFormHodgeMatrix * E.amplitude 1 x).trace) i) i 0 := by
  let W := fun x => frameExponentialJacobian g o e x * χ x ^ 2 * E.base.U x
  have hW : ContDiffAt ℝ 2 W 0 :=
    (((frameExponentialJacobian_smoothAt_zero g o e).of_le (by norm_num)).mul
      (hχ.pow 2)).mul (E.base.U_regular.of_le (by norm_num)).contDiffAt
  have hU : E.base.U 0 = 1 := E.base.U_near.self_of_nhds.trans
    (heatNormalLeadingAmplitude_zero g o e)
  change partialDeriv (partialDeriv (fun x => W x *
    (twoFormHodgeMatrix * E.amplitude 1 x).trace) i) i 0 = _
  rw [scalar_partial_second_product_at _ _ 0 hW
    (E.signed_amplitude_regular 1 (by norm_num)).contDiffAt,
    E.first_amplitude_signed_trace he, E.first_amplitude_signed_partial]
  simp [W, frameExponentialJacobian_zero, hχ0, hU]

theorem HeatNormalBundleExtension.signedFirst_hessian_trace
    {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (hχ : ContDiffAt ℝ 2 χ 0) (hχ0 : χ 0 = 1) :
    (∑ i, fderiv ℝ (fderiv ℝ (E.signedFirst χ)) 0 (coordinateVector i) (coordinateVector i)) =
      (1 / 6 : ℝ) * ∑ i, ∑ j, (twoFormHodgeMatrix *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j *
        twoFormConnectionCurvatureMatrix (twoFormMetricCurvatureTensor g ⟨c, f⟩) i j).trace := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← fourHeat_second_partial_eq_fderiv _ (E.signedFirst_regular χ hχ) i i,
    E.signedFirst_second χ hχ hχ0 (mem_chart_source FourSpace c), E.first_amplitude_signed_second]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar cutoff can be chosen inside the common geometric and
transport neighborhood. The coefficient and nondegeneracy conditions
used in the residual realization are thereby actual proved properties. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem exists_heatScalarAdaptedChart (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g) (hepos : e ∈ o.positive) :
    ∃ P : HeatScalarChartData D,
      (∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹) ∧
      (∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x) ∧
      (∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det) ∧
      (∀ x, |P.cutoff x| ≤ 1) ∧
      (∃ s > (0 : ℝ), ∀ x ∈ ball 0 s, P.cutoff x = 1) ∧
      (∀ x ∈ tsupport P.cutoff, ∀ t > (0 : ℝ),
        deriv (fun v => P.extension.scalarParametrix v x) t +
          fourHeatLocalOperator (P.extension.a x) (P.extension.b x) 0
            (P.extension.scalarParametrix t) x =
          fourHeatGaussian t x * t ^ 3 * fourHeatLocalOperator (P.extension.a x)
            (P.extension.b x) 0 (P.extension.scalarAmplitude 3) x) := by
  obtain ⟨E⟩ := exists_heatNormalExtension 10 g o e
  obtain ⟨rT, hrT, hT⟩ := E.scalarParametrix_residual hRic hepos
  have hdet : ContDiffAt ℝ ∞ (fun x => (heatNormalMetric g o e x).det) 0 := by
    simp only [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ _
    exact contDiffAt_const.mul
      (contDiffAt_prod fun i _ => heatNormalMetric_smoothAt_zero g o e (σ i) i)
  have hpos : ∀ᶠ x in 𝓝 (0 : FourSpace), 0 < (heatNormalMetric g o e x).det :=
    hdet.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (show
      (0 : ℝ) < (heatNormalMetric g o e 0).det from by
      rw [heatNormalMetric_zero, Matrix.det_one]
      exact zero_lt_one))
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), E.a x = (heatNormalMetric g o e x)⁻¹ ∧
      E.b x = heatNormalDrift g o e x ∧ 0 < (heatNormalMetric g o e x).det ∧ x ∈ ball 0 rT := by
    filter_upwards [E.a_near, E.b_near, hpos, ball_mem_nhds (0 : FourSpace) hrT]
      with x ha hb hd hx
    exact ⟨ha, hb, hd, hx⟩
  obtain ⟨r₀, hr₀, hball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨rC, C, hrC, hC, hE, hI, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  let R := min r₀ rC
  have hR : 0 < R := lt_min hr₀ hrC
  let χ := heatNormalChartBump R hR
  have hsR : tsupport χ ⊆ ball (0 : FourSpace) R := by
    rw [χ.tsupport_eq]
    exact closedBall_subset_ball (by change R / 2 < R; linarith)
  have hsC : tsupport χ ⊆ C.source := by
    rw [hC]
    exact hsR.trans (ball_subset_ball (min_le_right _ _))
  let P : HeatScalarChartData D := {
    extension := E
    chart := C
    exponential := hE
    in_chart := hCt
    point_regular := hP
    inverse_regular := hI
    inside_radius := hD
    cutoff := χ
    cutoff_regular := χ.contDiff
    cutoff_compact := χ.hasCompactSupport
    cutoff_support := hsC
    cutoff_zero := χ.one_of_mem_closedBall
      (mem_closedBall_self (by change 0 ≤ R / 4; positivity)) }
  have hnear (x : FourSpace) (hx : x ∈ tsupport P.cutoff) :=
    hball ((ball_subset_ball (min_le_left r₀ rC)) (hsR hx))
  refine ⟨P, (fun x hx => (hnear x hx).1), (fun x hx => (hnear x hx).2.1),
    (fun x hx => (hnear x hx).2.2.1), ?_, ?_, ?_⟩
  · intro x
    rw [abs_of_nonneg χ.nonneg]
    exact χ.le_one
  · refine ⟨R / 4, by positivity, ?_⟩
    intro x hx
    exact χ.one_of_mem_closedBall (ball_subset_closedBall hx)
  · intro x hx t ht
    exact hT x (hnear x hx).2.2.2 t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global scalar parametrix has exact normal-coordinate pairings,
including the explicit factor from the normalized geometric volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatNormalScalarLift_mul {X : Type*} [TopologicalSpace X]
    (C : OpenPartialHomeomorph FourSpace X) (ψ : FourSpace → ℝ) (f : X → ℝ) (x : X) :
    heatNormalScalarLift C ψ x * f x =
      heatNormalScalarLift C (fun y => ψ y * f (C y)) x := by
  classical
  by_cases hx : x ∈ C.target
  · rw [heatNormalScalarLift_on_target C ψ hx, heatNormalScalarLift_on_target C _ hx,
      C.right_inv hx]
  · simp only [heatNormalScalarLift, ite_eq_right hx, zero_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance scalarGlobal_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem HeatScalarChartData.column_pairing (P : HeatScalarChartData D)
    (t : ℝ) (f : C(M, ℝ)) :
    inner ℝ (P.column t) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f) =
      (normalizedChartFactor g).toReal * ∫ x,
        P.extension.scalarCutoff P.cutoff t x *
          (frameExponentialJacobian g o e x * f (P.chart x)) := by
  rw [L2.inner_def]
  calc
    _ = ∫ y, P.function t y * f y ∂normalizedVolume g := by
      apply integral_congr_ae
      filter_upwards [scalarFiniteValueL2_coe g (P.function t) (P.function_regular t),
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g) f] with y hy hf
      simp only [RCLike.inner_apply', conj_trivial, HeatScalarChartData.column, hy, hf]
    _ = ∫ y, heatNormalScalarLift P.chart
        (fun x => P.extension.scalarCutoff P.cutoff t x * f (P.chart x)) y
          ∂normalizedVolume g := by
      apply integral_congr_ae
      exact Eventually.of_forall (heatNormalScalarLift_mul P.chart _ f)
    _ = _ := by
      rw [heatNormalScalarLift_integral D P.chart P.exponential P.in_chart
        (P.point_regular.of_le (by norm_num)) P.inside_radius]
      · congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      · exact tsupport_mul_subset_left.trans
          ((P.extension.scalarCutoff_support P.cutoff t).trans P.cutoff_support)

def HeatScalarChartData.normalizedColumn (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) :=
  ((normalizedChartFactor g).toReal)⁻¹ • P.column t

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatScalarChartData.chart_zero (P : HeatScalarChartData D) :
    P.chart 0 = e.base := by
  have hz : (0 : FourSpace) ∈ P.chart.source := P.cutoff_support
    (subset_tsupport P.cutoff (by rw [Function.mem_support, P.cutoff_zero]; exact one_ne_zero))
  exact (P.exponential hz).trans (frameExponential_zero g o e)

theorem HeatScalarChartData.column_initial (P : HeatScalarChartData D) (f : C(M, ℝ)) :
    Tendsto (fun t => inner ℝ (P.column t) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f))
      (𝓝[Ioi 0] 0) (𝓝 ((normalizedChartFactor g).toReal * f e.base)) := by
  let F := fun x => frameExponentialJacobian g o e x * f (P.chart x)
  have hF : ContinuousOn F P.chart.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      (f.continuous.comp_continuousOn P.chart.continuousOn)
  have hχF := heat_continuous_mul_of_tsupport_subset P.cutoff_regular.continuous
    P.chart.open_source hF P.cutoff_support
  have h := (P.extension.scalarCutoff_initial P.cutoff F hχF P.cutoff_compact
    P.cutoff_zero).const_mul (normalizedChartFactor g).toReal
  have hz : F 0 = f e.base := by
    dsimp only [F]
    rw [frameExponentialJacobian_zero, P.chart_zero, one_mul]
  rw [hz] at h
  exact h.congr' (Eventually.of_forall fun t => (P.column_pairing t f).symm)

theorem HeatScalarChartData.normalizedColumn_initial (P : HeatScalarChartData D)
    (f : C(M, ℝ)) :
    Tendsto (fun t => inner ℝ (P.normalizedColumn t)
      (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f)) (𝓝[Ioi 0] 0) (𝓝 (f e.base)) := by
  have h := (P.column_initial f).const_mul ((normalizedChartFactor g).toReal)⁻¹
  have hn : (normalizedChartFactor g).toReal ≠ 0 := (normalizedChartFactor_toReal_pos g).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul] at h
  simpa only [HeatScalarChartData.normalizedColumn, real_inner_smul_left] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The cutoff scalar column has exactly the geometric Laplacian prescribed
by the normal-coordinate operator on the actual chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.scalar_laplacian_local (P : HeatScalarChartData D)
    (f : M → ℝ) (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (x : FourSpace)
    (hx : x ∈ P.chart.source) (hd : 0 < (heatNormalMetric g o e x).det) :
    fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
      (fun y => f (P.chart y)) x = -scalarLaplacianBase g f (P.chart x) := by
  let φ := fun z => f ((chartAt FourSpace c).symm z)
  have htarget := D.in_chart x (P.inside_radius hx)
  have hφ : ContDiffAt ℝ 2 φ (D.point x).1 :=
    ((hf.contMDiffAt.comp _ (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas c) htarget)).contDiffAt).of_le (by norm_num)
  have hpoint (y : FourSpace) (hy : y ∈ P.chart.source) :
      (D.point y).1 = chartAt FourSpace c (P.chart y) :=
    (D.exponential y (P.inside_radius hy)).trans
      (congrArg (chartAt FourSpace c) (P.exponential hy).symm)
  have hcomp : (fun y => φ (D.point y).1) =ᶠ[𝓝 x] (fun y => f (P.chart y)) := by
    filter_upwards [P.chart.open_source.mem_nhds hx] with y hy
    dsimp only [φ]
    rw [hpoint y hy, (chartAt FourSpace c).left_inv (P.in_chart (P.chart.map_source hy))]
  have hs : frameExponential g o e x ∈ (chartAt FourSpace c).source := by
    rw [← P.exponential hx]
    exact P.in_chart (P.chart.map_source hx)
  calc
    _ = fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
        (fun y => φ (D.point y).1) x := (fourHeatLocalOperator_germ _ _ _ hcomp).symm
    _ = -scalarChartOperator g c φ (D.point x).1 := D.scalar_operator_pullback x
      (P.inside_radius hx) (P.point_regular.contDiffAt (P.chart.open_source.mem_nhds hx) |>.of_le
        (by norm_num)) hs hd φ hφ
    _ = -scalarLaplacianBase g f ((chartAt FourSpace c).symm (D.point x).1) :=
      congrArg Neg.neg (scalar_finite_chart_laplacian g hf c ⟨_, htarget⟩).symm
    _ = _ := by
      rw [hpoint x hx, (chartAt FourSpace c).left_inv (P.in_chart (P.chart.map_source hx))]

theorem HeatScalarChartData.column_laplacian_local (P : HeatScalarChartData D)
    (t : ℝ) (x : FourSpace) (hx : x ∈ P.chart.source)
    (hd : 0 < (heatNormalMetric g o e x).det) :
    fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
      (P.extension.scalarCutoff P.cutoff t) x =
        -scalarLaplacianBase g (P.function t) (P.chart x) := by
  have he : (fun y => P.function t (P.chart y)) =ᶠ[𝓝 x]
      P.extension.scalarCutoff P.cutoff t := by
    filter_upwards [P.chart.open_source.mem_nhds hx] with y hy
    exact heatNormalScalarLift_source P.chart _ hy
  rw [← fourHeatLocalOperator_germ _ _ _ he]
  exact P.scalar_laplacian_local (P.function t) (P.function_regular t) x hx hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! Common actual parametrices have their Hodge generator identity and
one global L2 residual bound, uniformly in the nearby initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem exists_heatActualUniformParametrix (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) :
    ∃ E : HeatFamilySmoothCoefficients, ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      ∃ B ≥ (0 : ℝ), ∀ e' ∈ U,
        ∃ N : HeatCommonNormalMember g o e.base E r e',
          (∀ t l, ∃ hf : (N.parametrixData hr).column N.extension t l ∈ twoFormHodgeDomain hRic,
            twoFormHodgeGenerator hRic ⟨(N.parametrixData hr).column N.extension t l, hf⟩ =
              (N.parametrixData hr).operatorColumn N.extension t l) ∧
          (e' ∈ o.positive → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
            ‖(N.parametrixData hr).residual N.extension t l‖ ≤ B * t) := by
  obtain ⟨E, r, hr, U, hU, heU, B, hB, hN⟩ := exists_heatActualUniformResidual g o hRic e
  refine ⟨E, r, hr, U, hU, heU, 6 * B, by positivity, ?_⟩
  intro e' he'
  obtain ⟨N, hb⟩ := hN e' he'
  refine ⟨N, N.parametrixData_generator hr hRic, ?_⟩
  intro hepos t ht l
  apply (N.parametrixData hr).residual_norm_le N.extension t ht.1 B hB _ l
  simpa only [N.parametrixData_cutoff hr] using hb hepos t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! Cancellation of the differentiated first coefficient leaves the
actual quadratic Weitzenbock trace in the second Euler coefficient. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.second_amplitude_center (E : HeatNormalOneExtension D) :
    (2 : ℝ) • E.amplitude 2 0 =
      -heatOneMatrixScalarOperator (E.base.a 0) (E.base.b 0) (E.amplitude 1) 0 -
        ((3 : ℝ) • (1 : Mat4)) * E.amplitude 1 0 := by
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hB : E.B 0 = fun _ => 0 := by
    funext i
    exact (congrFun E.B_near.self_of_nhds i).trans (D.oneFirst_zero i)
  have hC : E.C 0 = (3 : ℝ) • (1 : Mat4) :=
    E.C_near.self_of_nhds.trans D.oneZero_center
  ext k l
  have hrec := fourHeatOneCoefficient_center 1 E.base.a E.base.b E.B E.C E.base.U
    (by rw [hU]; exact one_ne_zero) k l
  have hrec' : (2 : ℝ) * E.amplitude 2 0 k l =
      -fourHeatOneOperator (E.base.a 0) (E.base.b 0) (E.B 0) (E.C 0)
        (fun y q => E.amplitude 1 y q l) 0 k := by
    simpa only [HeatNormalOneExtension.amplitude, Nat.cast_one, one_add_one_eq_two] using hrec
  rw [hB, hC] at hrec'
  simp only [fourHeatOneOperator, fourHeatOneFirst, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, fourHeatOneZero] at hrec'
  change 2 * E.amplitude 2 0 k l =
    -fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 (fun y => E.amplitude 1 y k l) 0 -
      ∑ q, ((3 : ℝ) • (1 : Mat4)) k q * E.amplitude 1 0 q l
  linarith only [hrec']

def HeatNormalBundleExtension.eulerSecondAmplitude (E : HeatNormalBundleExtension D)
    (x : FourSpace) : ℝ :=
  2 * fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 2 x -
    2 * (E.oneCompanion.amplitude 2 x).trace + (E.amplitude 2 x).trace

theorem HeatNormalBundleExtension.eulerSecondAmplitude_center
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    E.eulerSecondAmplitude 0 =
      ((twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
        twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace - 72) / 2 := by
  let α := -fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 E.base.U 0
  have hU : E.base.U 0 ≠ 0 := (E.base.U_pos 0).ne'
  have hscalar := fourHeatCoefficient_center 1 E.base.a E.base.b (fun _ => 0) E.base.U hU
  have hfirst₁ : (E.oneCompanion.amplitude 1 0).trace = 4 * α - 12 := by
    rw [E.oneCompanion.first_amplitude_center]
    rw [show E.oneCompanion.base = E.base from rfl]
    norm_num [Matrix.trace_sub, Matrix.trace_smul, α]
    ring
  have hsecond₁ := congrArg Matrix.trace E.oneCompanion.second_amplitude_center
  rw [show E.oneCompanion.base = E.base from rfl] at hsecond₁
  simp only [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_neg,
    Matrix.smul_mul, Matrix.one_mul, smul_eq_mul] at hsecond₁
  rw [hfirst₁] at hsecond₁
  have hsecond₂ := congrArg Matrix.trace (E.second_amplitude_center he)
  rw [E.first_amplitude_intrinsic_center he] at hsecond₂
  simp only [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_neg,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_eq_mul] at hsecond₂
  rw [actual_twoFormPotential_trace hRic e] at hsecond₂
  have hcancel := E.eulerFirst_scalar_operator_zero hRic
  change 2 * fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 2 0 -
    2 * (E.oneCompanion.amplitude 2 0).trace + (E.amplitude 2 0).trace = _
  norm_num only [Nat.cast_one, one_add_one_eq_two] at hscalar
  dsimp only [α] at hfirst₁
  dsimp only [α] at hsecond₁
  linarith only [hscalar, hsecond₁, hsecond₂, hcancel]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact normal-coordinate pairing of two finite-regularity amplitudes
inside the actual two-form Hilbert space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance heatNormalInnerCompact : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
local instance heatNormalInnerProbability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem heatNormalAmplitudeTensor_inner
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a b : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ C.source) (hsb : tsupport b ⊆ C.source)
    (f : FrameBundle g) (hf : f.base ∈ C.target) :
    inner ℝ (heatNormalAmplitudeTensor D C hCt hP hD a ha hca hsa f)
      (heatNormalAmplitudeTensor D C hCt hP hD b hb hcb hsb f) =
      2 * inner ℝ (a (C.symm f.base)) (b (C.symm f.base)) := by
  let x := C.symm f.base
  have hx : x ∈ C.source := C.map_target hf
  have hxb := hD hx
  have hbase : (D.point x).1 = chartAt FourSpace c f.base := by
    rw [D.exponential x hxb, ← hE hx, C.right_inv hf]
  have hF := frameChartMatrix_normalizes g c f (hCt hf)
  rw [← hbase] at hF
  have hi : (D.point x).2⁻¹ * (D.point x).2 = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (heatNormalFrame_matrix_nondegenerate D hxb))
  have hback : frameTensor (D.point x).2 (heatNormalCoordinateTensor D b x) = twoFormTensor (b x) := by
    unfold heatNormalCoordinateTensor
    rw [← frameTensor_mul, hi, frameTensor_one]
  change inner ℝ (WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f)
    : TwoTensorEuclidean) (WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D b) f)) = _
  rw [heat_euclideanTensor_inner]
  simp only [heatNormalFrameTensorLift, ite_eq_left hf]
  change frameTensorPairing
    (frameTensor (frameChartMatrix g c f) (frameTensor (D.point x).2⁻¹ (twoFormTensor (a x))))
    (frameTensor (frameChartMatrix g c f) (heatNormalCoordinateTensor D b x)) = _
  rw [heat_normal_frame_pairing _ _ _ (D.orthonormal x hxb) hF, hback, twoFormTensor_pairing]

theorem heatNormalAmplitudeL2_inner_integral
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a b : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ C.source) (hsb : tsupport b ⊆ C.source) :
    inner ℝ (heatNormalAmplitudeL2 D C hCt hP hD a ha hca hsa)
      (heatNormalAmplitudeL2 D C hCt hP hD b hb hcb hsb) =
      (normalizedChartFactor g).toReal * ∫ x, frameExponentialJacobian g o e x * inner ℝ (a x) (b x) := by
  let A := heatNormalAmplitudeTensor D C hCt hP hD a ha hca hsa
  let B := heatNormalAmplitudeTensor D C hCt hP hD b hb hcb hsb
  let ψ := fun x => inner ℝ (a x) (b x)
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have hz : a x = 0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    change inner ℝ (a x) (b x) = 0
    rw [hz, inner_zero_left]
  have hψc : HasCompactSupport ψ := hca.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := (ha.continuous.inner hb.continuous).continuousOn
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hsa)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (f : FrameBundle g) : inner ℝ (A f) (B f) = 2 * heatNormalScalarLift C ψ f.base := by
    by_cases hf : f.base ∈ C.target
    · rw [heatNormalAmplitudeTensor_inner C hE hCt hP hD a b ha hb hca hcb hsa hsb f hf,
        heatNormalScalarLift_on_target C ψ hf]
    · have hz : A f = 0 := by
        change WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f) = _
        simp only [heatNormalFrameTensorLift, ite_eq_right hf]
        rfl
      rw [hz, inner_zero_left]
      simp only [heatNormalScalarLift, ite_eq_right hf, mul_zero]
  have hcalc : 2 * inner ℝ (heatNormalAmplitudeL2 D C hCt hP hD a ha hca hsa)
      (heatNormalAmplitudeL2 D C hCt hP hD b hb hcb hsb) =
      2 * ((normalizedChartFactor g).toReal * ∫ x, frameExponentialJacobian g o e x * ψ x) := by
    rw [← twoFormTensorL2_inner,
      heatNormalAmplitudeTensor_L2_realization C hCt hP hD a ha hca hsa,
      heatNormalAmplitudeTensor_L2_realization C hCt hP hD b hb hcb hsb, L2.inner_def]
    change (∫ f, inner ℝ ((ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ A) f)
      ((ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ B) f) ∂canonicalFrameMeasure g o) = _
    have he : (∫ f, inner ℝ ((ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ A) f)
        ((ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ B) f) ∂canonicalFrameMeasure g o) =
        ∫ f, inner ℝ (A f) (B f) ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) A,
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) B] with f hA hB
      rw [hA, hB]
    rw [he]
    simp_rw [heq]
    rw [integral_const_mul, canonicalFrameMeasure_integral_base g o _ hLi,
      heatNormalScalarLift_integral D C hE hCt hP hD ψ (hψs.trans hsa)]
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual global parametrix column has L2 growth at most t⁻¹. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.column_growth (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (l : Fin 6) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.column E t l‖ ≤ C / t := by
  obtain ⟨B, hB, hb⟩ := heatNormalCutoffColumn_square_integral_bound E P.cutoff
    (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact l
  let K := 2 * (normalizedChartFactor g).toReal * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro t ht
  have hn := heatNormalAmplitudeL2_norm_sq_le_integral P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius (heatNormalCutoffColumn E P.cutoff t l)
    (heatNormalCutoffColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support E P.cutoff t l))
    ((heatNormalCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)
  have hn' : ‖P.column E t l‖ ^ 2 ≤ K / t ^ 2 := by
    exact hn.trans ((mul_le_mul_of_nonneg_left (hb t ht) (by positivity)).trans_eq (by dsimp [K]; ring))
  have hs : (‖P.column E t l‖ * t) ^ 2 ≤ K := by
    calc
      _ = ‖P.column E t l‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (K / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      _ = K := by field_simp [ht.1.ne']
  apply (le_div_iff₀ ht.1).mpr
  nlinarith [sq_nonneg K, norm_nonneg (P.column E t l)]

theorem HeatNormalParametrixData.normalizedColumn_growth (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (l : Fin 6) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.normalizedColumn E t l‖ ≤ C / t := by
  obtain ⟨C, hC, hc⟩ := P.column_growth E l
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * C, by positivity, ?_⟩
  intro t ht
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.column E t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hc t ht) (norm_nonneg _)).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual global parametrix column has L2 growth at most t⁻¹. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.oneColumn_growth (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (l : Fin 4) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.oneColumn E t l‖ ≤ C / t := by
  obtain ⟨B, hB, hb⟩ := heatNormalOneCutoffColumn_square_integral_bound E P.cutoff
    P.cutoff_regular P.cutoff_compact l
  let K := (normalizedChartFactor g).toReal * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro t ht
  have hn := heatNormalOneAmplitudeL2_norm_sq_integral P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius (heatNormalOneCutoffColumn E P.cutoff t l)
    ((heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l).of_le (by norm_num))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support E P.cutoff t l))
    ((heatNormalOneCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)
  have hn' : ‖P.oneColumn E t l‖ ^ 2 ≤ K / t ^ 2 := by
    exact (le_of_eq hn).trans ((mul_le_mul_of_nonneg_left (hb t ht) (by positivity)).trans_eq (by dsimp [K]; ring))
  have hs : (‖P.oneColumn E t l‖ * t) ^ 2 ≤ K := by
    calc
      _ = ‖P.oneColumn E t l‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (K / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      _ = K := by field_simp [ht.1.ne']
  apply (le_div_iff₀ ht.1).mpr
  nlinarith [sq_nonneg K, norm_nonneg (P.oneColumn E t l)]

theorem HeatNormalParametrixData.oneNormalizedColumn_growth (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (l : Fin 4) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.oneNormalizedColumn E t l‖ ≤ C / t := by
  obtain ⟨C, hC, hc⟩ := P.oneColumn_growth E l
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * C, by positivity, ?_⟩
  intro t ht
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.oneColumn E t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hc t ht) (norm_nonneg _)).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Each actual smooth one-form eigenmode obeys the forced heat equation
for the genuinely constructed normal parametrix. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.one_eigen_evolution
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (t : ℝ) (ht : 0 < t) (l : Fin 4) (i : OneFormEigenIndex hRic d) :
    HasDerivAt (fun s => inner ℝ (P.oneColumn E s l) (oneFormEigenvector hRic d i))
      (inner ℝ (P.oneResidual E t l) (oneFormEigenvector hRic d i) -
        oneFormHeatRate hRic d i * inner ℝ (P.oneColumn E t l) (oneFormEigenvector hRic d i)) t := by
  obtain ⟨v, hv, hLv⟩ := oneFormEigenvector_smooth hRic d i
  have hL : smoothOneFormL2Linear (o := o) (smoothOneFormHodgeLaplacian (o := o) v) =
      oneFormHeatRate hRic d i • oneFormEigenvector hRic d i := by
    rw [hLv, map_smul, ← hv]
  have h := P.oneWeakEvolution E hpair t ht l v
  rw [hL, real_inner_smul_right, ← hv] at h
  exact h

def HeatNormalParametrixData.oneNormalizedResidual (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  ((normalizedChartFactor g).toReal)⁻¹ • P.oneResidual E t l

theorem HeatNormalParametrixData.one_normalized_eigen_evolution
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (t : ℝ) (ht : 0 < t) (l : Fin 4) (i : OneFormEigenIndex hRic d) :
    HasDerivAt (fun s => inner ℝ (P.oneNormalizedColumn E s l) (oneFormEigenvector hRic d i))
      (inner ℝ (P.oneNormalizedResidual E t l) (oneFormEigenvector hRic d i) -
        oneFormHeatRate hRic d i * inner ℝ (P.oneNormalizedColumn E t l) (oneFormEigenvector hRic d i)) t := by
  have h := (P.one_eigen_evolution E hpair hRic d t ht l i).const_mul ((normalizedChartFactor g).toReal)⁻¹
  simpa only [HeatNormalParametrixData.oneNormalizedColumn, HeatNormalParametrixData.oneNormalizedResidual,
    real_inner_smul_left, mul_sub, mul_left_comm] using h


theorem exists_heatNormalOneEvolution (E : HeatNormalOneExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source) (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ∃ P : HeatNormalParametrixData D,
      (∀ l (i : OneFormEigenIndex hRic d),
        Filter.Tendsto (fun t => inner ℝ (P.oneNormalizedColumn E t l) (oneFormEigenvector hRic d i))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (covariantFieldFramed g (oneFormEigenSection hRic d i).val e ![l]))) ∧
      ∀ t > (0 : ℝ), ∀ l (i : OneFormEigenIndex hRic d),
        HasDerivAt (fun s => inner ℝ (P.oneNormalizedColumn E s l) (oneFormEigenvector hRic d i))
          (inner ℝ (P.oneNormalizedResidual E t l) (oneFormEigenvector hRic d i) -
            oneFormHeatRate hRic d i * inner ℝ (P.oneNormalizedColumn E t l) (oneFormEigenvector hRic d i)) t := by
  obtain ⟨P, hP⟩ := exists_heatNormalOneWeakData E he hRic
  refine ⟨P, ?_, ?_⟩
  · intro l i
    rw [← oneFormEigenSection_L2 hRic d i]
    exact P.one_normalized_initial E he (oneFormEigenSection hRic d i) l
  · intro t ht l i
    exact P.one_normalized_eigen_evolution E hP hRic d t ht l i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual signed normal-parametrix Gaussian integral has the
signature curvature density as its limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalMatrixPolynomial (E : HeatNormalBundleExtension D)
    (t : ℝ) (x : FourSpace) : HeatMat6 :=
  E.amplitude 0 x + t • E.amplitude 1 x + t ^ 2 • E.amplitude 2 x + t ^ 3 • E.amplitude 3 x

theorem heatNormalMatrixPolynomial_component (E : HeatNormalBundleExtension D)
    (t : ℝ) (x : FourSpace) (k l : Fin 6) :
    heatNormalMatrixPolynomial E t x k l =
      fourHeatPolynomial (fun m y => E.amplitude m y k l) t x := by
  simp only [heatNormalMatrixPolynomial, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, fourHeatPolynomial]
  norm_num

theorem heatNormalMatrixPolynomial_signed (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) :
    frameExponentialJacobian g o e x * χ x ^ 2 *
        heatSignedGram (heatNormalMatrixPolynomial E t x) (heatNormalMatrixPolynomial E t x) =
      2 * t * E.signedFirst χ x + t ^ 2 * E.signedTail χ t x := by
  rw [heatNormalMatrixPolynomial, E.amplitude_zero, heatSignedGram_polynomial]
  unfold HeatNormalBundleExtension.signedFirst HeatNormalBundleExtension.signedTail
  ring

theorem HeatNormalBundleExtension.signed_reduced_gaussian_limit
    {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ) (hχ0 : χ 0 = 1)
    (hRic : RicciThree g) :
    Tendsto (fun t : ℝ => ∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
      (2 * t * E.signedFirst χ x + t ^ 2 * E.signedTail χ t x))
      (𝓝[>] 0) (𝓝 (curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩))) := by
  have hχ2 : ContDiffAt ℝ 2 χ 0 := (hχ.of_le (by norm_num)).contDiffAt
  have he := mem_chart_source FourSpace c
  obtain ⟨C, hC⟩ := (E.signedFirst_compact χ hc).exists_bound_of_continuous
    (E.signedFirst_continuous χ hχ.continuous)
  obtain ⟨B, _, hB⟩ := E.signedTail_bound χ hχ.continuous hc
  have h := fourHeat_signed_gaussian_limit (E.signedFirst χ)
    (E.signedFirst_continuous χ hχ.continuous) (E.signedFirst_regular χ hχ2)
    (E.signedFirst_zero χ he) (E.signedFirst_fderiv_zero χ hχ2 he) C hC
    (E.signedTail χ) (E.signedTail_continuous χ hχ.continuous) B 1 zero_lt_one hB
  have hval : (1 / (64 * Real.pi ^ 2)) *
      ((∑ i, fderiv ℝ (fderiv ℝ (E.signedFirst χ)) 0 (coordinateVector i) (coordinateVector i)) +
        E.signedTail χ 0 0) = curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩) := by
    rw [E.signedFirst_hessian_trace χ hχ2 hχ0, E.signedTail_zero χ hχ0,
      E.first_amplitude_signed_gram he, ← E.second_amplitude_signature_density hRic]
    have ha := E.second_amplitude_signature_polynomial
    field_simp
    linarith only [ha]
  rwa [hval] at h

theorem HeatNormalBundleExtension.signed_gaussian_limit
    {f : OrthonormalFrame g c} {D : HeatNormalFrameData g o c ⟨c, f⟩}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ) (hχ0 : χ 0 = 1)
    (hRic : RicciThree g) :
    Tendsto (fun t : ℝ => ∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o ⟨c, f⟩ x * χ x ^ 2 *
        heatSignedGram (heatNormalMatrixPolynomial E t x) (heatNormalMatrixPolynomial E t x)))
      (𝓝[>] 0) (𝓝 (curvatureSignatureDensity (twoFormMetricCurvatureTensor g ⟨c, f⟩))) := by
  simpa only [heatNormalMatrixPolynomial_signed] using
    E.signed_reduced_gaussian_limit χ hχ hc hχ0 hRic

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal parametrix solves the weak Hodge evolution equation
with its constructed, small L2 residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.operator_pairing
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (t : ℝ) (l : Fin 6)
    (hf : P.column E t l ∈ twoFormHodgeDomain hRic)
    (hgen : twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (v : smoothTwoForms o) :
    inner ℝ (P.operatorColumn E t l) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) =
      inner ℝ (P.column E t l)
        (smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)) := by
  have h := twoFormHodgeGenerator_symmetric hRic ⟨P.column E t l, hf⟩
    ⟨smoothTwoFormToL2 (v : SmoothL2TwoForm o), smoothTwoForm_mem_hodgeDomain hRic v⟩
  rw [hgen, twoFormHodgeGenerator_smooth] at h
  exact h

theorem HeatNormalParametrixData.weak_evolution
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (hRic : RicciThree g)
    (t : ℝ) (ht : 0 < t) (l : Fin 6)
    (hf : P.column E t l ∈ twoFormHodgeDomain hRic)
    (hgen : twoFormHodgeGenerator hRic ⟨P.column E t l, hf⟩ = P.operatorColumn E t l)
    (v : smoothTwoForms o) :
    HasDerivAt (fun s => inner ℝ (P.column E s l) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)))
      (inner ℝ (P.residual E t l) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) -
        inner ℝ (P.column E t l)
          (smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o))) t := by
  have hd := heatNormalGlobalParametrixColumn_weak_deriv E P.chart P.exponential
    P.in_chart P.point_regular P.inside_radius P.cutoff
    (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact P.cutoff_support t ht l
    (v : SmoothL2TwoForm o)
  have hp := P.operator_pairing E hRic t l hf hgen v
  have hr : inner ℝ (P.residual E t l) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) -
      inner ℝ (P.column E t l)
        (smoothTwoFormToL2 (smoothHodgeLaplacian hRic v : SmoothL2TwoForm o)) =
      inner ℝ (P.timeColumn E t l) (smoothTwoFormToL2 (v : SmoothL2TwoForm o)) := by
    rw [P.residual_eq E t l, inner_add_left, hp]
    ring
  rw [hr]
  exact hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact normal-coordinate L2 pairing and the sharp order of growth
of the actual scalar parametrix column. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance scalarGaussian_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

theorem HeatScalarChartData.column_norm_sq_integral (P : HeatScalarChartData D) (t : ℝ) :
    ‖P.column t‖ ^ 2 = (normalizedChartFactor g).toReal *
      ∫ x, frameExponentialJacobian g o e x * (P.extension.scalarCutoff P.cutoff t x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have h := P.column_pairing t (⟨P.function t, (P.function_regular t).continuous⟩ : C(M, ℝ))
  change inner ℝ (P.column t) (P.column t) = _ at h
  rw [h]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ P.chart.source
    · have hf := heatNormalScalarLift_source P.chart (P.extension.scalarCutoff P.cutoff t) hx
      change P.extension.scalarCutoff P.cutoff t x *
        (frameExponentialJacobian g o e x * P.function t (P.chart x)) = _
      change P.function t (P.chart x) = P.extension.scalarCutoff P.cutoff t x at hf
      rw [hf]
      ring
    · have hz : P.extension.scalarCutoff P.cutoff t x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hs => hx
          (P.cutoff_support (P.extension.scalarCutoff_support P.cutoff t hs)))
      change P.extension.scalarCutoff P.cutoff t x *
        (frameExponentialJacobian g o e x * P.function t (P.chart x)) =
        frameExponentialJacobian g o e x * (P.extension.scalarCutoff P.cutoff t x) ^ 2
      rw [hz]
      ring

def HeatScalarChartData.polynomial (P : HeatScalarChartData D) (t : ℝ) (x : FourSpace) : ℝ :=
  P.cutoff x * fourHeatPolynomial (fun m => P.extension.scalarAmplitude m) t x

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatScalarChartData.cutoff_gaussian (P : HeatScalarChartData D) (t : ℝ) (x : FourSpace) :
    P.extension.scalarCutoff P.cutoff t x = fourHeatGaussian t x * P.polynomial t x := by
  unfold HeatNormalExtension.scalarCutoff HeatNormalExtension.scalarParametrix polynomial
  ring

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatScalarChartData.polynomial_weight_bound (P : HeatScalarChartData D) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2 ≤ B := by
  let W := fun z : ℝ × FourSpace => frameExponentialJacobian g o e z.2 *
    (P.polynomial z.1 z.2) ^ 2
  have hP : Continuous (fun z : ℝ × FourSpace => P.polynomial z.1 z.2) :=
    (P.cutoff_regular.continuous.comp continuous_snd).mul
      (fourHeatPolynomial_joint_continuous _
        (fun m => (P.extension.scalarAmplitude_regular m (by omega)).continuous))
  have hW : Continuous W :=
    ((frameExponentialJacobian_continuous g o e).comp continuous_snd).mul (hP.pow 2)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod P.cutoff_compact).bddAbove_image hW.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ tsupport P.cutoff
  · exact (hB ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left _ _)
  · have hz : P.polynomial t x = 0 := by
      unfold polynomial
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    rw [hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact le_max_right _ _

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatScalarChartData.square_integral_bound (P : HeatScalarChartData D) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1,
      (∫ x, frameExponentialJacobian g o e x *
        (P.extension.scalarCutoff P.cutoff t x) ^ 2) ≤ C / t ^ 2 := by
  obtain ⟨B, hB, hbound⟩ := P.polynomial_weight_bound
  refine ⟨B / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro t ht
  have hp (x : FourSpace) : frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [P.cutoff_gaussian, mul_pow]
    calc
      _ = (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound t ⟨ht.1.le, ht.2⟩ x) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hc : Continuous (fun x => frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((P.extension.scalarCutoff_regular P.cutoff P.cutoff_regular t).continuous.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2) :=
    hi.mono' hc.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hp x)
  calc
    _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hp
    _ = _ := by rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]; ring

theorem HeatScalarChartData.column_growth (P : HeatScalarChartData D) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.column t‖ ≤ C / t := by
  obtain ⟨B, hB, hbound⟩ := P.square_integral_bound
  let K := (normalizedChartFactor g).toReal * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro t ht
  have hn : ‖P.column t‖ ^ 2 ≤ K / t ^ 2 := by
    rw [P.column_norm_sq_integral]
    exact (mul_le_mul_of_nonneg_left (hbound t ht) (by positivity)).trans_eq (by dsimp [K]; ring)
  have hs : (‖P.column t‖ * t) ^ 2 ≤ K := by
    calc
      _ = ‖P.column t‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (K / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn (sq_nonneg t)
      _ = K := by field_simp [ht.1.ne']
  apply (le_div_iff₀ ht.1).mpr
  nlinarith [sq_nonneg K, norm_nonneg (P.column t)]

theorem HeatScalarChartData.normalizedColumn_growth (P : HeatScalarChartData D) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.normalizedColumn t‖ ≤ C / t := by
  obtain ⟨C, hC, hc⟩ := P.column_growth
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * C, by positivity, ?_⟩
  intro t ht
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.column t‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hc t ht) (norm_nonneg _)).trans_eq (by ring)

theorem HeatScalarChartData.normalizedColumn_gaussian_integral
    (P : HeatScalarChartData D) (t : ℝ) :
    ‖P.normalizedColumn t‖ ^ 2 = ((normalizedChartFactor g).toReal)⁻¹ *
      ∫ x, fourHeatGaussian t x ^ 2 *
        (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2) := by
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.column t‖ ^ 2 = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, P.column_norm_sq_integral]
  have he : (∫ x, frameExponentialJacobian g o e x *
      (P.extension.scalarCutoff P.cutoff t x) ^ 2) =
      ∫ x, fourHeatGaussian t x ^ 2 *
        (frameExponentialJacobian g o e x * (P.polynomial t x) ^ 2) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change frameExponentialJacobian g o e x * (P.extension.scalarCutoff P.cutoff t x) ^ 2 = _
      rw [P.cutoff_gaussian]
      ring
  rw [he]
  field_simp [(normalizedChartFactor_toReal_pos g).ne']

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual time derivative of the global scalar parametrix is a
compact C4 function, represented in the same scalar L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatScalarChartData.timeAmplitude (P : HeatScalarChartData D) (t : ℝ) (x : FourSpace) : ℝ :=
  P.cutoff x * fourHeatGaussianPolynomialTime (fun m => P.extension.scalarAmplitude m) t x

theorem HeatScalarChartData.timeAmplitude_regular (P : HeatScalarChartData D) (t : ℝ) :
    ContDiff ℝ 4 (P.timeAmplitude t) := by
  have hu (m : Fin 4) := P.extension.scalarAmplitude_regular m (by omega)
  have hQ : ContDiff ℝ 4 (fun x => fourHeatPolynomialTime
      (fun m => P.extension.scalarAmplitude m) t x) :=
    ((hu 1).add ((contDiff_const (c := 2 * t)).mul (hu 2))).add
      ((contDiff_const (c := 3 * t ^ 2)).mul (hu 3))
  have hF : ContDiff ℝ 4 (fourHeatGaussianTimeFactor t) :=
    ((contDiff_norm_sq ℝ).div_const (4 * t ^ 2)).sub contDiff_const
  have hG : ContDiff ℝ 4 (fourHeatGaussian t) := (fourHeatGaussian_smooth t).of_le (by norm_num)
  have hP : ContDiff ℝ 4 (fourHeatPolynomial (fun m => P.extension.scalarAmplitude m) t) :=
    (((hu 0).add (contDiff_const.mul (hu 1))).add
      (contDiff_const.mul (hu 2))).add (contDiff_const.mul (hu 3))
  exact P.cutoff_regular.mul (((hF.mul hG).mul hP).add (hG.mul hQ))

theorem HeatScalarChartData.timeAmplitude_support (P : HeatScalarChartData D) (t : ℝ) :
    tsupport (P.timeAmplitude t) ⊆ tsupport P.cutoff := tsupport_mul_subset_left

theorem HeatScalarChartData.timeAmplitude_eq (P : HeatScalarChartData D)
    (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    P.timeAmplitude t x = deriv (fun s => P.extension.scalarCutoff P.cutoff s x) t :=
  ((fourHeatGaussianPolynomial_hasDerivAt (fun m => P.extension.scalarAmplitude m)
    t ht x).const_mul (P.cutoff x)).deriv.symm

def HeatScalarChartData.timeFunction (P : HeatScalarChartData D) (t : ℝ) : M → ℝ :=
  heatNormalScalarLift P.chart (P.timeAmplitude t)

theorem HeatScalarChartData.timeFunction_regular (P : HeatScalarChartData D) (t : ℝ) :
    ContMDiff I4 𝓘(ℝ, ℝ) 4 (P.timeFunction t) :=
  heatNormalScalarLift_regular P.chart _ P.inverse_regular (P.timeAmplitude_regular t)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (P.timeAmplitude_support t))
    ((P.timeAmplitude_support t).trans P.cutoff_support)

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarTime_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def HeatScalarChartData.timeColumn (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) :=
  scalarFiniteValueL2 g (P.timeFunction t) (P.timeFunction_regular t)

theorem HeatScalarChartData.timeColumn_pairing (P : HeatScalarChartData D)
    (t : ℝ) (f : C(M, ℝ)) :
    inner ℝ (P.timeColumn t) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f) =
      (normalizedChartFactor g).toReal * ∫ x, P.timeAmplitude t x *
        (frameExponentialJacobian g o e x * f (P.chart x)) := by
  rw [L2.inner_def]
  calc
    _ = ∫ y, P.timeFunction t y * f y ∂normalizedVolume g := by
      apply integral_congr_ae
      filter_upwards [scalarFiniteValueL2_coe g (P.timeFunction t) (P.timeFunction_regular t),
        ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g) f] with y hy hf
      simp only [RCLike.inner_apply', conj_trivial, HeatScalarChartData.timeColumn, hy, hf]
    _ = ∫ y, heatNormalScalarLift P.chart (fun x => P.timeAmplitude t x * f (P.chart x)) y
        ∂normalizedVolume g := by
      apply integral_congr_ae
      exact Eventually.of_forall (heatNormalScalarLift_mul P.chart _ f)
    _ = _ := by
      rw [heatNormalScalarLift_integral D P.chart P.exponential P.in_chart
        (P.point_regular.of_le (by norm_num)) P.inside_radius]
      · congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      · exact tsupport_mul_subset_left.trans ((P.timeAmplitude_support t).trans P.cutoff_support)

theorem HeatScalarChartData.column_weak_deriv (P : HeatScalarChartData D)
    (t : ℝ) (ht : 0 < t) (f : C(M, ℝ)) :
    HasDerivAt (fun s => inner ℝ (P.column s) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f))
      (inner ℝ (P.timeColumn t) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f)) t := by
  let F := fun x => frameExponentialJacobian g o e x * f (P.chart x)
  have hF : ContinuousOn F P.chart.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      (f.continuous.comp_continuousOn P.chart.continuousOn)
  have hχF := heat_continuous_mul_of_tsupport_subset P.cutoff_regular.continuous
    P.chart.open_source hF P.cutoff_support
  have h := (P.extension.scalarCutoff_pairing_deriv P.cutoff F hχF P.cutoff_compact
    t ht).const_mul (normalizedChartFactor g).toReal
  have hval : inner ℝ (P.timeColumn t) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f) =
      (normalizedChartFactor g).toReal *
        ∫ x, deriv (fun s => P.extension.scalarCutoff P.cutoff s x) t * F x := by
    rw [P.timeColumn_pairing]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => congrArg (· * F x) (P.timeAmplitude_eq t ht x)
  rw [← hval] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun s => P.column_pairing s f)

end
end PositiveEinsteinFour.Geometry
end

end OAI

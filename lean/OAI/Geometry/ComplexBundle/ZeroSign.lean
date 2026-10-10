import OAI.Geometry.ComplexBundle.HyperplaneProduct
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Basic.Sign.Basic
import Mathlib.LinearAlgebra.Orientation
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

namespace OAI

noncomputable section

/-! Real signs of complex derivatives and signed regular-zero coordinates. -/

section
open Asymptotics Topology
namespace Kaplansky

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- At a zero of a differentiable section, a merely continuous linear
change of fiber coordinates has derivative `T x ∘ D`. No derivative of
the transition family is needed. This applies to continuous bundle charts. -/
theorem hasFDerivAt_continuous_zero_coordinates
    {s : E → F} {D : E →L[ℝ] F} {x : E}
    (hs : HasFDerivAt s D x) (hz : s x = 0)
    {T : E → F →L[ℝ] G} (hT : ContinuousAt T x) :
    HasFDerivAt (fun y => T y (s y)) ((T x).comp D) x := by
  have ht : (fun y => T y - T x) =o[𝓝 x] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (by
      simpa only [sub_self] using hT.tendsto.sub (tendsto_const_nhds (x := T x)))
  have hsO : s =O[𝓝 x] (fun y => y - x) := by
    simpa only [hz, sub_zero] using hs.isBigO_sub
  have hp : (fun y => ‖T y - T x‖ * ‖s y‖) =o[𝓝 x] (fun y => y - x) := by
    apply Asymptotics.IsLittleO.of_norm_right
    simpa only [one_mul] using ht.norm_left.mul_isBigO hsO.norm_norm
  have herror : (fun y => (T y - T x) (s y)) =o[𝓝 x] (fun y => y - x) :=
    (isBoundedBilinearMap_apply.isBigO_comp).trans_isLittleO hp
  have hfixed := ((T x).hasFDerivAt.comp x hs).isLittleO
  apply HasFDerivAt.of_isLittleO
  apply (herror.add hfixed).congr_left
  intro y
  simp only [sub_apply, Function.comp_apply, hz, map_zero,
    sub_zero, ContinuousLinearMap.comp_apply]
  abel

end Kaplansky

end

namespace Kaplansky

section

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E]
  [IsScalarTower ℝ ℂ E]

/-- The real determinant of a complex endomorphism is the squared modulus
of its complex determinant. This includes complex dimension zero. -/
theorem real_det_complex (f : E →ₗ[ℂ] E) :
    (f.restrictScalars ℝ).det = Complex.normSq f.det := by
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- Complex linear coordinate changes preserve real orientation. -/
theorem real_det_complex_equiv_pos (e : E ≃ₗ[ℂ] E) :
    0 < (e.toLinearMap.restrictScalars ℝ).det := by
  rw [real_det_complex, Complex.normSq_pos]
  simpa only [LinearEquiv.coe_det] using Units.ne_zero (LinearEquiv.det e)

variable [FiniteDimensional ℂ E]

/-- Every orientation of the correct dimension is fixed by a complex
automorphism viewed over the reals. -/
theorem complex_equiv_preserves_orientation {ι : Type*} [Fintype ι]
    (o : Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E)
    (e : E ≃ₗ[ℂ] E) :
    Orientation.map ι (e.restrictScalars ℝ) o = o := by
  have : FiniteDimensional ℝ ℂ := Module.Finite.of_basis Complex.basisOneI
  have : FiniteDimensional ℝ E := Module.Finite.trans ℂ E
  apply (Orientation.map_eq_iff_det_pos o (e.restrictScalars ℝ) hι).mpr
  exact real_det_complex_equiv_pos e

end

section

variable {E F G : Type*}
  [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]
  [AddCommGroup G] [Module ℂ G] [Module ℝ G] [IsScalarTower ℝ ℂ G]

/-- Sign of a real derivative between complex vector spaces of equal
dimension. A complex identification is used to take the determinant;
`complexDerivativeSign_independent` proves that choice immaterial.
This is a local linear sign, not an Euler class or a global degree. -/
def complexDerivativeSign (e : E ≃ₗ[ℂ] F) (D : E →ₗ[ℝ] F) : SignType :=
  SignType.sign (((e.symm.restrictScalars ℝ).toLinearMap).comp D).det

theorem complexDerivativeSign_independent (e e' : E ≃ₗ[ℂ] F) (D : E →ₗ[ℝ] F) :
    complexDerivativeSign e' D = complexDerivativeSign e D := by
  let a : E ≃ₗ[ℂ] E := e.trans e'.symm
  have h : (e'.symm.restrictScalars ℝ).toLinearMap.comp D =
      (a.toLinearMap.restrictScalars ℝ).comp
        ((e.symm.restrictScalars ℝ).toLinearMap.comp D) := by
    ext x
    simp [a]
  unfold complexDerivativeSign
  rw [h, LinearMap.det_comp, sign_mul,
    sign_pos (real_det_complex_equiv_pos a), one_mul]

/-- An invertible complex derivative contributes positive sign. -/
theorem complexDerivativeSign_complex_equiv (e d : E ≃ₗ[ℂ] F) :
    complexDerivativeSign e (d.toLinearMap.restrictScalars ℝ) = 1 := by
  apply sign_pos
  exact real_det_complex_equiv_pos (d.trans e.symm)

/-- Changing complex coordinates in the codomain does not change the sign,
even when the derivative itself is only real linear. -/
theorem complexDerivativeSign_post (e : E ≃ₗ[ℂ] F) (b : F ≃ₗ[ℂ] G)
    (D : E →ₗ[ℝ] F) :
    complexDerivativeSign (e.trans b) ((b.toLinearMap.restrictScalars ℝ).comp D) =
      complexDerivativeSign e D := by
  unfold complexDerivativeSign
  congr 2
  ext x
  simp

/-- Changing complex coordinates in the domain conjugates the endomorphism
used for the real determinant, and consequently preserves its sign. -/
theorem complexDerivativeSign_pre (e : E ≃ₗ[ℂ] F) (a : G ≃ₗ[ℂ] E)
    (D : E →ₗ[ℝ] F) :
    complexDerivativeSign (a.trans e) (D.comp (a.toLinearMap.restrictScalars ℝ)) =
      complexDerivativeSign e D := by
  unfold complexDerivativeSign
  have h : ((a.trans e).symm.restrictScalars ℝ).toLinearMap.comp
      (D.comp (a.toLinearMap.restrictScalars ℝ)) =
      (a.symm.restrictScalars ℝ).toLinearMap.comp
        (((e.symm.restrictScalars ℝ).toLinearMap.comp D).comp
          (a.restrictScalars ℝ).toLinearMap) := by
    ext x
    rfl
  rw [h]
  exact congrArg SignType.sign (LinearMap.det_conj
    ((e.symm.restrictScalars ℝ).toLinearMap.comp D) (a.symm.restrictScalars ℝ))

end

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
  [IsScalarTower ℝ ℂ G]

/-- The real derivative sign at a zero is invariant under a continuous
change of complex fiber coordinates. The derivative may be only real linear;
the transition family need not be differentiable. -/
theorem regularZeroSign_continuous_fiber_coordinates
    {s : E → F} {D : E →L[ℝ] F} {x : E}
    (hs : HasFDerivAt s D x) (hz : s x = 0)
    {T : E → F →L[ℝ] G} (hT : ContinuousAt T x)
    (b : F ≃L[ℂ] G) (hb : T x = b.toContinuousLinearMap.restrictScalars ℝ)
    (e : E ≃ₗ[ℂ] F) (e' : E ≃ₗ[ℂ] G) :
    complexDerivativeSign e' (fderiv ℝ (fun y => T y (s y)) x).toLinearMap =
      complexDerivativeSign e D.toLinearMap := by
  rw [(hasFDerivAt_continuous_zero_coordinates hs hz hT).fderiv, hb]
  rw [complexDerivativeSign_independent (e.trans b.toLinearEquiv) e']
  exact complexDerivativeSign_post e b.toLinearEquiv D.toLinearMap

/-- Invariance under a differentiable change of base coordinates whose
derivative at the zero is a complex linear equivalence. -/
theorem regularZeroSign_base_coordinates [FiniteDimensional ℂ G]
    {s : E → F} {D : E →L[ℝ] F} {g : G → E} {x : G}
    (hs : HasFDerivAt s D (g x)) (a : G ≃L[ℂ] E)
    (hg : HasFDerivAt g (a.toContinuousLinearMap.restrictScalars ℝ) x)
    (e : E ≃ₗ[ℂ] F) (e' : G ≃ₗ[ℂ] F) :
    complexDerivativeSign e' (fderiv ℝ (s ∘ g) x).toLinearMap =
      complexDerivativeSign e D.toLinearMap := by
  rw [(hs.comp x hg).fderiv]
  rw [complexDerivativeSign_independent (a.toLinearEquiv.trans e) e']
  exact complexDerivativeSign_pre e a.toLinearEquiv D.toLinearMap

/-- A complex regular zero retains positive local sign after an arbitrary
continuous change of complex fiber coordinates. -/
theorem complex_regular_zero_sign_in_continuous_coordinates
    {s : E → F} {x : E} (d : E ≃L[ℂ] F)
    (hs : HasFDerivAt s (d.toContinuousLinearMap.restrictScalars ℝ) x)
    (hz : s x = 0) {T : E → F →L[ℝ] G} (hT : ContinuousAt T x)
    (b : F ≃L[ℂ] G) (hb : T x = b.toContinuousLinearMap.restrictScalars ℝ)
    (e' : E ≃ₗ[ℂ] G) :
    complexDerivativeSign e' (fderiv ℝ (fun y => T y (s y)) x).toLinearMap = 1 := by
  rw [regularZeroSign_continuous_fiber_coordinates hs hz hT b hb d.toLinearEquiv e']
  exact complexDerivativeSign_complex_equiv d.toLinearEquiv d.toLinearEquiv

end Kaplansky

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {ι : Type} [Fintype ι] (K : ι → ℕ)

/-- The genuine product graph chart used for the canonical zero. -/
def canonicalProductGraphChart :
    OpenPartialHomeomorph (ProjectiveProduct K) (ProjectiveProductModel K) :=
  OpenPartialHomeomorph.pi (fun i => grassmannChart (standardLineGraphFrame (K i)))

theorem canonicalProductGraphChart_symm (A : ProjectiveProductModel K) :
    (canonicalProductGraphChart K).symm A = canonicalProductGraphPoint K A := rfl

theorem canonicalProduct_zero_in_chart :
    firstCoordinateProduct K ∈ (canonicalProductGraphChart K).source := by
  rw [← canonicalProductGraphPoint_zero K]
  intro i hi
  exact graphPlane_inChart (standardLineGraphFrame (K i)) 0

theorem canonicalProductGraphChart_zero :
    canonicalProductGraphChart K (firstCoordinateProduct K) = 0 := by
  rw [← canonicalProductGraphPoint_zero K]
  funext i
  exact slopeCoordinate_point (standardLineGraphFrame (K i)) 0

theorem canonicalProductSectionCoordinates_hasFDerivAt (A : ProjectiveProductModel K) :
    HasFDerivAt (canonicalProductSectionCoordinates K)
      ((productSlopeEvaluationEquiv K).toContinuousLinearMap.restrictScalars ℝ) A := by
  have he : canonicalProductSectionCoordinates K = productSlopeEvaluationEquiv K :=
    funext (canonicalProductSectionCoordinates_eq K)
  rw [he]
  exact ((productSlopeEvaluationEquiv K).toContinuousLinearMap.hasFDerivAt).restrictScalars ℝ

def canonicalProductLocalSign (P : ProjectiveProduct K) : SignType :=
  complexDerivativeSign (productSlopeEvaluationEquiv K).toLinearEquiv
    (fderiv ℝ (canonicalProductSectionCoordinates K) (canonicalProductGraphChart K P)).toLinearMap

theorem canonicalProductLocalSign_eq_one (P : ProjectiveProduct K) :
    canonicalProductLocalSign K P = 1 := by
  unfold canonicalProductLocalSign
  rw [(canonicalProductSectionCoordinates_hasFDerivAt K _).fderiv]
  exact complexDerivativeSign_complex_equiv (productSlopeEvaluationEquiv K).toLinearEquiv
    (productSlopeEvaluationEquiv K).toLinearEquiv

/-- The finite set here is proved to be the zero set of the actual global
section, and to lie inside the chart where the local sign is computed. -/
def canonicalProductZeroSet : Finset (ProjectiveProduct K) :=
  {firstCoordinateProduct K}

theorem mem_canonicalProductZeroSet_iff (P : ProjectiveProduct K) :
    P ∈ canonicalProductZeroSet K ↔ hyperplaneProductSection K P = 0 := by
  classical
  simp only [canonicalProductZeroSet, Finset.mem_singleton,
    hyperplaneProductSection_eq_zero_iff]

theorem canonicalProductZeroSet_in_chart (P : ProjectiveProduct K)
    (hP : P ∈ canonicalProductZeroSet K) :
    P ∈ (canonicalProductGraphChart K).source := by
  have h := (hyperplaneProductSection_eq_zero_iff K P).mp
    ((mem_canonicalProductZeroSet_iff K P).mp hP)
  simpa only [h] using canonicalProduct_zero_in_chart K

/-- The signed zero count of this specific section is one. Invariance under
changing the section, and identification with an Euler/Chern invariant,
remain separate obligations; neither is asserted by this definition. -/
def canonicalProductSignedZeroCount : ℤ :=
  ∑ P ∈ canonicalProductZeroSet K, (canonicalProductLocalSign K P : ℤ)

theorem canonicalProductSignedZeroCount_eq_one :
    canonicalProductSignedZeroCount K = 1 := by
  classical
  simp [canonicalProductSignedZeroCount, canonicalProductZeroSet,
    canonicalProductLocalSign_eq_one]

end Kaplansky

end

end OAI

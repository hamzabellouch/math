import OAI.Analysis.KadisonSimilarity.Representation.VectorL2Multiplication
import OAI.Analysis.KadisonSimilarity.Representation.L2HilbertSum
import OAI.Analysis.KadisonSimilarity.Representation.SpectralIntertwining
import OAI.Analysis.KadisonSimilarity.Derivation.CyclicCommutativeModel

namespace OAI

/-! Scalar multiplication is preserved by coordinate inclusions and the
cyclic spectral maps. These are the intertwining identities for the common
central Hilbert model. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory
open scoped NNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem l2MapIsometry_scalar_intertwines (J : ℂ →ₗᵢ[ℂ] H) (f : C(X, ℂ)) (ξ : Lp ℂ 2 μ) :
    l2MapIsometry μ J (continuousL2Mul μ f ξ) =
      VectorL2.continuousL2Mul μ f (l2MapIsometry μ J ξ) := by
  apply Lp.ext
  filter_upwards [l2MapIsometry_ae μ J (continuousL2Mul μ f ξ),
    continuousL2Mul_ae μ f ξ,
    VectorL2.continuousL2Mul_ae μ f (l2MapIsometry μ J ξ),
    l2MapIsometry_ae μ J ξ] with x hJ hm hV hξ
  rw [hJ, hm, hV, hξ]
  change J (f x • ξ x) = f x • J (ξ x)
  exact J.map_smul (f x) (ξ x)

/-- Compose a scalar intertwiner with a fixed Hilbert coordinate and retain
its intertwining identity without unfolding the scalar construction. -/
def coordinateIntertwinerData (ν : Measure X) (V : ℂ →ₗᵢ[ℂ] H)
    (d : {J : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ //
      ∀ (f : C(X, ℂ)) (ξ : Lp ℂ 2 ν),
        J (continuousL2Mul ν f ξ) = continuousL2Mul μ f (J ξ)}) :
    {J : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp H 2 μ //
      ∀ (f : C(X, ℂ)) (ξ : Lp ℂ 2 ν),
        J (continuousL2Mul ν f ξ) = VectorL2.continuousL2Mul μ f (J ξ)} := by
  refine ⟨(l2MapIsometry μ V).comp d.val, ?_⟩
  intro f ξ
  change l2MapIsometry μ V (d.val (continuousL2Mul ν f ξ)) = _
  rw [d.property f ξ]
  exact l2MapIsometry_scalar_intertwines μ V f _

section Density
variable [T2Space X] (ν : Measure X) [IsFiniteMeasure ν] [ν.WeaklyRegular]
  (u : X → ℝ≥0) (hu : Measurable u) (hL2 : MemLp (fun x => (u x : ℂ)) 2 μ)

theorem spectralDensityIsometryOfEq_intertwines (heq : squaredDensityMeasure μ u = ν)
    (f : C(X, ℂ)) (ξ : Lp ℂ 2 ν) :
    spectralDensityIsometryOfEq μ u hu hL2 ν heq (continuousL2Mul ν f ξ) =
      continuousL2Mul μ f (spectralDensityIsometryOfEq μ u hu hL2 ν heq ξ) := by
  subst ν
  exact spectralDensityIsometry_intertwines μ u hu hL2 f ξ

/-- Retain the intertwining property with the chosen measure-change isometry,
so later concrete instantiations do not unfold its extension construction. -/
def spectralDensityIntertwinerData (heq : squaredDensityMeasure μ u = ν) :
    {J : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 μ //
      ∀ (f : C(X, ℂ)) (ξ : Lp ℂ 2 ν),
        J (continuousL2Mul ν f ξ) = continuousL2Mul μ f (J ξ)} :=
  ⟨spectralDensityIsometryOfEq μ u hu hL2 ν heq,
    spectralDensityIsometryOfEq_intertwines μ ν u hu hL2 heq⟩

end Density

section Cyclic
variable [T2Space X] [CompleteSpace H]
  {A : Type*} [CommCStarAlgebra A]

local instance scalarIntertwiningMeasurable : MeasurableSpace (WeakDual.characterSpace ℂ A) :=
  borel (WeakDual.characterSpace ℂ A)
local instance scalarIntertwiningBorel : BorelSpace (WeakDual.characterSpace ℂ A) := ⟨rfl⟩

theorem commutativeCyclicIsometry_intertwines
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) (a : A)
    (ξ : Lp ℂ 2 (commutativeVectorMeasure π v)) :
    commutativeCyclicIsometry π v
      (continuousL2Mul (commutativeVectorMeasure π v) (gelfandStarTransform A a) ξ) =
        π a (commutativeCyclicIsometry π v ξ) := by
  change Lp ℂ 2 (VectorSpectralMeasure.measure (commutativeSpectralCalculus π) v) at ξ
  change VectorSpectralMeasure.cyclicMap (commutativeSpectralCalculus π) v
    (continuousL2Mul (VectorSpectralMeasure.measure (commutativeSpectralCalculus π) v)
      (gelfandStarTransform A a) ξ) =
        π a (VectorSpectralMeasure.cyclicMap (commutativeSpectralCalculus π) v ξ)
  rw [VectorSpectralMeasure.cyclicMap_intertwines]
  change π ((gelfandStarTransform A).symm (gelfandStarTransform A a)) _ = π a _
  rw [StarAlgEquiv.symm_apply_apply]

end Cyclic
end KadisonSimilarity

end

end OAI

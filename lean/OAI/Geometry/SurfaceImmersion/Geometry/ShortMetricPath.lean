import OAI.Geometry.SurfaceImmersion.Geometry.PositiveTensorMetric

namespace OAI

/-! The positive metric remainder and the actual smooth metric path used
by the finite primitive preparation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance pathFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance pathFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance pathDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance pathDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance pathSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance pathSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M) (g : SmoothMetric M) {F : M → Space}
  (hF : ContMDiff planeModel spaceModel ∞ F)
  (hshort : ∀ p v, inducedForm F p v v ≤ (1/2 : ℝ)*g.inner p v v)

def shortRemainderMetric : SmoothMetric M :=
  positiveTensorMetric (g.inner-inducedTensor F)
    (g.contMDiff.sub_section (A.inducedTensor_smooth hF))
    (by
      intro p v w
      change g.inner p v w-inducedTensor F p v w = g.inner p w v-inducedTensor F p w v
      rw [g.symm,inducedTensor_symmetric])
    (by
      intro p v hv
      change 0 < g.inner p v v-inducedForm F p v v
      have hp := g.pos p v hv
      have hs := hshort p v
      linarith)

lemma shortRemainderMetric_lower (p : M) (v : TangentSpace planeModel p) :
    (1/2 : ℝ)*g.inner p v v ≤ (A.shortRemainderMetric g hF hshort).inner p v v := by
  change (1/2 : ℝ)*g.inner p v v ≤ g.inner p v v-inducedForm F p v v
  linarith [hshort p v]

def shortPathMetric (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (s : ℝ) (hs : 0 ≤ s) : SmoothMetric M :=
  positiveTensorMetric ((A.immersionMetric hF hI).inner+s • (A.shortRemainderMetric g hF hshort).inner)
    ((A.immersionMetric hF hI).contMDiff.add_section
      (A.shortRemainderMetric g hF hshort).contMDiff.const_smul_section)
    (by
      intro p v w
      change (A.immersionMetric hF hI).inner p v w+s*(A.shortRemainderMetric g hF hshort).inner p v w =
        (A.immersionMetric hF hI).inner p w v+s*(A.shortRemainderMetric g hF hshort).inner p w v
      rw [(A.immersionMetric hF hI).symm,(A.shortRemainderMetric g hF hshort).symm])
    (by
      intro p v hv
      have h₀ := (A.immersionMetric hF hI).pos p v hv
      have h₁ := (A.shortRemainderMetric g hF hshort).pos p v hv
      change 0 < (A.immersionMetric hF hI).inner p v v+s*(A.shortRemainderMetric g hF hshort).inner p v v
      exact add_pos_of_pos_of_nonneg h₀ (mul_nonneg hs h₁.le))

lemma shortPathMetric_apply (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (s : ℝ) (hs : 0 ≤ s) (p : M) (v w : TangentSpace planeModel p) :
    (A.shortPathMetric g hF hshort hI s hs).inner p v w =
      (1-s)*inducedForm F p v w+s*g.inner p v w := by
  change inducedForm F p v w+s*(g.inner p v w-inducedForm F p v w) = _
  ring

lemma shortPathMetric_start (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    (A.shortPathMetric g hF hshort hI 0 le_rfl).inner = inducedTensor F := by
  funext p
  ext v w
  rw [A.shortPathMetric_apply]
  simp only [sub_zero,one_mul,zero_mul,add_zero,inducedTensor_apply]

lemma shortPathMetric_finish (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p)) :
    (A.shortPathMetric g hF hshort hI 1 zero_le_one).inner = g.inner := by
  funext p
  ext v w
  rw [A.shortPathMetric_apply]
  simp

lemma shortPathMetric_lower (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (s : ℝ) (hs : 0 ≤ s) {c : ℝ}
    (hlower : ∀ p v, c*g.inner p v v ≤ inducedForm F p v v)
    (p : M) (v : TangentSpace planeModel p) :
    c*g.inner p v v ≤ (A.shortPathMetric g hF hshort hI s hs).inner p v v := by
  have hm : 0 ≤ (A.shortRemainderMetric g hF hshort).inner p v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((A.shortRemainderMetric g hF hshort).pos p v hv).le
  change c*g.inner p v v ≤ inducedForm F p v v+s*(A.shortRemainderMetric g hF hshort).inner p v v
  exact (hlower p v).trans (le_add_of_nonneg_right (mul_nonneg hs hm))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Algebra.LeftTangentTrivialization
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PullbackInnerProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! # A left-invariant Riemannian metric

An inner product at the identity is transported by the actual differentials
of left translation. Its smoothness is checked in the tangent bundle charts.
-/

noncomputable section
namespace PolycyclicRecognition

open Bundle Bornology Set
open scoped Manifold ContDiff Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]

def leftInvariantInner (e : E ≃L[ℝ] F) (g : G) :
    TangentSpace (𝓘(ℝ, E)) g →L[ℝ] TangentSpace (𝓘(ℝ, E)) g →L[ℝ] ℝ :=
  pullbackInner (E := E) (e.toContinuousLinearMap.comp (leftLogDerivative (E := E) g))

theorem leftInvariantInner_pos (e : E ≃L[ℝ] F) (g : G)
    (v : TangentSpace (𝓘(ℝ, E)) g) (hv : v ≠ 0) :
    0 < leftInvariantInner e g v v :=
  pullbackInner_pos (E := E) ((leftTangentEquiv (E := E) g).trans e) v hv

theorem leftInvariantInner_bounded (e : E ≃L[ℝ] F) (g : G) :
    IsVonNBounded ℝ {v : TangentSpace (𝓘(ℝ, E)) g | leftInvariantInner e g v v < 1} :=
  pullbackInner_bounded (E := E) ((leftTangentEquiv (E := E) g).trans e)

def leftLogCoordinate (g₀ g : G) : E →L[ℝ] E :=
  (leftLogDerivative (E := E) g).comp
    ((trivializationAt E (TangentSpace (𝓘(ℝ, E))) g₀).symmL ℝ g)

theorem contMDiffAt_leftLogCoordinate (g₀ : G) :
    ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, E →L[ℝ] E)) ∞
      (leftLogCoordinate (E := E) g₀) g₀ := by
  have hb : (trivializationAt E (TangentSpace (𝓘(ℝ, E))) (1 : G)).continuousLinearMapAt ℝ 1 =
      ContinuousLinearMap.id ℝ E := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt (by simp), mfderiv_extChartAt_self]
    rfl
  have hs := contMDiffAt_leftLogDerivative (E := E) g₀
  apply hs.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro g
  ext v
  dsimp only [leftLogCoordinate, inTangentCoordinates, ContinuousLinearMap.inCoordinates, id_eq]
  rw [hb]
  rfl

theorem leftInvariantInner_coordinates (e : E ≃L[ℝ] F) (g₀ g : G)
    (hg : g ∈ (trivializationAt E (TangentSpace (𝓘(ℝ, E))) g₀).baseSet) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun g => TangentSpace (𝓘(ℝ, E)) g →L[ℝ] TangentSpace (𝓘(ℝ, E)) g →L[ℝ] ℝ)
      g₀ (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) g (leftInvariantInner e g))).2 =
      pullbackInner (e.toContinuousLinearMap.comp (leftLogCoordinate (E := E) g₀ g)) := by
  have hg' : g ∈ (chartAt E g₀).source := hg
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    leftInvariantInner, pullbackInner, leftLogCoordinate,
    Trivialization.linearMapAt_apply, hg']
  rfl

theorem contMDiff_leftInvariantInner (e : E ≃L[ℝ] F) :
    ContMDiff (𝓘(ℝ, E)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ))) ∞
      (fun g : G => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) g (leftInvariantInner e g)) := by
  intro g₀
  rw [contMDiffAt_section]
  have hco := (contMDiffAt_const (c := e.toContinuousLinearMap)).clm_comp
    (contMDiffAt_leftLogCoordinate (E := E) g₀)
  have hs := contDiff_pullbackInner.contDiffAt.comp_contMDiffAt hco
  apply hs.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace (𝓘(ℝ, E))) g₀).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace (𝓘(ℝ, E))) g₀)] with g hg
  exact leftInvariantInner_coordinates e g₀ g hg

def leftInvariantRiemannianMetric (e : E ≃L[ℝ] F) :
    ContMDiffRiemannianMetric (𝓘(ℝ, E)) ∞ E (TangentSpace (𝓘(ℝ, E)) : G → Type _) where
  inner := leftInvariantInner e
  symm _g _v _w := real_inner_comm _ _
  pos := leftInvariantInner_pos e
  isVonNBounded := leftInvariantInner_bounded e
  contMDiff := contMDiff_leftInvariantInner e

theorem leftInvariantInner_mul (e : E ≃L[ℝ] F) (g h : G) (v w : E) :
    leftInvariantInner e (g * h)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h v)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h w) =
      leftInvariantInner e h v w := by
  have hv := congrArg (fun D : E →L[ℝ] E => D v) (leftLogDerivative_mul (E := E) g h)
  have hw := congrArg (fun D : E →L[ℝ] E => D w) (leftLogDerivative_mul (E := E) g h)
  change inner ℝ
    (e (leftLogDerivative (E := E) (g * h)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h v)))
    (e (leftLogDerivative (E := E) (g * h)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h w))) =
    inner ℝ (e (leftLogDerivative (E := E) h v)) (e (leftLogDerivative (E := E) h w))
  change leftLogDerivative (E := E) (g * h)
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h v) =
      leftLogDerivative (E := E) h v at hv
  change leftLogDerivative (E := E) (g * h)
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (fun k : G => g * k) h w) =
      leftLogDerivative (E := E) h w at hw
  rw [hv, hw]

end PolycyclicRecognition

end

end OAI

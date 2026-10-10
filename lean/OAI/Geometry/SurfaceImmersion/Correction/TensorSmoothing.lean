import OAI.Geometry.SurfaceImmersion.Correction.GlobalBundleSmoothing

namespace OAI

/-! Smoothing on the actual covariant two-tensor bundle of the surface. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle MeasureTheory
open JetPolynomial (Base)

abbrev TensorFiber := Plane →L[ℝ] Plane →L[ℝ] ℝ

local instance tensorModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorModelSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance tensorModelComplete : CompleteSpace TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

abbrev CovariantTwoTensor (p : M) :=
  TangentSpace planeModel p →L[ℝ] TangentSpace planeModel p →L[ℝ] ℝ

local instance tensorDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

local instance tensorDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def tensorTriv (i : A.centers) :
    Trivialization TensorFiber (TotalSpace.proj : TotalSpace TensorFiber
      (CovariantTwoTensor (M := M)) → M) :=
  trivializationAt TensorFiber (CovariantTwoTensor (M := M)) (i : M)

instance tensorTriv_mem (i : A.centers) : MemTrivializationAtlas (A.tensorTriv i) := by
  unfold tensorTriv
  infer_instance

lemma tensorTriv_domain (i : A.centers) :
    (chart (i : M)).source ⊆ (A.tensorTriv i).baseSet := by
  intro x hx
  unfold tensorTriv CovariantTwoTensor TensorFiber
  rw [hom_trivializationAt_baseSet, hom_trivializationAt_baseSet]
  simp only [TangentBundle.trivializationAt_baseSet, mem_inter_iff]
  exact ⟨by simpa only [chart_source] using hx,
    by simpa only [chart_source] using hx, mem_univ x⟩

def tensorSmooth (r : ℕ) (s : ℝ) (u : ∀ p : M, CovariantTwoTensor p) :
    ∀ p : M, CovariantTwoTensor p := A.bundleSmooth (F := TensorFiber) (E := CovariantTwoTensor (M := M)) A.tensorTriv r s u

def TensorWeightedBound (s : ℝ) (m : ℕ) (C : ℝ)
    (u : ∀ p : M, CovariantTwoTensor p) : Prop :=
  A.BundleWeightedBound (F := TensorFiber) (E := CovariantTwoTensor (M := M)) A.tensorTriv s m C u

variable [CompactSpace M]

theorem tensorSmooth_smooth (r : ℕ) {s : ℝ} (hs : 0 < s)
    {u : ∀ p : M, CovariantTwoTensor p}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.tensorSmooth r s u p)) :=
  A.bundleSmooth_smooth (F := TensorFiber) (E := CovariantTwoTensor (M := M)) A.tensorTriv A.tensorTriv_domain r hs hu

theorem tensor_smoothing_bounds (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧
      (∀ (u : ∀ p : M, CovariantTwoTensor p) (s t C : ℝ),
        0 < s → 0 < t → t ≤ 1 → 0 ≤ C →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun p => TotalSpace.mk' TensorFiber p (u p)) → A.TensorWeightedBound t m C u →
        A.TensorWeightedBound t m
          (D * (1 + (1 + ∫ y, ‖kernel 0 y‖) ^ r) * C) (A.tensorSmooth r s u)) ∧
      (∀ (u : ∀ p : M, CovariantTwoTensor p) (s t C : ℝ),
        0 < s → s ≤ 1 → 0 ≤ C →
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun p => TotalSpace.mk' TensorFiber p (u p)) → A.TensorWeightedBound t 0 C u →
        A.TensorWeightedBound s m (D * weightedGainConstant r m * C) (A.tensorSmooth r s u)) :=
  A.bundle_smoothing_bounds (F := TensorFiber) (E := CovariantTwoTensor (M := M))
    A.tensorTriv A.tensorTriv_domain r m

theorem tensor_smoothing_tail (r m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ p : M, CovariantTwoTensor p) (s t τ B C : ℝ),
      0 < τ → τ ≤ s → s ≤ t → t ≤ 1 → 0 ≤ B → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      A.TensorWeightedBound t r B u → A.TensorWeightedBound t m C u →
      A.TensorWeightedBound τ m
        (D * tailConstant r * (B * (s / t) ^ r + C * (τ / t) ^ r))
        (fun p => u p - A.tensorSmooth r s u p) :=
  A.bundle_smoothing_tail (F := TensorFiber) (E := CovariantTwoTensor (M := M)) A.tensorTriv A.tensorTriv_domain r m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

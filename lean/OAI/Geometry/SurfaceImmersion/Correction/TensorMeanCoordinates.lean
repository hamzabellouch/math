import OAI.Geometry.SurfaceImmersion.Correction.TensorSmoothing
import OAI.Geometry.SurfaceImmersion.Correction.BundleSmoothingLinearity

namespace OAI

/-! Encode global tensor sections by their finite atlas coordinates. This
retains the compact-surface partition identity while permitting the finite
mean iteration to run on a normed vector-valued function space. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

local instance meanModelNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance meanModelSpace : NormedSpace ℝ TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

local instance meanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance meanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))

local instance sectionTensorNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance sectionTensorSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def tensorEncode (u : ∀ x : M, CovariantTwoTensor x) : Base → A.centers → TensorFiber :=
  fun x i => A.bundleLocalize A.tensorTriv i u x

def tensorDecode (f : Base → A.centers → TensorFiber) : ∀ x : M, CovariantTwoTensor x :=
  fun x => ∑ i : A.centers, A.bundleRestore A.tensorTriv i (fun y => f y i) x

lemma tensorDecode_encode (u : ∀ x : M, CovariantTwoTensor x) :
    A.tensorDecode (A.tensorEncode u) = u := by
  funext x
  exact A.bundle_sum_restore_localize A.tensorTriv A.tensorTriv_domain u x

lemma tensorEncode_add (u v : ∀ x : M, CovariantTwoTensor x) :
    A.tensorEncode (u + v) = A.tensorEncode u + A.tensorEncode v := by
  funext x i
  exact congrFun (A.bundleLocalize_add A.tensorTriv i u v) x

lemma tensorEncode_smul (a : ℝ) (u : ∀ x : M, CovariantTwoTensor x) :
    A.tensorEncode (a • u) = a • A.tensorEncode u := by
  funext x i
  exact congrFun (A.bundleLocalize_smul A.tensorTriv i a u) x

lemma tensorDecode_add (f g : Base → A.centers → TensorFiber) :
    A.tensorDecode (f + g) = A.tensorDecode f + A.tensorDecode g := by
  funext x
  simp only [tensorDecode, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (A.bundleRestore_add A.tensorTriv i (fun y => f y i) (fun y => g y i)) x

lemma tensorDecode_smul (a : ℝ) (f : Base → A.centers → TensorFiber) :
    A.tensorDecode (a • f) = a • A.tensorDecode f := by
  funext x
  simp only [tensorDecode, Pi.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (A.bundleRestore_smul A.tensorTriv i a (fun y => f y i)) x

lemma tensorEncode_sub (u v : ∀ x : M, CovariantTwoTensor x) :
    A.tensorEncode (u - v) = A.tensorEncode u - A.tensorEncode v := by
  funext x i
  change A.bundleLocalize A.tensorTriv i (u - v) x =
    A.bundleLocalize A.tensorTriv i u x - A.bundleLocalize A.tensorTriv i v x
  by_cases hx : x ∈ (chart (i : M)).target
  · simp only [bundleLocalize, localize, indicator_of_mem hx, bundleComponent,
      Pi.sub_apply, map_sub, smul_sub]
  · simp only [bundleLocalize, localize, indicator_of_notMem hx, sub_self]

lemma tensorDecode_sub (f g : Base → A.centers → TensorFiber) :
    A.tensorDecode (f - g) = A.tensorDecode f - A.tensorDecode g := by
  funext x
  simp only [tensorDecode, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bundleRestore, map_sub, smul_sub]

def tensorProject (f : Base → A.centers → TensorFiber) : Base → A.centers → TensorFiber :=
  A.tensorEncode (A.tensorDecode f)

lemma tensorProject_encode (u : ∀ x : M, CovariantTwoTensor x) :
    A.tensorProject (A.tensorEncode u) = A.tensorEncode u := by
  unfold tensorProject
  rw [A.tensorDecode_encode]

lemma tensorProject_idempotent (f : Base → A.centers → TensorFiber) :
    A.tensorProject (A.tensorProject f) = A.tensorProject f :=
  A.tensorProject_encode _

variable [CompactSpace M]

lemma tensorEncode_smooth {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x))) : ContDiff ℝ ∞ (A.tensorEncode u) := by
  apply contDiff_pi.mpr
  intro i
  exact A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu

omit [CompactSpace M] in
lemma tensorDecode_smooth {f : Base → A.centers → TensorFiber} (hf : ContDiff ℝ ∞ f) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.tensorDecode f x)) := by
  apply ContMDiff.sum_section
  intro i _
  exact A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain i (contDiff_pi.mp hf i)

lemma tensorEncode_bound {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hC : 0 ≤ C) (hb : A.TensorWeightedBound s m C u) :
    WeightedBound univ s m C (A.tensorEncode u) :=
  WeightedBound.pi uniqueDiffOn_univ hs hC
    (contDiffOn_pi.mp (A.tensorEncode_smooth hu).contDiffOn) hb

omit [CompactSpace M] in
lemma tensorBound_of_encode {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContDiff ℝ ∞ (A.tensorEncode u)) {s C : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hb : WeightedBound univ s m C (A.tensorEncode u)) :
    A.TensorWeightedBound s m C u :=
  fun i => hb.component uniqueDiffOn_univ hs hC hu.contDiffOn i

lemma tensorDecode_bound (m : ℕ) : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (f : Base → A.centers → TensorFiber) (s C : ℝ), 0 < s → s ≤ 1 → 0 ≤ C →
      ContDiff ℝ ∞ f → WeightedBound univ s m C f →
      A.TensorWeightedBound s m (D * C) (A.tensorDecode f) := by
  obtain ⟨D,hD,hd⟩ := A.bundle_restoration_bound A.tensorTriv A.tensorTriv_domain m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  exact hd (fun i x => f x i) s C hs hs1 hC (fun i => contDiff_pi.mp hf i)
    (fun i => hb.component uniqueDiffOn_univ hs.le hC hf.contDiffOn i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

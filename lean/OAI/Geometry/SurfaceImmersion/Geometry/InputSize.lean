import OAI.Geometry.SurfaceImmersion.Geometry.CompactSectionBounds
import OAI.Geometry.SurfaceImmersion.Correction.CoupledSmoothing

namespace OAI

/-! Finite joint input norms for the adaptive correction iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
local instance inputSizeFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputSizeFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance inputSizeDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance inputSizeDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance inputSizeSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputSizeSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma inputBound_mono_const {t C D : ℝ} {m : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p} (hb : A.InputBound t m C G H)
    (hCD : C ≤ D) : A.InputBound t m D G H := by
  constructor
  · intro i j hj x
    exact (hb.1 i j hj x).trans hCD
  · intro i
    exact (hb.2 i).mono_const hCD

omit [CompactSpace M] in
lemma inputBound_mono_order {t C : ℝ} {m r : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p} (hb : A.InputBound t m C G H)
    (hr : r ≤ m) : A.InputBound t r C G H := by
  constructor
  · intro i j hj x
    exact hb.1 i j (hj.trans (Nat.add_le_add_left hr 2)) x
  · intro i
    exact (hb.2 i).mono_order hr

/-- The least nonnegative bound for the joint map/metric input. -/
def inputSize (t : ℝ) (m : ℕ) (G : M → Space)
    (H : ∀ p : M, CovariantTwoTensor p) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ A.InputBound t m C G H}

omit [CompactSpace M] in
lemma inputSize_nonneg {t : ℝ} {m : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p}
    (hex : ∃ C : ℝ, 0 ≤ C ∧ A.InputBound t m C G H) :
    0 ≤ A.inputSize t m G H := by
  apply le_csInf hex
  intro C hC
  exact hC.1

omit [CompactSpace M] in
lemma inputSize_le {t C : ℝ} {m : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p}
    (hC : 0 ≤ C) (hb : A.InputBound t m C G H) :
    A.inputSize t m G H ≤ C := by
  exact csInf_le ⟨0,fun _ h => h.1⟩ ⟨hC,hb⟩

omit [CompactSpace M] in
lemma inputSize_bound {t : ℝ} {m : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p}
    (hex : ∃ C : ℝ, 0 ≤ C ∧ A.InputBound t m C G H) :
    A.InputBound t m (A.inputSize t m G H) G H := by
  constructor
  · intro i j hj x
    exact le_csInf hex (fun C hC => hC.2.1 i j hj x)
  · intro i j hj x hx
    exact le_csInf hex (fun C hC => hC.2.2 i j hj x hx)

omit [CompactSpace M] in
lemma inputSize_le_iff {t C : ℝ} {m : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p}
    (hex : ∃ D : ℝ, 0 ≤ D ∧ A.InputBound t m D G H) (hC : 0 ≤ C) :
    A.inputSize t m G H ≤ C ↔ A.InputBound t m C G H := by
  exact ⟨fun h => A.inputBound_mono_const (A.inputSize_bound hex) h,
    A.inputSize_le hC⟩

omit [CompactSpace M] in
lemma inputSize_mono_order {t : ℝ} {m r : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p}
    (hex : ∃ C : ℝ, 0 ≤ C ∧ A.InputBound t m C G H) (hr : r ≤ m) :
    A.inputSize t r G H ≤ A.inputSize t m G H :=
  A.inputSize_le (A.inputSize_nonneg hex)
    (A.inputBound_mono_order (A.inputSize_bound hex) hr)

/-- Every finite-stage smooth input has a finite joint norm, without any
uniform bound on its higher derivatives. -/
theorem exists_input_bound {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (m : ℕ)
    {G : M → Space} {H : ∀ p : M, CovariantTwoTensor p}
    (hG : ContMDiff planeModel spaceModel ∞ G)
    (hH : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (H p))) :
    ∃ C : ℝ, 0 ≤ C ∧ A.InputBound t m C G H := by
  obtain ⟨CG,hCG,hGb⟩ := A.exists_shifted_bound 2 m hG
  obtain ⟨CH,hCH,hHb⟩ := A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain m hH
  refine ⟨CG+CH,add_nonneg hCG hCH,?_,?_⟩
  · intro i j hj x
    have hh := hGb i j hj x
    simp only [one_pow,one_mul] at hh
    calc
      _ ≤ 1*‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) G) x‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ ht ht1) (norm_nonneg _)
      _ ≤ CG+CH := by simpa only [one_mul] using hh.trans (le_add_of_nonneg_right hCH)
  · intro i
    exact ((hHb i).shrink_scale ht ht1).mono_const (le_add_of_nonneg_left hCG)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

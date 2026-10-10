import OAI.Geometry.SurfaceImmersion.Geometry.ScaledInitialMap
import OAI.Geometry.SurfaceImmersion.Correction.PreparedCorrection
import OAI.Geometry.SurfaceImmersion.Geometry.GlobalInputRecurrence

namespace OAI

/-! Finite initial input estimates for the scalar-contracted map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
local instance initialBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance initialBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma space_smul_contMDiff {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    ContMDiff planeModel spaceModel ∞ (a • F) :=
  (a • ContinuousLinearMap.id ℝ Space).contDiff.contMDiff.comp hF

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma weightedBound_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {s C : ℝ} {m : ℕ}
    (hb : A.WeightedBound s m C F) (a : ℝ) :
    A.WeightedBound s m (|a| * C) (a • F) := by
  intro i
  rw [localize_smul]
  exact (hb i).const_smul uniqueDiffOn_univ
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn a

lemma shiftedBound_smul_of_abs_le_one {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {s C a : ℝ} {q m : ℕ}
    (_hs : 0 ≤ s) (hC : 0 ≤ C) (ha : |a| ≤ 1)
    (hb : A.ShiftedBound q m s C F) : A.ShiftedBound q m s C (a • F) := by
  intro i j hj x
  have hf := localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF
  change s^(j-q)*‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) (a • F)) x‖ ≤ C
  rw [localize_smul,iteratedFDeriv_const_smul_apply (hf.of_le (by simp)).contDiffAt,
    norm_smul,Real.norm_eq_abs]
  calc
    _ = |a| * (s^(j-q)*‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) F) x‖) := by ring
    _ ≤ |a| * C := mul_le_mul_of_nonneg_left (hb i j hj x) (abs_nonneg a)
    _ ≤ C := by nlinarith

omit [CompactSpace M] in
lemma shifted_zero_to_weighted {F : M → Space} {P : ℝ} {q : ℕ}
    (hb : A.ShiftedBound q 0 1 P F) : A.WeightedBound 1 q P F := by
  intro i j hj x _
  have hh := hb i j (by omega) x
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hh

/-- The contracted initial map has the required two-derivative prefix and
finite high-order input bound. -/
theorem contracted_initial_input_scaled
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    {g : SmoothMetric M} {δ s σ P Q C D e B : ℝ} {m : ℕ}
    (hδ : δ ≠ 0) (hδ1 : δ^2 ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hσ : 0 < σ) (hsσ : s ≤ σ)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hmap0 : A.ShiftedBound 2 0 σ P F) (hmap : A.ShiftedBound 2 m σ C F)
    (hmetric0 : A.TensorWeightedBound 1 0 Q g.inner)
    (hmetric : A.TensorWeightedBound 1 m D g.inner)
    (herror : A.TensorWeightedBound s m (δ^2*e) (inducedTensor F-g.inner))
    (hMB : P+(s/σ)*C ≤ B) (hHB : Q+s*D+e ≤ B) :
    A.InputBound s m B (Real.sqrt (1-δ^2) • F)
      (normalizedTensorDefect g.inner δ (Real.sqrt (1-δ^2) • F)) := by
  have hsqrt : |Real.sqrt (1-δ^2)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (sub_nonneg.mpr hδ1),Real.sqrt_nonneg (1-δ^2),sq_nonneg δ]
  have hbF := A.shiftedBound_smul_of_abs_le_one hF hs
    (add_nonneg hP (mul_nonneg (div_nonneg hs hσ.le) hC)) hsqrt
    (A.shifted_shrink_with_prefix hmap0 hmap hσ hs hsσ hP hC)
  have hbH := A.normalized_initial_error_bound hF g.contMDiff hδ hδ1 he herror
  have hh := A.tensorWeightedBound_add g.contMDiff
    ((A.normalizedTensorDefect_smooth g.contMDiff δ (space_smul_contMDiff hF (Real.sqrt (1-δ^2)))).sub_section g.contMDiff)
    hs (A.tensor_shrink_with_norm hs hs1 hD hmetric0 hmetric) hbH
  have hid : g.inner+(normalizedTensorDefect g.inner δ (Real.sqrt (1-δ^2) • F)-g.inner) =
      normalizedTensorDefect g.inner δ (Real.sqrt (1-δ^2) • F) := by abel
  rw [hid] at hh
  exact ⟨fun i j hj x => (hbF i j hj x).trans hMB,fun i => (hh i).mono_const hHB⟩

/-- The contracted initial map has the required two-derivative prefix and
finite high-order input bound. -/
theorem contracted_initial_input
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    {g : SmoothMetric M} {δ s P Q C D e B : ℝ} {m : ℕ}
    (hδ : δ ≠ 0) (hδ1 : δ^2 ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hmap0 : A.ShiftedBound 2 0 1 P F) (hmap : A.ShiftedBound 2 m 1 C F)
    (hmetric0 : A.TensorWeightedBound 1 0 Q g.inner)
    (hmetric : A.TensorWeightedBound 1 m D g.inner)
    (herror : A.TensorWeightedBound s m (δ^2*e) (inducedTensor F-g.inner))
    (hMB : P+s*C ≤ B) (hHB : Q+s*D+e ≤ B) :
    A.InputBound s m B (Real.sqrt (1-δ^2) • F)
      (normalizedTensorDefect g.inner δ (Real.sqrt (1-δ^2) • F)) := by
  exact A.contracted_initial_input_scaled hF hδ hδ1 hs hs1 zero_lt_one hs1
    hP hC hD he hmap0 hmap hmetric0 hmetric herror
    (by simpa only [div_one] using hMB) hHB

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

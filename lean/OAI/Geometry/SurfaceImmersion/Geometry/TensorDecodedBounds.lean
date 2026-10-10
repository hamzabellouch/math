import OAI.Geometry.SurfaceImmersion.Atlas.TensorPlaneCoordinates
import OAI.Geometry.SurfaceImmersion.Correction.TensorMeanIteration

namespace OAI

/-! Uniform chart-reading estimates for the redundant coordinates used by
finite mean substitution, including the radius of every local trial ball. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance decodedFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance decodedFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance decodedDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance decodedDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance decodedSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance decodedSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma tensorPlaneRead_decode_sub (i : A.centers) (f g : Base → A.centers → TensorFiber) :
    A.tensorPlaneRead i (A.tensorDecode (f-g)) =
      A.tensorPlaneRead i (A.tensorDecode f) - A.tensorPlaneRead i (A.tensorDecode g) := by
  rw [A.tensorDecode_sub, A.tensorPlaneRead_sub]

theorem tensorPlaneRead_decode_bound (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (i : A.centers) (f : Base → A.centers → TensorFiber) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f → WeightedBound univ s m C f →
      WeightedBound univ s m (D*C) (A.tensorPlaneRead i (A.tensorDecode f)) := by
  classical
  obtain ⟨E,hE,he⟩ := A.tensorDecode_bound m
  choose D hD hd using fun i : A.centers => A.tensorPlaneRead_bound i m
  let B : ℝ := (∑ i : A.centers, D i) * E
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro i f s C hs hs1 hC hf hb
  have hh := hd i (A.tensorDecode f) s (E*C) hs hs1 (mul_nonneg hE hC)
    (A.tensorDecode_smooth hf) (he f s C hs hs1 hC hf hb)
  apply hh.mono_const
  have hi : D i ≤ ∑ j : A.centers, D j :=
    Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ i)
  calc
    D i * (E*C) = (D i * E)*C := by ring
    _ ≤ B*C := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hi hE) hC
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hC

theorem tensorPlaneRead_decode_ball : ∃ D : ℝ, 1 ≤ D ∧
    ∀ (reference : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (reference x)) →
    ∀ (f : Base → A.centers → TensorFiber) (r : ℝ), 0 ≤ r → ContDiff ℝ ∞ f →
      InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
      InTrialBall univ (A.tensorPlaneRead i reference) (D*r) (A.tensorPlaneRead i (A.tensorDecode f)) := by
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRead_decode_bound 0
  refine ⟨D+1,by linarith,?_⟩
  intro reference href f r hr hf hb i x _
  have hdiff : ContDiff ℝ ∞ (f-A.tensorEncode reference) := hf.sub (A.tensorEncode_smooth href)
  have hbound : WeightedBound univ 1 0 r (f-A.tensorEncode reference) := by
    intro j hj y hy
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    simpa only [pow_zero, one_mul, norm_iteratedFDerivWithin_zero, Pi.sub_apply] using (hb y hy).le
  have hh := (hd i (f-A.tensorEncode reference) 1 r zero_lt_one le_rfl hr hdiff hbound).norm_le
    (mem_univ x)
  rw [A.tensorPlaneRead_decode_sub, A.tensorDecode_encode] at hh
  have hrpos : 0 < r := (norm_nonneg (f 0 - A.tensorEncode reference 0)).trans_lt (hb 0 (mem_univ 0))
  exact hh.trans_lt (by nlinarith)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import OAI.Geometry.SurfaceImmersion.Correction.SmoothPrimitiveFamily
import OAI.Geometry.SurfaceImmersion.Geometry.UniformMetricPathBounds

namespace OAI

/-! One fixed cycle count controls all partial metrics. The estimates allow
a different exact primitive decomposition in every cycle. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance cycleBoundFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance cycleBoundFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance cycleBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance cycleBoundDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance cycleBoundSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance cycleBoundSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothPrimitiveFamily
variable {ι : Type*} [Fintype ι] {u : ∀ p : M, CovariantTwoTensor p}
  (d : SmoothPrimitiveFamily ι u) (A : SmoothingAtlas M)

lemma partial_tensor_bound {D : ℝ} (hD : 0 ≤ D) (m : ℕ)
    (hb : ∀ a, A.TensorWeightedBound 1 m D (d.term a)) (s : Finset ι) :
    A.TensorWeightedBound 1 m ((Fintype.card ι : ℝ)*D) (fun p => ∑ a ∈ s, d.term a p) := by
  classical
  intro i
  change WeightedEstimates.WeightedBound univ 1 m _
    (A.bundleLocalize A.tensorTriv i (fun p => ∑ a ∈ s, d.term a p))
  rw [A.bundleLocalize_sum]
  have hh := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ zero_le_one s
    (fun _ : ι => D) (fun a => A.bundleLocalize A.tensorTriv i (d.term a))
    (fun a _ => (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i (d.term_smooth A a)).contDiffOn)
    (fun a _ => hb a i)
  apply hh.mono_const
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_univ s) hD

lemma scaled_partial_tensor_bound {D : ℝ} (hD : 0 ≤ D) (m : ℕ)
    (hb : ∀ a, A.TensorWeightedBound 1 m D (d.term a)) (N : ℕ) (s : Finset ι) :
    A.TensorWeightedBound 1 m ((Fintype.card ι : ℝ)*D/(N : ℝ))
      ((N : ℝ)⁻¹ • (fun p => ∑ a ∈ s, d.term a p)) := by
  have hh := A.tensorWeightedBound_const_smul
    (ContMDiff.sum_section (fun a _ => d.term_smooth A a))
    (d.partial_tensor_bound A hD m hb s) (N : ℝ)⁻¹
  convert hh using 1
  rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  ring

lemma cycleMetric_bound {D C : ℝ} (hD : 0 ≤ D) (m : ℕ)
    (hb : ∀ a, A.TensorWeightedBound 1 m D (d.term a))
    (g : SmoothMetric M) (N c : ℕ) (s : Finset ι)
    (hpath : A.TensorWeightedBound 1 m C (g.inner+((c : ℝ)/(N : ℝ)) • u)) :
    A.TensorWeightedBound 1 m (C+(Fintype.card ι : ℝ)*D/(N : ℝ))
      (d.cycleMetric A g N c s).inner := by
  have hsmooth := g.contMDiff.add_section
    ((d.tensor_smooth A).const_smul_section (a := (c : ℝ)/(N : ℝ)))
  have hss : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p ((N : ℝ)⁻¹ • ∑ a ∈ s, d.term a p)) :=
    (ContMDiff.sum_section (fun a _ => d.term_smooth A a)).const_smul_section
  have hh := A.tensorWeightedBound_add hsmooth hss zero_le_one hpath
    (d.scaled_partial_tensor_bound A hD m hb N s)
  have he : (d.cycleMetric A g N c s).inner =
      (g.inner+((c : ℝ)/(N : ℝ)) • u)+(N : ℝ)⁻¹ • (fun p => ∑ a ∈ s, d.term a p) := by
    funext p
    change g.inner p+(((c : ℝ)/(N : ℝ)) • u p+(N : ℝ)⁻¹ • ∑ a ∈ s, d.term a p) = _
    exact (add_assoc _ _ _).symm
  rw [he]
  exact hh

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma exists_cycle_count (D : ℝ) :
    ∃ N : ℕ, 0 < N ∧ (Fintype.card ι : ℝ)*D/(N : ℝ) ≤ 1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 ((Fintype.card ι : ℝ)*D))
  have hN0 : (0 : ℝ) < N := (le_max_left _ _).trans_lt hN
  refine ⟨N,by exact_mod_cast hN0,?_⟩
  exact (div_le_one hN0).mpr ((le_max_right _ _).trans hN.le)

end SmoothPrimitiveFamily
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

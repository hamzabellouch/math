import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTensorPullback
import OAI.Geometry.SurfaceImmersion.Geometry.CompactLocalBounds
import OAI.Geometry.Immersion.ClosedSurface.CoordinateBounds

namespace OAI

/-! Fixed nonlinear coordinate changes preserve weighted tensor error
bounds with a constant independent of the fast scale. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

def tensorCoordinateMatrixUnit (k l : Fin 3) : PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor :=
  (ContinuousLinearMap.proj l).smulRight (Pi.single k 1)

lemma tensorCoordinatePullbackValue_sum (T : Base → Base) (x : Base) :
    tensorCoordinatePullbackValue T x =
      ∑ k : Fin 3, ∑ l : Fin 3,
        tensorCoordinateJacobian T k l x • tensorCoordinateMatrixUnit k l := by
  ext A k
  simp only [sum_apply,smul_apply,
    Finset.sum_apply,Pi.smul_apply,tensorCoordinateMatrixUnit,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
    Pi.single_apply]
  simp only [mul_ite,mul_one,mul_zero]
  have hi (j : Fin 3) :
      (∑ l : Fin 3, if k = j then tensorCoordinateJacobian T j l x * A l else 0) =
        if k = j then ∑ l : Fin 3, tensorCoordinateJacobian T j l x * A l else 0 := by
    split_ifs <;> simp_all
  simp_rw [hi]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact (tensorCoordinateJacobian_sum T x A k).symm

lemma tensorCoordinatePullbackValue_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T) :
    ContDiff ℝ ∞ (tensorCoordinatePullbackValue T) := by
  have he : tensorCoordinatePullbackValue T = fun x =>
      ∑ k : Fin 3, ∑ l : Fin 3,
        tensorCoordinateJacobian T k l x • tensorCoordinateMatrixUnit k l :=
    funext (tensorCoordinatePullbackValue_sum T)
  rw [he]
  apply ContDiff.sum
  intro k _
  apply ContDiff.sum
  intro l _
  exact (tensorCoordinateJacobian_smooth hT k l).smul contDiff_const

theorem fixed_tensor_coordinate_bound {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {V W : Set Base} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hW : IsOpen W) (hVW : MapsTo T V W) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → PhaseMean.Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiffOn ℝ ∞ f W →
      WeightedBound W s m C f →
      WeightedBound V s m (D*C) (fun x => tensorCoordinatePullbackValue T x (f (T x))) := by
  obtain ⟨B,hB,hTb⟩ := compact_local_weighted_bound hV isOpen_univ hVc
    subset_closure (subset_univ _) hT.contDiffOn m
  obtain ⟨J,hJ,hJb⟩ := compact_local_weighted_bound hV isOpen_univ hVc
    subset_closure (subset_univ _) (tensorCoordinatePullbackValue_smooth hT).contDiffOn m
  refine ⟨2^m*J*((m.factorial : ℝ)*B^m),by positivity,?_⟩
  intro f s C hs hs1 hC hf hb
  have hc := hb.comp_coordinates hV.uniqueDiffOn hW.uniqueDiffOn hs hs1 hB hC
    hT.contDiffOn hf hVW (fun j _ hj x hx => by
      simpa only [one_pow,one_mul] using hTb 1 zero_le_one le_rfl j hj x hx)
  have hh := (hJb s hs.le hs1).clm_apply hV.uniqueDiffOn hs.le (zero_le_one.trans hJ)
    (by positivity) (tensorCoordinatePullbackValue_smooth hT).contDiffOn
    (hf.comp hT.contDiffOn hVW) hc
  convert hh using 1 <;> first | rfl | ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI

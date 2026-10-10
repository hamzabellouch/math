import OAI.Geometry.SurfaceImmersion.Correction.GlobalSmoothedMetricStep
import OAI.Geometry.SurfaceImmersion.Geometry.GlobalScaleGain

namespace OAI

/-! Both components of the actual next input admit a common recurrence bound. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates JetPolynomial
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma shiftedBound_of_weighted {f : Base → V} {s C : ℝ} {q m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : WeightedEstimates.WeightedBound univ s (q+m) C f) :
    ShiftedBound q m s (C/s^q) f := by
  intro j hj x
  have hh := hb.deriv_le hs hj (mem_univ x)
  rw [iteratedFDerivWithin_univ] at hh
  by_cases hq : q ≤ j
  · have he : s^j = s^(j-q)*s^q := by rw [← pow_add,Nat.sub_add_cancel hq]
    calc
      _ ≤ s^(j-q)*(C/s^j) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ = _ := by rw [he]; field_simp
  · have hjq : j ≤ q := by omega
    simp only [Nat.sub_eq_zero_of_le hjq,pow_zero,one_mul]
    exact hh.trans (div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 hjq))

lemma weighted_shrink_with_norm {E W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : E → W} {s P C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hp : WeightedEstimates.WeightedBound univ 1 0 P f)
    (hc : WeightedEstimates.WeightedBound univ 1 m C f) :
    WeightedEstimates.WeightedBound univ s m (P+s*C) f := by
  intro j hj x hx
  by_cases hz : j = 0
  · subst j
    have h := hp 0 le_rfl x hx
    simp only [pow_zero,one_mul] at h ⊢
    exact h.trans (le_add_of_nonneg_right (mul_nonneg hs hC))
  · have h := hc j hj x hx
    simp only [one_pow,one_mul] at h
    calc
      _ ≤ s^j*C := mul_le_mul_of_nonneg_left h (pow_nonneg hs _)
      _ ≤ s*C := mul_le_mul_of_nonneg_right
        (by simpa only [pow_one] using pow_le_pow_of_le_one hs hs1 (show 1 ≤ j by omega)) hC
      _ ≤ P+s*C := le_add_of_nonneg_left (by
        exact le_trans (norm_nonneg (f x)) (hp.norm_le (mem_univ x)))

local instance inputRecurrenceFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance inputRecurrenceFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma weighted_to_shifted {F : M → V} {s C : ℝ} {q m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : A.WeightedBound s (q+m) C F) : A.ShiftedBound q m s (C/s^q) F :=
  fun i => shiftedBound_of_weighted hs hs1 hC (hb i)

omit [CompactSpace M] in
lemma tensor_shrink_with_norm {T : ∀ p : M, CovariantTwoTensor p} {s P C : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hp : A.TensorWeightedBound 1 0 P T) (hc : A.TensorWeightedBound 1 m C T) :
    A.TensorWeightedBound s m (P+s*C) T :=
  fun i => weighted_shrink_with_norm hs hs1 hC (hp i) (hc i)

theorem next_input_bound {target : ∀ p : M, CovariantTwoTensor p}
    (htarget : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    {F U : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hU : ContMDiff planeModel spaceModel ∞ U)
    {t τ P P₀ Pm C K B δ' : ℝ} {m : ℕ}
    (ht : 0 < t) (hτ : 0 < τ) (hτt : τ ≤ t) (hτ1 : τ ≤ 1)
    (hP : 0 ≤ P) (hP₀ : 0 ≤ P₀) (hPm : 0 ≤ Pm)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hp : A.ShiftedBound 2 0 t P F) (hc : A.ShiftedBound 2 m t C F)
    (hu : A.WeightedBound τ (2+m) K U)
    (ht₀ : A.TensorWeightedBound 1 0 P₀ target)
    (htm : A.TensorWeightedBound 1 m Pm target)
    (hb : A.TensorWeightedBound τ m B (normalizedTensorDefect target δ' (F+U)-target)) :
    A.InputBound τ m (P+P₀+τ*Pm+(τ/t)*C+K/τ^2+B)
      (F+U) (normalizedTensorDefect target δ' (F+U)) := by
  have hmap := A.shifted_map_recurrence hF hU hp hc
    (A.weighted_to_shifted hτ hτ1 hK hu) ht hτ.le hτt hP hC
  have htargetBound := A.tensor_shrink_with_norm hτ.le hτ1 hPm ht₀ htm
  have hdiff := (A.normalizedTensorDefect_smooth htarget δ' (hF.add hU)).sub_section htarget
  have htensor := A.tensorWeightedBound_add htarget hdiff hτ.le htargetBound hb
  have he : target+(normalizedTensorDefect target δ' (F+U)-target) =
      normalizedTensorDefect target δ' (F+U) := by abel
  rw [he] at htensor
  constructor
  · intro i j hj x
    exact (hmap i j hj x).trans (by
      have hq : 0 ≤ τ*Pm := mul_nonneg hτ.le hPm
      linarith)
  · intro i
    exact (htensor i).mono_const (by
      have hq : 0 ≤ (τ/t)*C := mul_nonneg (div_nonneg hτ.le ht.le) hC
      have hk : 0 ≤ K/τ^2 := div_nonneg hK (sq_nonneg τ)
      linarith)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

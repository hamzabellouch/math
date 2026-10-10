import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds
import OAI.Geometry.SurfaceImmersion.Geometry.FixedOrderThreshold

namespace OAI

/-! A square of the fast scale gives a uniform low-order geometric budget. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.WeightedEstimates
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma WeightedBound.square_scale {f : E → V} {z B C : ℝ} {m : ℕ}
    (hb : WeightedBound univ z m C f) (hzero : WeightedBound univ 1 0 B f)
    (hz : 0 < z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hsmall : C*z ≤ 1) :
    WeightedBound univ (z^2) m (B+1) f := by
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hzero.norm_le (mem_univ 0))
  intro j hj x hx
  by_cases hj0 : j = 0
  · subst j
    simpa only [pow_zero,one_mul,norm_iteratedFDerivWithin_zero] using
      (hzero.norm_le hx).trans (le_add_of_nonneg_right zero_le_one)
  · have hj1 : 1 ≤ j := by omega
    have hp : z^j ≤ z := by
      simpa only [pow_one] using pow_le_pow_of_le_one hz.le hz1 hj1
    calc
      (z^2)^j*‖iteratedFDerivWithin ℝ j f univ x‖ =
          z^j*(z^j*‖iteratedFDerivWithin ℝ j f univ x‖) := by rw [pow_two,mul_pow]; ring
      _ ≤ z^j*C := mul_le_mul_of_nonneg_left (hb j hj x hx) (pow_nonneg hz.le _)
      _ ≤ z*C := mul_le_mul_of_nonneg_right hp hC
      _ ≤ 1 := by simpa only [mul_comm] using hsmall
      _ ≤ B+1 := by linarith

end ClosedSurfaceR4.WeightedEstimates
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_rescaled_read_bound (V₀ : ℝ) (hV₀ : 0 ≤ V₀) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ C : ℝ, 0 ≤ C → ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
    ∀ z : ℝ, 0 < z → z < η → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F → A.WeightedBound 1 0 V₀ F →
      A.WeightedBound z 3 C F → ∀ i,
      WeightedEstimates.WeightedBound univ (z^2) 3 B
        (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
  classical
  choose D₀ hD₀ hd₀ using fun i => A.vectorPlaneRead_bound (V := Space) i 0
  choose D₃ hD₃ hd₃ using fun i => A.vectorPlaneRead_bound (V := Space) i 3
  let L := ‖spaceCoordinates.toContinuousLinearMap‖
  let B := 1+∑ i : A.centers, L*D₀ i*V₀
  let K := 1+∑ i : A.centers, L*D₃ i
  have hL : 0 ≤ L := norm_nonneg _
  have hsum₀ : 0 ≤ ∑ i : A.centers, L*D₀ i*V₀ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg hL (hD₀ i)) hV₀)
  have hsum₃ : 0 ≤ ∑ i : A.centers, L*D₃ i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg hL (hD₃ i))
  refine ⟨B,by change 1 ≤ 1+∑ i : A.centers, L*D₀ i*V₀; linarith,?_⟩
  intro C hC
  obtain ⟨η,hη,hη1,hh⟩ := ExactCorrection.positive_power_threshold (K*C) 1 1
    zero_lt_one zero_lt_one
  refine ⟨η,hη,hη1,?_⟩
  intro z hz hzη F hF hzero hb i
  have hz1 := hzη.le.trans hη1
  have hread0 := (hd₀ i F 1 V₀ zero_lt_one le_rfl hV₀ hF hzero).linear
    uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hF).contDiffOn
    spaceCoordinates.toContinuousLinearMap
  have hread3 := (hd₃ i F z C hz hz1 hC hF hb).linear
    uniqueDiffOn_univ hz.le (A.vectorPlaneRead_smooth i hF).contDiffOn
    spaceCoordinates.toContinuousLinearMap
  have hiK : L*D₃ i ≤ K := by
    have hi := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => mul_nonneg hL (hD₃ j)) (Finset.mem_univ i)
    change L*D₃ i ≤ 1+∑ j : A.centers, L*D₃ j
    linarith
  have hsmall : (L*(D₃ i*C))*z ≤ 1 := by
    have hh' : (K*C)*z ≤ 1 := by simpa only [Real.rpow_one] using (hh z hz hzη).le
    exact (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_right hiK hC] : L*(D₃ i*C) ≤ K*C) hz.le).trans hh'
  apply (hread3.square_scale hread0 hz hz1 (mul_nonneg hL (mul_nonneg (hD₃ i) hC)) hsmall).mono_const
  have hi := Finset.single_le_sum (s := Finset.univ)
    (fun j _ => mul_nonneg (mul_nonneg hL (hD₀ j)) hV₀) (Finset.mem_univ i)
  change L*(D₀ i*V₀)+1 ≤ 1+∑ j : A.centers, L*D₀ j*V₀
  nlinarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

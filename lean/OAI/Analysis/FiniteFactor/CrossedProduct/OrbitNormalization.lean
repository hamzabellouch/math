import OAI.Analysis.FiniteFactor.Fiber.Shift
import OAI.Analysis.FiniteFactor.CrossedProduct.CappedPair
import OAI.Analysis.FiniteFactor.OrbitSampling.TorusSupport

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sourceCocycle_orbit_ratio (θ c : SourceCoordinate → ℝ)
    {x : SourceCoordinate → ℝ} (hx : finiteFloorSupport θ x) (n k : ℤ) :
    sourceCocycle θ c k (coordinateRotate θ n x) / sourceCocycle θ c k x =
      sourceCocycle θ c n (coordinateRotate θ k x) / sourceCocycle θ c n x := by
  apply (div_eq_div_iff (ne_of_gt (sourceCocycle_pos ..)) (ne_of_gt (sourceCocycle_pos ..))).mpr
  rw [← sourceCocycle_add θ c hx n k, ← sourceCocycle_add θ c hx k n, add_comm n k]

theorem sourceTorusRepresentative_rotate (θ : SourceCoordinate → ℝ) (n : ℤ) (z : SourceTorus) :
    sourceTorusRepresentative (sourceTorusRotate θ n z) =
      coordinateRotate θ n (sourceTorusRepresentative z) := by
  have hc : ∀ i, coordinateRotate θ n (sourceTorusRepresentative z) i ∈ Set.Ico (0 : ℝ) 1 :=
    fun i => ⟨Int.fract_nonneg _,Int.fract_lt_one _⟩
  calc
    _ = sourceTorusRepresentative (sourceTorusQuotient
        (coordinateRotate θ n (sourceTorusRepresentative z))) := by
      rw [sourceTorusQuotient_rotate, sourceTorusQuotient_representative]
    _ = _ := sourceTorusRepresentative_quotient _ hc

/-- Covariance and invariance give the rotated range inclusion after removing
the shift. This is an identity of bounded operators, not a range assumption. -/
theorem fiber_rotated_invariant
    (A B W : SourceFiberHilbert →L[ℂ] SourceFiberHilbert) (n : ℤ)
    (hc : fiberShift (-n) * A = B * fiberShift (-n))
    (hi : (1-A)*W*A = 0) :
    (1-B)*(fiberShift (-n)*W)*A = 0 := by
  have he : (1-B)*fiberShift (-n) = fiberShift (-n)*(1-A) := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hc]
  calc
    _ = ((1-B)*fiberShift (-n))*W*A := by simp only [mul_assoc]
    _ = (fiberShift (-n)*(1-A))*W*A := by rw [he]
    _ = fiberShift (-n)*((1-A)*W*A) := by simp only [mul_assoc]
    _ = 0 := by rw [hi, mul_zero]

/-- On ordered actual orbit pairs, the capped diagonal is exactly the
normalized weighted shift power. -/
theorem sourceCappedRatio_orbit_diagonal
    (θ : SourceCoordinate → ℝ) (z : SourceTorus) (n : ℕ)
    (hx : finiteFloorSupport θ (sourceTorusRepresentative z))
    (hord : ∀ i, sourceTorusRepresentative z i ≤
      sourceTorusRepresentative (sourceTorusRotate θ n z) i)
    (W : SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (hW : ∀ (v : SourceFiberHilbert) (k : ℤ), W v k =
      (sourceCocycle θ sourceLogWeight n
        (coordinateRotate θ (k-(n : ℤ)) (sourceTorusRepresentative z)) : ℂ) * v (k-(n : ℤ))) :
    fiberDiagonal (sourceCappedRatio θ (z,sourceTorusRotate θ n z))
      (sourceCappedRatio_norm θ (z,sourceTorusRotate θ n z)) =
    (sourceCocycle θ sourceLogWeight n (sourceTorusRepresentative z) : ℂ)⁻¹ •
      (fiberShift (-(n : ℤ))*W) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  funext k
  change sourceCappedRatio θ (z,sourceTorusRotate θ n z) k * v k =
    (sourceCocycle θ sourceLogWeight n (sourceTorusRepresentative z) : ℂ)⁻¹ *
      (W v (k-(-(n : ℤ))))
  have hord' : ∀ i, sourceTorusRepresentative z i ≤ coordinateRotate θ n (sourceTorusRepresentative z) i := by
    simpa only [sourceTorusRepresentative_rotate] using hord
  have hle := sourceCocycle_ordered θ sourceLogWeight sourceLogWeight_nonneg hx
    (finiteFloorSupport_rotate θ hx n) hord' k
  rw [sourceCappedRatio, sourceTorusRepresentative_rotate,
    min_eq_left ((div_le_one (sourceCocycle_pos ..)).mpr hle),
    sourceCocycle_orbit_ratio θ sourceLogWeight hx n k, Complex.ofReal_div, hW]
  have he : k-(-(n : ℤ))-(n : ℤ) = k := by omega
  rw [he]
  simp only [div_eq_mul_inv]
  ring

end
end FiniteFactor

end OAI

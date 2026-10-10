import OAI.Geometry.EinsteinFour.JacobiTraceProducts

namespace OAI

/-! The sharp averaged ordered-product estimate at Weyl energy three. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private instance matrixContinuousENorm : ContinuousENorm NormalMatrix :=
  @SeminormedAddGroup.toContinuousENorm NormalMatrix
    (inferInstanceAs (SeminormedAddGroup NormalMatrix))

theorem integral_trace_curvature_product_le
    (A B : Ω → NormalMatrix) (L : List (Ω → NormalMatrix))
    (hA : Continuous A) (hB : Continuous B)
    (hL : ∀ C ∈ L, Continuous C)
    (hpos : ∀ C ∈ L, ∀ x, (C x).PosSemidef ∧ (C x).trace = 3)
    (hEA : (∫ x, ‖A x‖ ^ 2 ∂μ) = 15 / 2)
    (hEB : (∫ x, ‖B x‖ ^ 2 ∂μ) = 15 / 2) :
    (∫ x, (A x * (L.map (fun C => C x)).prod * B x).trace ∂μ) ≤
      (5 / 6 : ℝ) * 3 ^ (L.length + 2) := by
  have hc : Continuous (fun x => (A x * (L.map (fun C => C x)).prod * B x).trace) :=
    ((hA.mul (continuous_list_prod L hL)).mul hB).matrix_trace
  have hi := hc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hia : Integrable (fun x => ‖A x‖ ^ 2) μ := (hA.norm.pow 2).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hib : Integrable (fun x => ‖B x‖ ^ 2) μ := (hB.norm.pow 2).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hpoint (x : Ω) : (A x * (L.map (fun C => C x)).prod * B x).trace ≤
      (3 ^ L.length / 2) * (‖A x‖ ^ 2 + ‖B x‖ ^ 2) := by
    have hp := abs_trace_curvature_product_le (A x) (B x)
      (L.map (fun C => C x)) (by
        intro C hC
        obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
        exact hpos D hD x)
    rw [List.length_map] at hp
    have hpow : (0 : ℝ) ≤ 3 ^ L.length := by positivity
    have hab : 2 * ‖A x‖ * ‖B x‖ ≤ ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖A x‖ - ‖B x‖)]
    have hmul := mul_le_mul_of_nonneg_left hab hpow
    have hp' := (le_abs_self _).trans hp
    nlinarith
  calc
    _ ≤ ∫ x, (3 ^ L.length / 2) * (‖A x‖ ^ 2 + ‖B x‖ ^ 2) ∂μ :=
      integral_mono hi ((hia.add hib).const_mul _) hpoint
    _ = (3 ^ L.length / 2) * (15 / 2 + 15 / 2) := by
      rw [integral_const_mul, integral_add hia hib, hEA, hEB]
    _ = _ := by rw [pow_add]; norm_num; ring

end
end PositiveEinsteinFour.Jacobi

end OAI

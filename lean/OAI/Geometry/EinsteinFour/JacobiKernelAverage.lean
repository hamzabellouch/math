import OAI.Geometry.EinsteinFour.JacobiKernelTrace
import OAI.Geometry.EinsteinFour.JacobiTraceAverage

namespace OAI

/-! Averaged powers of the actual noncommuting finite curvature kernel. -/
namespace PositiveEinsteinFour.Jacobi
open Matrix MeasureTheory
open scoped Matrix.Norms.Frobenius
noncomputable section
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [BorelSpace Ω] [CompactSpace Ω] in
theorem curvatureKernel_power_block_continuous {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℝ) (R : Fin N → Ω → NormalMatrix)
    (hR : ∀ i, Continuous (R i)) (k : ℕ) (i j : Fin N) :
    Continuous (fun x => blockAt (curvatureKernel G (fun l => R l x) ^ k) i j) := by
  induction k generalizing i j with
  | zero => simpa only [pow_zero, blockAt_one] using
      (continuous_const : Continuous (fun _ : Ω => if i = j then (1 : NormalMatrix) else 0))
  | succ k ih =>
      simp only [pow_succ', blockAt_mul, blockAt_curvatureKernel]
      exact continuous_finsetSum _ (fun l _ =>
        ((continuous_const : Continuous (fun _ : Ω => G i l)).smul (hR l)).mul (ih l j))

theorem integral_trace_kernel_sandwich_le {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (R : Fin N → Ω → NormalMatrix) (hR : ∀ i, Continuous (R i))
    (hbound : ∀ i x, ‖R i x‖ ≤ 3) (k : ℕ) (i j : Fin N)
    (A B : Ω → NormalMatrix) (hA : Continuous A) (hB : Continuous B)
    (hEA : (∫ x, ‖A x‖ ^ 2 ∂μ) = 15 / 2)
    (hEB : (∫ x, ‖B x‖ ^ 2 ∂μ) = 15 / 2) :
    (∫ x, (A x * blockAt (curvatureKernel G (fun l => R l x) ^ k) i j * B x).trace ∂μ) ≤
      (3 ^ k * (G ^ k) i j) * (15 / 2) := by
  let c := 3 ^ k * (G ^ k) i j
  have hc : 0 ≤ c := mul_nonneg (by positivity) (scalar_pow_entry_nonneg G hG k i j)
  have hcont := ((hA.mul (curvatureKernel_power_block_continuous G R hR k i j)).mul hB).matrix_trace
  have hi := hcont.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hia : Integrable (fun x => ‖A x‖ ^ 2) μ :=
    (hA.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hib : Integrable (fun x => ‖B x‖ ^ 2) μ :=
    (hB.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hp (x : Ω) :
      (A x * blockAt (curvatureKernel G (fun l => R l x) ^ k) i j * B x).trace ≤
        (c / 2) * (‖A x‖ ^ 2 + ‖B x‖ ^ 2) := by
    have h := (le_abs_self _).trans (abs_trace_mul_le_frobenius
      (A x * blockAt (curvatureKernel G (fun l => R l x) ^ k) i j) (B x))
    have hb := curvatureKernel_power_bound G hG (fun l => R l x)
      (fun l => hbound l x) k (A x) i j
    have h' := mul_le_mul_of_nonneg_right hb (norm_nonneg (B x))
    have ha : 2 * ‖A x‖ * ‖B x‖ ≤ ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖A x‖ - ‖B x‖)]
    have hm := mul_le_mul_of_nonneg_left ha hc
    change ‖A x * blockAt (curvatureKernel G (fun l => R l x) ^ k) i j‖ * ‖B x‖ ≤
      (c * ‖A x‖) * ‖B x‖ at h'
    nlinarith
  calc
    _ ≤ ∫ x, (c / 2) * (‖A x‖ ^ 2 + ‖B x‖ ^ 2) ∂μ :=
      integral_mono hi ((hia.add hib).const_mul _) hp
    _ = c * (15 / 2) := by
      rw [integral_const_mul, integral_add hia hib, hEA, hEB]
      ring

/-- At the exceptional energy three, all finite moments of order at least
two are bounded by five sixths of the scalar curvature-three moments. -/
theorem integral_trace_curvatureKernel_power_le {N : ℕ}
    (G : Matrix (Fin N) (Fin N) ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (R : Fin N → Ω → NormalMatrix) (hR : ∀ i, Continuous (R i))
    (hpos : ∀ i x, (R i x).PosSemidef ∧ (R i x).trace = 3)
    (hE : ∀ i, (∫ x, ‖R i x‖ ^ 2 ∂μ) = 15 / 2) (k : ℕ) :
    (∫ x, (curvatureKernel G (fun i => R i x) ^ (k + 2)).trace ∂μ) ≤
      (5 / 6 : ℝ) * 3 ^ (k + 2) * (G ^ (k + 2)).trace := by
  let F := fun i j l x =>
    (R j x * blockAt (curvatureKernel G (fun a => R a x) ^ k) j l * R i x).trace
  have hi (i j l : Fin N) : Integrable (F i j l) μ :=
    ((((hR j).mul (curvatureKernel_power_block_continuous G R hR k j l)).mul
      (hR i)).matrix_trace).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs (i j l : Fin N) : (∫ x, F i j l x ∂μ) ≤
      (3 ^ k * (G ^ k) j l) * (15 / 2) :=
    integral_trace_kernel_sandwich_le G hG R hR
      (fun a x => frobenius_le_three_of_posSemidef_trace (hpos a x).1 (hpos a x).2)
      k j l (R j) (R i) (hR j) (hR i) (hE j) (hE i)
  calc
    _ = ∫ x, ∑ i, ∑ j, ∑ l, (G i j * G l i) * F i j l x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => trace_curvatureKernel_power G _ k)
    _ = ∑ i, ∑ j, ∑ l, (G i j * G l i) * ∫ x, F i j l x ∂μ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
        integrable_finsetSum _ (fun l _ => (hi i j l).const_mul _)))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ =>
        integrable_finsetSum _ (fun l _ => (hi i j l).const_mul _))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun l _ => (hi i j l).const_mul _)]
      simp_rw [integral_const_mul]
    _ ≤ ∑ i, ∑ j, ∑ l, (G i j * G l i) *
        ((3 ^ k * (G ^ k) j l) * (15 / 2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      exact mul_le_mul_of_nonneg_left (hs i j l) (mul_nonneg (hG i j) (hG l i))
    _ = _ := by
      rw [scalar_power_trace_endpoints, pow_add]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      norm_num
      ring

end
end PositiveEinsteinFour.Jacobi

end OAI

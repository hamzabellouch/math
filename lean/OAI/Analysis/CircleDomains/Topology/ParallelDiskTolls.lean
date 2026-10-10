import OAI.Analysis.CircleDomains.Sobolev.SourceArea
import OAI.Analysis.CircleDomains.Modulus.FiniteGapPayment

namespace OAI

/-!
# Exact costs of round holes on parallel lines

The horizontal lines meeting a closed round disk form an interval of
length twice its radius. Integrating finitely many hole tolls therefore
gives exactly the radius-weighted sum. Disjointness and a common containing
disk bound this sum by the square norm of the oscillation tolls.
-/

open Set Function Metric MeasureTheory

namespace CircleDomainRigidity

theorem horizontal_line_meets_closedBall (c : ℂ) {r y : ℝ} :
    (∃ x : ℝ, (⟨x, y⟩ : ℂ) ∈ closedBall c r) ↔ y ∈ Icc (c.im - r) (c.im + r) := by
  constructor
  · rintro ⟨x, hx⟩
    have hb : |y - c.im| ≤ r := by
      have hx' : ‖(⟨x, y⟩ : ℂ) - c‖ ≤ r := by
        simpa only [mem_closedBall, dist_eq_norm] using hx
      exact (Complex.abs_im_le_norm ((⟨x, y⟩ : ℂ) - c)).trans hx'
    exact ⟨by linarith [(abs_le.mp hb).1], by linarith [(abs_le.mp hb).2]⟩
  · intro hy
    refine ⟨c.re, ?_⟩
    have heq : dist (⟨c.re, y⟩ : ℂ) c = |y - c.im| := by
      rw [dist_eq_norm, ← Complex.abs_im_eq_norm.mpr (by simp)]
      rfl
    rw [mem_closedBall, heq]
    exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem integral_parallel_disk_tolls
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) (hr : ∀ i, 0 ≤ r i) :
    (∫ y : ℝ, ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) =
      ∑ i, 2 * r i * A i := by
  have hi (i : I) : Integrable
      ((Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator_const _ measurableSet_Icc]
  simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
  rw [ENNReal.toReal_ofReal (by linarith [hr i])]
  ring

theorem real_volume_closedBall (c : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (closedBall c r)).toReal = Real.pi * r ^ 2 := by
  simpa only [Complex.volume_closedBall, Complex.volume_ball] using real_volume_ball c hr

theorem sum_radii_sq_le_of_disjoint_closed_disks
    {I : Type*} [Fintype I] (c : I → ℂ) (r : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L) :
    ∑ i, r i ^ 2 ≤ L ^ 2 := by
  have hm : (∑' i, volume (closedBall (c i) (r i))) ≤ volume (closedBall (0 : ℂ) L) := by
    rw [← measure_iUnion hdisj (fun _ => measurableSet_closedBall)]
    exact measure_mono (iUnion_subset hsub)
  have hreal := ENNReal.toReal_mono measure_closedBall_lt_top.ne hm
  rw [ENNReal.tsum_toReal_eq (fun _ => measure_closedBall_lt_top.ne), tsum_fintype] at hreal
  simp_rw [real_volume_closedBall _ (hr _)] at hreal
  rw [real_volume_closedBall 0 hL, ← Finset.mul_sum] at hreal
  exact (mul_le_mul_iff_right₀ Real.pi_pos).mp hreal

theorem parallel_disk_tolls_le_square_norm
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) {L : ℝ}
    (hr : ∀ i, 0 ≤ r i) (hL : 0 ≤ L)
    (hdisj : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hsub : ∀ i, closedBall (c i) (r i) ⊆ closedBall 0 L) :
    (∫ y : ℝ, ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) ≤
      2 * L * Real.sqrt (∑ i, A i ^ 2) := by
  rw [integral_parallel_disk_tolls c r A hr]
  have hs : Real.sqrt (∑ i, r i ^ 2) ≤ L := by
    simpa only [Real.sqrt_sq hL] using Real.sqrt_le_sqrt
      (sum_radii_sq_le_of_disjoint_closed_disks c r hr hL hdisj hsub)
  calc
    _ = 2 * ∑ i, r i * A i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 2 * (Real.sqrt (∑ i, r i ^ 2) * Real.sqrt (∑ i, A i ^ 2)) :=
      mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt Finset.univ r A) (by norm_num)
    _ ≤ 2 * (L * Real.sqrt (∑ i, A i ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)) (by norm_num)
    _ = _ := by ring

end CircleDomainRigidity

end OAI

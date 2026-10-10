import Mathlib

namespace OAI

noncomputable section

section
open Set Metric Filter TopologicalSpace MeasureTheory Function
open scoped Classical BigOperators Topology Cardinal ENNReal NNReal

namespace SeparableQuotient.Positive.Rows
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]



lemma ball_subset_closure_image_of_adjoint_lower (T : X →L[ℝ] Y) {c : ℝ}
    (hlower : ∀ f : StrongDual ℝ Y, c * ‖f‖ ≤ ‖f.comp T‖) :
    closedBall (0 : Y) c ⊆ closure (T '' closedBall (0 : X) 1) := by
  intro y hy
  by_contra hn
  have hconv : Convex ℝ (closure (T '' closedBall (0 : X) 1)) :=
    ((convex_closedBall (0 : X) 1).linear_image T.toLinearMap).closure
  obtain ⟨f, a, hsep, hay⟩ := geometric_hahn_banach_closed_point hconv isClosed_closure hn
  have ha : 0 < a := by
    simpa using hsep 0 (subset_closure ⟨0, by simp, by simp⟩)
  have hT : ‖f.comp T‖ ≤ a := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm ha.le
    intro x hx
    apply abs_le.mpr
    constructor
    · have hh := hsep (T (-x)) (subset_closure ⟨-x, by simp [hx], rfl⟩)
      simp only [map_neg] at hh
      change -a ≤ f (T x)
      linarith
    · exact (hsep (T x) (subset_closure ⟨x, by simp [hx], rfl⟩)).le
  have hy' : ‖y‖ ≤ c := by simpa using hy
  have hfy : f y ≤ ‖f‖ * c :=
    (le_abs_self _).trans ((f.le_opNorm y).trans (mul_le_mul_of_nonneg_left hy' (norm_nonneg _)))
  have hh := hlower f
  nlinarith

lemma approx_preimage_of_adjoint_lower (T : X →L[ℝ] Y) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ f : StrongDual ℝ Y, c * ‖f‖ ≤ ‖f.comp T‖) (z : Y) :
    ∃ x : X, dist (T x) z ≤ 1 / 2 * ‖z‖ ∧ ‖x‖ ≤ c⁻¹ * ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz], by simp [hz]⟩
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let r : ℝ := ‖z‖ / c
  have hr : 0 < r := div_pos hzn hc
  let y : Y := r⁻¹ • z
  have hy : y ∈ closedBall (0 : Y) c := by
    rw [mem_closedBall_zero_iff]
    change ‖r⁻¹ • z‖ ≤ c
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hr]
    dsimp [r]
    field_simp
    linarith
  have hyr : r • y = z := by simp [y, smul_smul, hr.ne']
  obtain ⟨w, ⟨x, hx, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp
    (ball_subset_closure_image_of_adjoint_lower T hlower hy) (c / 2) (by positivity)
  refine ⟨r • x, ?_, ?_⟩
  · have heq : dist (T (r • x)) z = r * dist (T x) y := by
      rw [← hyr, map_smul, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
        abs_of_pos hr, dist_eq_norm]
    rw [heq]
    calc
      r * dist (T x) y ≤ r * (c / 2) := mul_le_mul_of_nonneg_left (by simpa [dist_comm] using hdist.le) hr.le
      _ = 1 / 2 * ‖z‖ := by dsimp [r]; field_simp
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc
      r * ‖x‖ ≤ r * 1 := mul_le_mul_of_nonneg_left (by simpa using hx) hr.le
      _ = c⁻¹ * ‖z‖ := by dsimp [r]; ring



theorem surjective_of_adjoint_lower [CompleteSpace X] (T : X →L[ℝ] Y) {c : ℝ}
    (hc : 0 < c) (hlower : ∀ f : StrongDual ℝ Y, c * ‖f‖ ≤ ‖f.comp T‖) :
    ∀ z : Y, ∃ x : X, T x = z ∧ ‖x‖ ≤ (2 / c) * ‖z‖ := by
  choose g hg using approx_preimage_of_adjoint_lower T hc hlower
  let h (y : Y) := y - T (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  intro y
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [Function.iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let u (n : ℕ) := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (c⁻¹ * ‖y‖) := fun n => by
    apply le_trans (hg _).2
    calc
      c⁻¹ * ‖h^[n] y‖ ≤ c⁻¹ * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (c⁻¹ * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ summable_geometric_two
  have su : Summable u := sNu.of_norm
  let x := ∑' n, u n
  have hx : ‖x‖ ≤ (2 / c) * ‖y‖ := calc
    ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm sNu
    _ ≤ ∑' n, (1 / 2) ^ n * (c⁻¹ * ‖y‖) :=
      sNu.tsum_le_tsum ule (Summable.mul_right _ summable_geometric_two)
    _ = (∑' n : ℕ, (1 / 2 : ℝ) ^ n) * (c⁻¹ * ‖y‖) := tsum_mul_right
    _ = (2 / c) * ‖y‖ := by rw [tsum_geometric_two]; ring
  have heq : ∀ n : ℕ, T (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n IH => rw [Finset.sum_range_succ, map_add, IH, Function.iterate_succ_apply', sub_add]
  have hl₁ : Tendsto (fun n => T (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (T x)) :=
    (T.continuous.tendsto x).comp su.hasSum.tendsto_sum_nat
  simp only [heq] at hl₁
  have hl₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    exact (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).mul tendsto_const_nhds
  exact ⟨x, by simpa using tendsto_nhds_unique hl₁ hl₂, hx⟩
end SeparableQuotient.Positive.Rows

end

end

end OAI

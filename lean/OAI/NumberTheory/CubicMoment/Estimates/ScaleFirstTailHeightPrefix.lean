import OAI.NumberTheory.CubicMoment.Estimates.HeightWindowCount

namespace OAI

/-! An initial segment of the geometric height windows is exactly the
difference of two aligned full tails. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma heightWindowCount_shift {H T : ℝ} (hH : 0 < H) (hT : 0 < T) (j : ℕ) :
    heightWindowCount H (T*(3/2:ℝ)^j) = heightWindowCount H T-j := by
  have hr : 0 < Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have hB : 0 < 2*Real.pi*H := by positivity
  have hp : 0 < (3/2:ℝ)^j := by positivity
  have he : Real.log ((2*Real.pi*H)/(T*(3/2:ℝ)^j))/Real.log (3/2:ℝ) =
      Real.log ((2*Real.pi*H)/T)/Real.log (3/2:ℝ)-(j:ℝ) := by
    rw [Real.log_div hB.ne' (mul_pos hT hp).ne', Real.log_mul hT.ne' hp.ne',
      Real.log_pow,Real.log_div hB.ne' hT.ne']
    field_simp
    ring
  unfold heightWindowCount
  rw [he,Nat.ceil_sub_natCast]

lemma geometricHeight_prefix (f : ℝ → ℂ) {H T : ℝ} (hH : 0 < H) (hT : 0 < T)
    {j : ℕ} (hj : j ≤ heightWindowCount H T) :
    (∑ s ∈ Finset.range j, f (T*(3/2:ℝ)^s)) =
      (∑ s ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^s))-
        ∑ s ∈ Finset.range (heightWindowCount H (T*(3/2:ℝ)^j)),
          f ((T*(3/2:ℝ)^j)*(3/2:ℝ)^s) := by
  rw [heightWindowCount_shift hH hT j]
  apply (eq_sub_iff_add_eq).mpr
  calc
    _ = (∑ s ∈ Finset.range j, f (T*(3/2:ℝ)^s))+
        ∑ s ∈ Finset.range (heightWindowCount H T-j), f (T*(3/2:ℝ)^(j+s)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      rw [pow_add]
      ring
    _ = _ := by
      simpa only [Nat.add_sub_of_le hj] using
        (Finset.sum_range_add (fun s => f (T*(3/2:ℝ)^s)) j
          (heightWindowCount H T-j)).symm

lemma initial_filter_range {p : ℕ → Prop} [DecidablePred p]
    (hp : ∀ {i j}, i ≤ j → p j → p i) (N : ℕ) :
    ∃ j ≤ N, (Finset.range N).filter p = Finset.range j := by
  induction N with
  | zero => exact ⟨0,le_rfl,by simp⟩
  | succ N ih =>
    by_cases hN : p N
    · refine ⟨N+1,le_rfl,Finset.filter_eq_self.mpr ?_⟩
      intro i hi
      exact hp (by have := Finset.mem_range.mp hi; omega) hN
    · obtain ⟨j,hj,he⟩ := ih
      refine ⟨j,hj.trans (Nat.le_succ N),?_⟩
      rw [Finset.range_add_one,Finset.filter_insert]
      simp only [hN,ite_false,he]

lemma geometricHeight_filtered_prefix (f : ℝ → ℂ) {H T : ℝ}
    (hH : 0 < H) (hT : 0 < T) (V : ℝ) :
    ∃ j ≤ heightWindowCount H T,
      (∑ s ∈ Finset.range (heightWindowCount H T),
        if T*(3/2:ℝ)^s ≤ V then f (T*(3/2:ℝ)^s) else 0) =
        (∑ s ∈ Finset.range (heightWindowCount H T), f (T*(3/2:ℝ)^s))-
          ∑ s ∈ Finset.range (heightWindowCount H (T*(3/2:ℝ)^j)),
            f ((T*(3/2:ℝ)^j)*(3/2:ℝ)^s) := by
  obtain ⟨j,hj,he⟩ := initial_filter_range (p := fun s => T*(3/2:ℝ)^s ≤ V)
    (fun {i j} hij hV =>
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 3/2) hij) hT.le).trans hV)
    (heightWindowCount H T)
  refine ⟨j,hj,?_⟩
  calc
    _ = ∑ s ∈ (Finset.range (heightWindowCount H T)).filter
        (fun s => T*(3/2:ℝ)^s ≤ V), f (T*(3/2:ℝ)^s) := (Finset.sum_filter _ _).symm
    _ = ∑ s ∈ Finset.range j, f (T*(3/2:ℝ)^s) := by rw [he]
    _ = _ := geometricHeight_prefix f hH hT hj

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Estimates.PartitionMoment

namespace OAI

/-! A fixed finite linear combination preserves a positive moment saving. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_positive_lower_bound {κ : Type*} [Fintype κ] (e : κ → ℝ)
    (he : ∀ k, 0 < e k) : ∃ d : ℝ, 0 < d ∧ ∀ k, d ≤ e k := by
  classical
  have h : ∀ S : Finset κ, ∃ d : ℝ, 0 < d ∧ ∀ k ∈ S, d ≤ e k := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert k S hk ih =>
      obtain ⟨d,hd,hde⟩ := ih
      refine ⟨min d (e k),lt_min hd (he k),?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hde j hj)
  obtain ⟨d,hd,hde⟩ := h Finset.univ
  exact ⟨d,hd,fun k => hde k (Finset.mem_univ k)⟩

theorem finite_weighted_moment_saving {κ : Type*} [Fintype κ]
    (e : κ → ℝ) (he : ∀ k, 0 < e k) (c : κ → ℂ) :
    ∃ d : ℝ, 0 < d ∧ ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y →
      ∀ (ρ : Type*) [Fintype ρ] (f : κ → ρ → ℂ),
      (∀ k, (∑ r, ‖f k r‖^2) ≤ Y^(7/3-e k)) →
      (∑ r, ‖∑ k, c k*f k r‖^2) ≤ Y^(7/3-d) := by
  obtain ⟨d,hd,hde⟩ := finite_positive_lower_bound e he
  let C : ℝ := (Fintype.card κ)*(∑ k, ‖c k‖^2)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < d/2 by linarith)).eventually_ge_atTop C)
  refine ⟨d/2,by positivity,max 1 T,le_max_left _ _,?_⟩
  intro Y hY ρ _ f hf
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hf' (k : κ) : (∑ r, ‖f k r‖^2) ≤ Y^(7/3-d) :=
    (hf k).trans (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith [hde k]))
  calc
    _ ≤ (Fintype.card κ:ℝ)*(∑ k, ∑ r, ‖c k*f k r‖^2) :=
      finite_piece_moment (fun k r => c k*f k r)
    _ = (Fintype.card κ:ℝ)*(∑ k, ‖c k‖^2*(∑ r, ‖f k r‖^2)) := by
      simp_rw [norm_mul,mul_pow,← Finset.mul_sum]
    _ ≤ (Fintype.card κ:ℝ)*(∑ k, ‖c k‖^2*Y^(7/3-d)) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hf' k) (sq_nonneg _)))
        (Nat.cast_nonneg _)
    _ = C*Y^(7/3-d) := by rw [← Finset.sum_mul]; dsimp [C]; ring
    _ ≤ Y^(d/2)*Y^(7/3-d) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI

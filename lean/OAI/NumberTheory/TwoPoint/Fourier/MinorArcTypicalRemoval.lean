import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalDensity
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTTypicalCoarse
import OAI.NumberTheory.TwoPoint.Bounds.SmoothWindowSum

namespace OAI

/-! Removing the typical-set restriction costs its actual missing density.
This comparison is uniform in the additive frequency and pays the discarded
integers once, before either the major- or minor-arc estimate is applied. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma minor_arc_typical_pointwise_error {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    {n : ℕ} (hn : 0 < n) :
    ‖F n - mrtTypicalCoefficient J P F n‖ ≤
      if ¬mrtTypical J P n then (1 : ℝ) else 0 := by
  unfold mrtTypicalCoefficient
  by_cases h : mrtTypical J P n
  · simp [h]
  · simpa [h] using hF n hn

lemma minor_arc_typical_error_sum {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    (X H : ℕ) (α : ℝ) :
    shortExponentialIntegral F X H α ≤
      shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α +
        (H : ℝ) * ∑ n ∈ range (X + H),
          if ¬mrtTypical J P (n + 1) then (1 : ℝ) else 0 := by
  have herr := window_error_from_density F (mrtTypicalCoefficient J P F)
    (fun n => if ¬mrtTypical J P n then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> positivity)
    (fun n hn => minor_arc_typical_pointwise_error J P F hF hn) H X α
  simp only [shortExponentialIntegral_eq_sum, norm_shortExponentialSum_eq_window]
  calc
    _ ≤ ∑ v ∈ range X,
        (‖shortWindowSum (mrtTypicalCoefficient J P F) H α v‖ +
          ‖shortWindowSum F H α v -
            shortWindowSum (mrtTypicalCoefficient J P F) H α v‖) := by
      apply sum_le_sum
      intro v _
      calc
        _ = ‖shortWindowSum (mrtTypicalCoefficient J P F) H α v +
            (shortWindowSum F H α v -
              shortWindowSum (mrtTypicalCoefficient J P F) H α v)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by rw [sum_add_distrib]; exact add_le_add le_rfl herr

lemma minor_arc_typical_density_sum {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (N : ℕ) [NeZero N] :
    (∑ n ∈ range N, if ¬mrtTypical J P (n + 1) then (1 : ℝ) else 0) =
      (N : ℝ) * (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical J P (1 + n.val)) := by
  unfold FiniteLaw.probability FiniteLaw.average uniformFiniteLaw
  dsimp only
  rw [← mul_sum, Fintype.card_fin, ← mul_assoc]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [mul_one_div_cancel hN, one_mul]
  symm
  apply sum_bij (fun n _ => n.val)
  · intro n _
    exact mem_range.mpr n.isLt
  · intro n _ m _ he
    exact Fin.ext he
  · intro n hn
    exact ⟨⟨n, mem_range.mp hn⟩, mem_univ _, rfl⟩
  · intro n _
    simp only [Nat.add_comm 1]

theorem minor_arc_remove_typical {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    (X H : ℕ) [NeZero (X + H)] (α δ : ℝ)
    (hdensity : (uniformFiniteLaw (Fin (X + H))).probability
      (fun n => ¬mrtTypical J P (1 + n.val)) ≤ δ) :
    shortExponentialIntegral F X H α ≤
      shortExponentialIntegral (mrtTypicalCoefficient J P F) X H α +
        (H : ℝ) * (X + H) * δ := by
  apply (minor_arc_typical_error_sum J P F hF X H α).trans
  rw [minor_arc_typical_density_sum]
  apply add_le_add le_rfl
  calc
    _ ≤ (H : ℝ) * ((X + H : ℕ) * δ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdensity (Nat.cast_nonneg _)) (Nat.cast_nonneg H)
    _ = _ := by push_cast; ring

end TwoPointCorrelations

end OAI

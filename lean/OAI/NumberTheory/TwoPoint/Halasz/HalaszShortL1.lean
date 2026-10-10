import OAI.NumberTheory.TwoPoint.Halasz.HalaszShortTransfer
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcTypicalRemoval

namespace OAI

/-! The typical-set error is linear in its density in the published L1
norm. No square root of the discarded density is introduced. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_short_integral_cells (F : ℕ → ℂ) (A N H : ℕ) (α : ℝ) :
    (∫ x in (A:ℝ)..(A+N:ℕ), ‖shortExponentialSum F H α x‖) =
      ∑ v ∈ range N, ‖shortExponentialSum F H α (A+v:ℕ)‖ := by
  symm
  calc
    _ = ∑ v ∈ range N, ∫ x in (A+v:ℕ)..(A+v+1:ℕ),
        ‖shortExponentialSum F H α x‖ := by
      apply sum_congr rfl
      intro v _
      simpa only [Nat.cast_add, Nat.cast_one] using
        (integral_shortExponentialSum_unit F H α (A+v)).symm
    _ = _ := by
      simpa only [Nat.add_zero, Nat.add_assoc] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun n : ℕ => ((A+n:ℕ):ℝ)) (n := N)
          (fun v _ => by simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one, add_assoc] using
            shortExponentialSum_unit_integrable F H α (A+v)))

lemma halasz_window_shift (F : ℕ → ℂ) (A H v : ℕ) (α : ℝ) :
    shortWindowSum (fun n => F (A+n)) H α v = shortWindowSum F H α (A+v) := by
  simp only [shortWindowSum, Nat.add_assoc]

lemma halasz_translated_bad_count {ι : Type*} (J : Finset ι) (P : ι → Finset ℕ)
    (A N : ℕ) [NeZero N] :
    (∑ n ∈ range N, if ¬mrtTypical J P (A+n+1) then (1:ℝ) else 0) =
      (N:ℝ) * (uniformFiniteLaw (Fin N)).probability
        (fun n => ¬mrtTypical J P (A+1+n.val)) := by
  unfold FiniteLaw.probability FiniteLaw.average uniformFiniteLaw
  dsimp only
  rw [← mul_sum, Fintype.card_fin, ← mul_assoc]
  have hN : (N:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
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
    simp only [Nat.add_right_comm A 1 n.val]

theorem halasz_typical_short_L1 {ι : Type*} (J : Finset ι)
    (P : ι → Finset ℕ) (F : ℕ → ℂ) (hF : OneBounded F)
    (A N H : ℕ) [NeZero (N+H)] (α δ : ℝ)
    (hδ : (uniformFiniteLaw (Fin (N+H))).probability
      (fun n => ¬mrtTypical J P (A+1+n.val)) ≤ δ) :
    (∫ x in (A:ℝ)..(A+N:ℕ), ‖shortExponentialSum F H α x‖) ≤
      (∫ x in (A:ℝ)..(A+N:ℕ),
        ‖shortExponentialSum (mrtTypicalCoefficient J P F) H α x‖) +
        (H:ℝ)*(N+H)*δ := by
  let G := mrtTypicalCoefficient J P F
  have herr := window_error_from_density (fun n => F (A+n)) (fun n => G (A+n))
    (fun n => if ¬mrtTypical J P (A+n) then (1:ℝ) else 0)
    (fun _ => by split_ifs <;> positivity)
    (fun n hn => minor_arc_typical_pointwise_error J P F hF (by omega)) H N α
  simp only [halasz_window_shift] at herr
  have hcount := halasz_translated_bad_count J P A (N+H)
  simp only [Nat.add_assoc] at hcount
  rw [hcount] at herr
  have herr' : (∑ v ∈ range N,
      ‖shortWindowSum F H α (A+v)-shortWindowSum G H α (A+v)‖) ≤
      (H:ℝ)*(N+H)*δ := by
    apply herr.trans
    have hs := mul_le_mul_of_nonneg_left hδ
      (show 0 ≤ (H:ℝ)*(N+H) by positivity)
    simpa only [mul_assoc, Nat.cast_add, Nat.add_assoc] using hs
  rw [halasz_short_integral_cells, halasz_short_integral_cells]
  simp_rw [norm_shortExponentialSum_eq_window]
  calc
    _ ≤ ∑ v ∈ range N, (‖shortWindowSum G H α (A+v)‖ +
        ‖shortWindowSum F H α (A+v)-shortWindowSum G H α (A+v)‖) := by
      apply sum_le_sum
      intro v _
      have hh := norm_add_le (shortWindowSum G H α (A+v))
        (shortWindowSum F H α (A+v)-shortWindowSum G H α (A+v))
      rw [add_sub_cancel] at hh
      exact hh
    _ ≤ _ := by rw [sum_add_distrib]; exact add_le_add le_rfl herr'

end TwoPointCorrelations

end OAI

import OAI.NumberTheory.CubicMoment.Estimates.SmoothPartitionCount
import OAI.NumberTheory.CubicMoment.Estimates.MellinMomentTransfer

namespace OAI

/-! Summing the explicit smooth norm partition loses only a small part of
an established power saving. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_piece_moment {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (f : κ → ρ → ℂ) :
    (∑ r, ‖∑ k, f k r‖^2) ≤ (Fintype.card κ:ℝ)*(∑ k, ∑ r, ‖f k r‖^2) := by
  calc
    _ ≤ ∑ r, (Fintype.card κ:ℝ)*(∑ k, ‖f k r‖^2) := by
      apply Finset.sum_le_sum
      intro r _
      apply (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_sum_le _ _) 2).trans
      simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : κ => (1:ℝ))
        (fun k => ‖f k r‖)
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_partition_moment_power {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ Y : ℝ, T ≤ Y → ∀ (ρ : Type*) [Fintype ρ]
      (f : (ι → Fin (normPartitionCount (2*Y))) → ρ → ℂ),
      (∀ k, (∑ r, ‖f k r‖^2) ≤ Y^(7/3-ε)) →
      (∑ r, ‖∑ k, f k r‖^2) ≤ Y^(7/3-ε/2) := by
  obtain ⟨C,hC,hcount⟩ := normPartitionCount_power_bound (2*Fintype.card ι)
    (show 0 < ε/4 by linarith)
  let K : ℝ := C*2^(ε/4)
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < ε/4 by linarith)).eventually_ge_atTop K)
  refine ⟨max 1 T,le_max_left _ _,?_⟩
  intro Y hY ρ _ f hf
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hc : ((Fintype.card (ι → Fin (normPartitionCount (2*Y)))):ℝ)^2 ≤ K*Y^(ε/4) := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,← pow_mul]
    rw [Nat.mul_comm]
    apply (hcount (2*Y) (by linarith)).trans_eq
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hYp.le]
    dsimp [K]
    ring
  calc
    _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)*
        (∑ k, ∑ r, ‖f k r‖^2) := finite_piece_moment f
    _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)^2*Y^(7/3-ε) := by
      calc
        _ ≤ (Fintype.card (ι → Fin (normPartitionCount (2*Y))):ℝ)*
            (∑ _k : ι → Fin (normPartitionCount (2*Y)), Y^(7/3-ε)) := by
          apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hf k))
            (Nat.cast_nonneg _)
        _ = _ := by simp; ring
    _ ≤ (K*Y^(ε/4))*Y^(7/3-ε) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hYp.le _)
    _ = K*Y^(7/3-3*ε/4) := by
      rw [mul_assoc,← Real.rpow_add hYp,
        show ε/4+(7/3-ε) = 7/3-3*ε/4 by ring]
    _ ≤ Y^(ε/4)*Y^(7/3-3*ε/4) := mul_le_mul_of_nonneg_right
      (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; congr 1; ring

end CubicFirstMoment

end

end OAI

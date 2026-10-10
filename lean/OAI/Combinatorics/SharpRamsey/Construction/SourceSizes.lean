import Mathlib

namespace OAI

section
namespace SharpLogRamsey.InitialExperiment
open Real Filter
open scoped Topology
noncomputable section

lemma eventually_source_sizes (i : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    ∀ᶠ q : ℕ in atTop,
      3 ≤ q ∧ 1 ≤ log (q:ℝ) ∧
      0 < ⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊ ∧
      ⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊ ≤ ⌊(q:ℝ)^(i+3)*log (q:ℝ)⌋₊ ∧
      (⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊:ℝ) ≤ (q:ℝ)*(log (q:ℝ))^(1+η) ∧
      ((q:ℝ)*(log (q:ℝ))^(1+η))/2 ≤ (⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊:ℝ) ∧
      (⌊(q:ℝ)^(i+3)*log (q:ℝ)⌋₊:ℝ) ≤ (q:ℝ)^(i+3)*log (q:ℝ) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop η (by norm_num : (0:ℝ)<1)).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall,
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    eventually_ge_atTop (3:ℕ)] with q hsmall hl hq
  change 1 ≤ log (q:ℝ) at hl
  have hq1 : (1:ℝ) ≤ q:=by exact_mod_cast (show 1 ≤ q by omega)
  have hq2 : (2:ℝ) ≤ q:=by exact_mod_cast (show 2 ≤ q by omega)
  have hq0 : (0:ℝ) < q:=by linarith
  have hl0 : 0 < log (q:ℝ):=by linarith
  simp only [Real.norm_eq_abs,abs_of_pos (rpow_pos_of_pos hl0 _),
    rpow_one,abs_of_pos hq0,one_mul] at hsmall
  have hpow : 1 ≤ (log (q:ℝ))^(1+η):=one_le_rpow hl (by linarith)
  have hQ : 2 ≤ (q:ℝ)*(log (q:ℝ))^(1+η):=by nlinarith only [hpow,hq2]
  have hf : (⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊:ℝ)+1 > (q:ℝ)*(log (q:ℝ))^(1+η):=Nat.lt_floor_add_one _
  have hlower : ((q:ℝ)*(log (q:ℝ))^(1+η))/2 ≤ (⌊(q:ℝ)*(log (q:ℝ))^(1+η)⌋₊:ℝ):=by linarith
  refine ⟨hq,hl,?_,?_,Nat.floor_le (by positivity),hlower,Nat.floor_le (by positivity)⟩
  · exact (Nat.one_le_floor_iff _).mpr (by linarith)
  · apply Nat.floor_mono
    calc
      _ = (q:ℝ)*log (q:ℝ)*(log (q:ℝ))^η:=by rw [rpow_add hl0,rpow_one];ring
      _ ≤ (q:ℝ)*log (q:ℝ)*(q:ℝ):=mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = (q:ℝ)^2*log (q:ℝ):=by ring
      _ ≤ _:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq1 (by omega : 2 ≤ i+3)) hl0.le
end
end SharpLogRamsey.InitialExperiment

end

end OAI

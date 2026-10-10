import OAI.NumberTheory.JointDickman.Amplification.CanonicalTypicalDensity

namespace OAI

/-! # Maximal band selection below the square-root logarithmic cutoff -/
namespace JointDickman
open Finset Filter TwoPointCorrelations
open scoped Topology Classical

lemma exists_mellin_band_above (Q Y : ℝ) (hQ : 1 ≤ Real.log Q) :
    ∃ j : ℕ, Y < Real.log (mrtBandUpper Q (j+1)) := by
  obtain ⟨j, hj⟩ := exists_nat_gt Y
  refine ⟨j, hj.trans_le ?_⟩
  have hjs : (j : ℝ) ≤ (j+1 : ℕ) := by exact_mod_cast (show j ≤ j+1 by omega)
  exact hjs.trans (mrt_band_index_le_log_upper Q (j+1) (by omega) hQ)

noncomputable def mellinBandCount (Q Y : ℝ) (hQ : 1 ≤ Real.log Q) : ℕ :=
  Nat.find (exists_mellin_band_above Q Y hQ)

lemma mellinBandCount_next (Q Y : ℝ) (hQ : 1 ≤ Real.log Q) :
    Y < Real.log (mrtBandUpper Q (mellinBandCount Q Y hQ+1)) :=
  Nat.find_spec (exists_mellin_band_above Q Y hQ)

lemma mellinBandCount_good (Q Y : ℝ) (hQ : 1 ≤ Real.log Q)
    {j : ℕ} (hj : j < mellinBandCount Q Y hQ) :
    mrtBandUpper Q (j+1) ≤ Real.exp Y := by
  have hh : ¬Y < Real.log (mrtBandUpper Q (j+1)) :=
    Nat.find_min (exists_mellin_band_above Q Y hQ) hj
  have hl := le_of_not_gt hh
  have hup : 0 < mrtBandUpper Q (j+1) := Real.exp_pos _
  calc
    _ = Real.exp (Real.log (mrtBandUpper Q (j+1))) := (Real.exp_log hup).symm
    _ ≤ _ := Real.exp_le_exp.mpr hl

lemma mellinBandCount_tendsto (Q : ℝ) (hQ : 1 ≤ Real.log Q) :
    Tendsto (fun Y => mellinBandCount Q Y hQ) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (Real.log (mrtBandUpper Q (b+1)))] with Y hY
  by_contra hnot
  have hb : mellinBandCount Q Y hQ+1 ≤ b+1 := by omega
  have hh := mrt_log_band_upper_mono hQ (by omega) hb
  linarith [mellinBandCount_next Q Y hQ]

lemma twice_exp_sqrt_log_le {X : ℝ} (hX : 0 < X) (hL : 4 ≤ Real.log X) :
    2*Real.exp (Real.sqrt (Real.log X)) ≤ X := by
  have hs : Real.sqrt (Real.log X) ≤ Real.log X/2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor <;> nlinarith
  have h2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = Real.exp (Real.log 2 + Real.sqrt (Real.log X)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by linarith)
    _ = X := Real.exp_log hX

lemma selected_mellin_bands_fit (Q X : ℝ) (hQ : 1 ≤ Real.log Q)
    (hX : 0 < X) (hL : 4 ≤ Real.log X) :
    ∀ j ∈ range (mellinBandCount Q (Real.sqrt (Real.log X)) hQ),
      2*mrtBandUpper Q (j+1) ≤ X := by
  intro j hj
  exact (mul_le_mul_of_nonneg_left
    (mellinBandCount_good Q _ hQ (mem_range.mp hj)) (by norm_num)).trans
    (twice_exp_sqrt_log_le hX hL)

lemma selected_mellin_bands_sieve (Q X : ℝ) (hQ : 1 ≤ Real.log Q)
    (hL : 1 ≤ Real.log X) :
    ∀ j ∈ range (mellinBandCount Q (Real.sqrt (Real.log X)) hQ),
      mrtBandUpper Q (j+1) ≤ Real.exp ((Real.log X)^(99/100 : ℝ)) := by
  intro j hj
  apply (mellinBandCount_good Q _ hQ (mem_range.mp hj)).trans
  apply Real.exp_le_exp.mpr
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

theorem selected_mellin_count : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ X : ℝ in atTop, ∀ P Q η : ℝ, 2 ≤ P → P ≤ Q →
      ∀ hQ : 1 ≤ Real.log Q,
      (((range (⌊3*X⌋₊+1)).filter fun n =>
        ¬mrtTypical (range (mellinBandCount Q (Real.sqrt (Real.log X)) hQ))
          (canonicalMellinBands P Q η).primes n).card : ℝ) / X ≤ C*Real.log P/Real.log Q := by
  obtain ⟨C, hC, hbound⟩ := canonical_typical_prefix_count
  refine ⟨C, hC, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hbound,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 4),
    eventually_ge_atTop (1 : ℝ)] with X hbound hL hX
  intro P Q η hP hPQ hQ
  apply hbound P Q η X _ hP hPQ hQ hX (selected_mellin_bands_sieve Q X hQ (by linarith))
  have hX0 : 0 < X := by linarith
  have hr : (Real.log X)^(199/200 : ℝ) ≤ Real.log X :=
    Real.rpow_le_self_of_one_le (by linarith) (by norm_num)
  have he := Real.exp_le_exp.mpr hr
  rw [Real.exp_log hX0] at he
  linarith

end JointDickman

end OAI

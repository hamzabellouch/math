import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedGramConstants

namespace OAI

/-! A fixed logarithmic spacing controls the total leakage for every
polynomial number of sites. The exponent is chosen once for the reduction. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

def localLeakageConstant (freq : ℝ) : ℝ :=
  localizedTailConstant freq * Real.exp 2 * (∫ x : Position, |localDualBump x|)

theorem localLeakageConstant_nonnegative (freq : ℝ) : 0 ≤ localLeakageConstant freq :=
  mul_nonneg (mul_nonneg (localizedTailConstant_nonnegative freq) (Real.exp_pos _).le)
    (integral_nonneg (fun _ => abs_nonneg _))

theorem localLeakageBound_log (freq : ℝ) (k : ℕ) {N : ℝ} (hN : 0 < N) :
    localLeakageBound freq ((k : ℝ) * Real.log N) = localLeakageConstant freq / N ^ k := by
  unfold localLeakageBound localLeakageConstant
  rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hN]
  ring

theorem exists_localizedGram_spacing {freq : ℝ} (hfreq : 0 < freq) (A : ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      5 ≤ (k : ℝ) * Real.log N ∧
      N ^ A * localLeakageBound freq ((k : ℝ) * Real.log N) ≤ localDualMass freq / 2 := by
  let C := localLeakageConstant freq
  let a := localDualMass freq
  have ha : 0 < a := localDualMass_positive hfreq
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨q, hq⟩ := exists_nat_ge (max (5 / Real.log 2) (2 * C / a))
  have hqD : 5 / Real.log 2 ≤ (q : ℝ) := (le_max_left _ _).trans hq
  have hqC : 2 * C / a ≤ (q : ℝ) := (le_max_right _ _).trans hq
  have hqpos : (0 : ℝ) < q := (div_pos (by norm_num) hlog).trans_le hqD
  have hqNat : 0 < q := by exact_mod_cast hqpos
  have hpow : (q : ℝ) ≤ (2 : ℝ) ^ q := by exact_mod_cast (Nat.lt_two_pow_self (n := q)).le
  refine ⟨A + q, by omega, fun N hN => ?_⟩
  have hNp : 0 < N := by linarith
  have hlogN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN
  have hD := (div_le_iff₀ hlog).mp hqD
  have hqN : (2 : ℝ) ^ q ≤ N ^ q := pow_le_pow_left₀ (by norm_num) hN q
  have hC : 2 * C ≤ a * N ^ q := by
    have h := (div_le_iff₀ ha).mp (hqC.trans (hpow.trans hqN))
    nlinarith only [h]
  constructor
  · have h := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg q)
    have hadd := mul_nonneg (Nat.cast_nonneg A) (Real.log_nonneg (by linarith : 1 ≤ N))
    push_cast
    nlinarith only [hD, h, hadd]
  · rw [localLeakageBound_log freq (A + q) hNp, pow_add]
    have hcancel : N ^ A * (C / (N ^ A * N ^ q)) = C / N ^ q := by
      field_simp [pow_ne_zero A hNp.ne', pow_ne_zero q hNp.ne']
    change N ^ A * (C / (N ^ A * N ^ q)) ≤ a / 2
    rw [hcancel]
    apply (div_le_iff₀ (pow_pos hNp q)).mpr
    nlinarith only [hC]

theorem exists_uniform_localizedGram_coercivity {freq : ℝ} (hfreq : 0 < freq) (A : ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∀ (N : ℝ), 2 ≤ N → ∀ (m : ℕ), (m : ℝ) ≤ N ^ A →
      ∀ (u : Fin m → PlanarPosition),
        (∀ i j, i ≠ j → (k : ℝ) * Real.log N ≤ ‖u i - u j‖) → ∀ d : Fin m → ℝ,
          localizedGramConstant freq * ∑ i, d i ^ 2 ≤
            ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j := by
  obtain ⟨k, hk, hspacing⟩ := exists_localizedGram_spacing hfreq A
  refine ⟨k, hk, fun N hN m hm u hsep d => ?_⟩
  obtain ⟨hD, hleak⟩ := hspacing N hN
  exact localizedGram_uniform_coercive hfreq hD u hsep
    ((mul_le_mul_of_nonneg_right hm (localLeakageBound_nonnegative _ _)).trans hleak) d

end ContinuumCoulomb

end

end OAI

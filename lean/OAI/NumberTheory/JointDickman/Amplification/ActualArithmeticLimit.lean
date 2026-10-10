import OAI.NumberTheory.JointDickman.Amplification.ActualArithmeticMean

namespace OAI

/-! # Uniform decay of the arithmetic candidate root fluctuations -/

namespace JointDickman
open Filter
open scoped Topology

noncomputable def arithmeticFluctuationError (K : ℝ) (B : ℕ) : ℝ :=
  K*(B : ℝ)^(-(7/200 : ℝ))+(B : ℝ)^10*conditionedRootError B+
    coefficientRootError B+10*(B : ℝ)^19/(auxiliaryCutoff B : ℝ)+4/(B : ℝ)

theorem arithmeticFluctuationError_tendsto (K : ℝ) :
    Tendsto (arithmeticFluctuationError K) atTop (𝓝 0) := by
  have hr := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 7/200)).comp
    tendsto_natCast_atTop_atTop
  have hp := (polynomial_div_primeCutoff_tendsto_zero (k := 19) (by norm_num)).comp
    tendsto_natCast_atTop_atTop
  have hp' : Tendsto (fun B : ℕ => (B : ℝ)^19/(auxiliaryCutoff B : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,auxiliaryCutoff,Nat.cast_pow] using hp
  have hi : Tendsto (fun B : ℕ => 4/(B : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have ht := ((((hr.const_mul K).add conditionedRootError_weighted_tendsto).add
    coefficientRootError_tendsto).add (hp'.const_mul 10)).add hi
  simp only [mul_zero,add_zero] at ht
  convert ht using 1
  funext B
  unfold arithmeticFluctuationError
  simp only [Function.comp_def]
  ring

theorem forced_cost_polynomial {B M : ℕ} (hB : 2 ≤ B) (hM : M ≤ B^2) :
    (B : ℝ)^10*(5*(M : ℝ)^3*(B : ℝ)^3/(Real.log 2*auxiliaryCutoff B)) ≤
      10*(B : ℝ)^19/(auxiliaryCutoff B : ℝ) := by
  have hP : (0 : ℝ) < auxiliaryCutoff B := by
    exact_mod_cast (show 0 < auxiliaryCutoff B from pow_pos (by omega) _)
  have hMr : (M : ℝ) ≤ (B : ℝ)^2 := by exact_mod_cast hM
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by have h := Real.log_two_gt_d9; linarith
  have hinv : 1/(Real.log 2*auxiliaryCutoff B) ≤ 2/(auxiliaryCutoff B : ℝ) := by
    have hh : (auxiliaryCutoff B : ℝ)/2 ≤ Real.log 2*auxiliaryCutoff B := by nlinarith
    exact (one_div_le_one_div_of_le (by positivity) hh).trans_eq (by ring)
  calc
    _ = 5*(B : ℝ)^10*(M : ℝ)^3*(B : ℝ)^3*(1/(Real.log 2*auxiliaryCutoff B)) := by ring
    _ ≤ 5*(B : ℝ)^10*((B : ℝ)^2)^3*(B : ℝ)^3*(2/(auxiliaryCutoff B : ℝ)) := by gcongr
    _ = _ := by ring

theorem actual_arithmetic_fluctuation_decay
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
        0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
        ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
          arithmeticSquareMean B (actualCandidateCutError B L T H M τ C χ) ≤ E B := by
  obtain ⟨K,_,hbound⟩ := actual_arithmetic_fluctuation_bound hFord hMertens hL hτ hτsmall
  refine ⟨arithmeticFluctuationError K,arithmeticFluctuationError_tendsto K,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 2] with B hbound hB
  intro C T H M hT hTs hTP hM0 hM hMexp χ hχ
  exact (hbound C T H M hT hTs hTP hM0 hM hMexp χ hχ).trans
    (by unfold arithmeticFluctuationError; linarith only [forced_cost_polynomial hB hM])

end JointDickman

end OAI

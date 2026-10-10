import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.TargetHubbardParameters
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedGramSpacing

namespace OAI

/-! Uniform finite-Hamiltonian bounds used before selecting the source
geometry and numerical precision. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem exists_target_hopping_exponent (freq : ℝ) (R A : ℕ) :
    ∃ v : ℕ, 1 ≤ v ∧ ∀ (N τ : ℝ), 2 ≤ N → 0 ≤ τ → τ ≤ 1 →
      ∀ {Edge : Type*} [Fintype Edge], (Fintype.card Edge : ℝ) ≤ N^R →
      ∀ (distance K : Edge → ℝ), (∀ e, 0 ≤ K e) → (∀ e, K e ≤ N^A) →
      (∑ e, |coulombHoppingTarget freq τ (K e) (distance e)|) ≤ N^v := by
  obtain ⟨q,hq,hconst⟩ := exists_polynomial_constant_bounds (by norm_num : (0:ℝ)<1)
    (Real.sqrt (localizedCoulombProfile freq 0))
  refine ⟨R+A+q,by omega,?_⟩
  intro N τ hN hτ hτ1 Edge _ hcard distance K hK hKhi
  have hN1 : 1 ≤ N := by linarith
  have hsqrt : Real.sqrt (N^A*localizedCoulombProfile freq 0) ≤ N^(A+q) := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ N^A),pow_add]
    apply mul_le_mul ?_ (hconst N hN).2 (Real.sqrt_nonneg _) (by positivity)
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith [one_le_pow₀ hN1 (n := A)]
  have hτsqrt : τ*Real.sqrt (N^A*localizedCoulombProfile freq 0) ≤ N^(A+q) :=
    (mul_le_mul_of_nonneg_right hτ1 (Real.sqrt_nonneg _)).trans (by simpa using hsqrt)
  have hcardmul := mul_le_mul hcard hτsqrt
    (mul_nonneg hτ (Real.sqrt_nonneg _)) (by positivity : (0:ℝ) ≤ N^R)
  rw [← pow_add] at hcardmul
  have ht := target_hopping_sum_bound freq τ (N^A) hτ distance K hK hKhi
  have h4 := mul_le_mul_of_nonneg_left hcardmul (by norm_num : (0:ℝ) ≤ 4)
  have he : R+(A+q)=R+A+q := by omega
  rw [he] at h4
  nlinarith only [ht,h4]

theorem localLeakageBound_antitone (freq : ℝ) {a b : ℝ} (hab : a ≤ b) :
    localLeakageBound freq b ≤ localLeakageBound freq a := by
  unfold localLeakageBound
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (localizedTailConstant_nonnegative freq))
    (MeasureTheory.integral_nonneg (fun _ => abs_nonneg _))

theorem exists_source_leakage_threshold {freq : ℝ} (hfreq : 0 < freq) (R : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ ∀ (k : ℕ), q ≤ k → ∀ (N D : ℝ), 2 ≤ N →
      25*(k:ℝ)*Real.log N ≤ D → ∀ M : ℕ, (M:ℝ) ≤ N^R →
      5 ≤ D ∧ (M:ℝ)*localLeakageBound freq D ≤ localDualMass freq/2 := by
  obtain ⟨q,hq,hspacing⟩ := exists_localizedGram_spacing hfreq R
  refine ⟨q,by omega,fun k hk N D hN hD M hM => ?_⟩
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hqk : (q:ℝ) ≤ 25*(k:ℝ) := by
    have hh : (q:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [Nat.cast_nonneg k (α := ℝ)]
  have hqd : (q:ℝ)*Real.log N ≤ D := (mul_le_mul_of_nonneg_right hqk hlog).trans hD
  obtain ⟨hfive,hleak⟩ := hspacing N hN
  refine ⟨hfive.trans hqd,?_⟩
  exact (mul_le_mul hM (localLeakageBound_antitone freq hqd)
    (localLeakageBound_nonnegative freq D) (by positivity)).trans hleak

end ContinuumCoulomb

end

end OAI

import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombGap
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarUniformCalibration

namespace OAI

/-! Uniform contact calibration for the actual Coulomb profile, with a
single polynomial scale also enforcing the many-site Gram bound. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

def coulombHoppingTarget (freq τ K d : ℝ) : ℝ :=
  τ * Real.sqrt (K * (localizedCoulombProfile freq 0 - localizedCoulombProfile freq d))

theorem coulombHoppingTarget_continuous {freq : ℝ} (hfreq : 0 < freq) (τ K : ℝ) :
    Continuous (coulombHoppingTarget freq τ K) :=
  continuous_const.mul ((continuous_const.mul
    (continuous_const.sub (localizedCoulombProfile_continuous hfreq))).sqrt)

theorem localizedCoulombProfile_nonnegative (freq d : ℝ) : 0 ≤ localizedCoulombProfile freq d := by
  unfold localizedCoulombProfile
  rw [localizedCoulombProfileAt_eq]
  exact localizedCoulombCoeff_nonnegative freq _ _

theorem coulombHoppingTarget_bounds {freq D τ K d : ℝ} (hfreq : 0 < freq) (hD : 5 ≤ D)
    (hleak : 2 * localLeakageBound freq D ≤ localDualMass freq / 2) (hd : D ≤ d)
    (hτ : 0 ≤ τ) (hK : 0 ≤ K) :
    τ * Real.sqrt (K * localizedGramConstant freq) ≤ coulombHoppingTarget freq τ K d ∧
      coulombHoppingTarget freq τ K d ≤ τ * Real.sqrt (K * localizedCoulombProfile freq 0) := by
  constructor
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (localizedCoulombProfile_gap hfreq hD hleak hd) hK)) hτ
  · exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left (sub_le_self _ (localizedCoulombProfile_nonnegative freq d)) hK)) hτ

theorem exists_uniform_coulomb_calibration {freq ε : ℝ} (hfreq : 0 < freq)
    (hε : 0 < ε) (hε₁ : ε < 1) (A S : ℕ) :
    ∃ k : ℕ, 0 < k ∧ ∀ N : ℝ, 2 ≤ N →
      5 ≤ (1 - ε) * ((k : ℝ) * Real.log N) ∧
      (∀ d : ℝ, (1 - ε) * ((k : ℝ) * Real.log N) ≤ d →
        localizedGramConstant freq ≤ localizedCoulombProfile freq 0 - localizedCoulombProfile freq d) ∧
      (∀ τ K : ℝ, 0 ≤ τ → 0 ≤ K →
        (N ^ A)⁻¹ ≤ τ * Real.sqrt (K * localizedGramConstant freq) →
        τ * Real.sqrt (K * localizedCoulombProfile freq 0) ≤ N ^ A →
        ∃ d ∈ Set.Icc ((1 - ε) * ((k : ℝ) * Real.log N))
          ((1 + ε) * ((k : ℝ) * Real.log N)), N ^ k * planarHopping d = coulombHoppingTarget freq τ K d) ∧
      (∀ (m : ℕ), (m : ℝ) ≤ N ^ S → ∀ (u : Fin m → PlanarPosition),
        (∀ i j, i ≠ j → (1 - ε) * ((k : ℝ) * Real.log N) ≤ ‖u i - u j‖) →
        ∀ d : Fin m → ℝ, localizedGramConstant freq * ∑ i, d i ^ 2 ≤
          ∑ i, ∑ j, localizedCoulombCoeff freq (u i) (u j) * d i * d j) := by
  obtain ⟨k₀, _, hspacing⟩ := exists_localizedGram_spacing hfreq (S + 1)
  obtain ⟨k, hk, hlarge, hcal⟩ :=
    exists_uniform_planar_calibration_above ((k₀ : ℝ) / (1 - ε)) A hε hε₁
  refine ⟨k, hk, fun N hN => ?_⟩
  have hNp : 0 < N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN₁
  have hlength : (k₀ : ℝ) * Real.log N ≤ (1 - ε) * ((k : ℝ) * Real.log N) := by
    have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ (sub_pos.mpr hε₁)).mp hlarge) hlog
    nlinarith only [h]
  obtain ⟨hD, hleak⟩ := hspacing N hN
  have hpow : N ^ S ≤ N ^ (S + 1) := pow_le_pow_right₀ hN₁ (Nat.le_succ S)
  have htwo : (2 : ℝ) ≤ N ^ (S + 1) := by
    exact hN.trans (by simpa only [pow_one] using pow_le_pow_right₀ hN₁ (show 1 ≤ S + 1 by omega))
  have hleak₂ : 2 * localLeakageBound freq ((k₀ : ℝ) * Real.log N) ≤ localDualMass freq / 2 :=
    (mul_le_mul_of_nonneg_right htwo (localLeakageBound_nonnegative _ _)).trans hleak
  refine ⟨hD.trans hlength, ?_, ?_, ?_⟩
  · intro d hd
    exact localizedCoulombProfile_gap hfreq hD hleak₂ (hlength.trans hd)
  · intro τ K hτ hK hlo hhi
    apply (hcal N hN).2 (coulombHoppingTarget freq τ K)
      (coulombHoppingTarget_continuous hfreq τ K).continuousOn
    intro d hd
    have hb := coulombHoppingTarget_bounds hfreq hD hleak₂ (hlength.trans hd.1) hτ hK
    exact ⟨hlo.trans hb.1, hb.2.trans hhi⟩
  · intro m hm u hsep d
    apply localizedGram_uniform_coercive hfreq hD u
      (fun i j hij => hlength.trans (hsep i j hij)) ?_ d
    exact (mul_le_mul_of_nonneg_right (hm.trans hpow) (localLeakageBound_nonnegative _ _)).trans hleak

theorem calibrated_superexchange {freq scale τ K d : ℝ} (hgap : 0 <
    localizedCoulombProfile freq 0 - localizedCoulombProfile freq d) (hK : 0 ≤ K)
    (hcal : scale * planarHopping d = coulombHoppingTarget freq τ K d) :
    (scale * planarHopping d) ^ 2 /
      (localizedCoulombProfile freq 0 - localizedCoulombProfile freq d) = τ ^ 2 * K := by
  rw [hcal, coulombHoppingTarget, mul_pow, Real.sq_sqrt (mul_nonneg hK hgap.le)]
  field_simp [hgap.ne']

end ContinuumCoulomb

end

end OAI

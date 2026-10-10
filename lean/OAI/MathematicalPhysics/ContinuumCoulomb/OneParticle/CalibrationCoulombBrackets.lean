import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationEndpointSigns
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombTargetRange

namespace OAI

/-! Explicit rational search intervals for the actual Coulomb-calibrated
hopping target. The fixed exponent simultaneously enforces the separated
two-site denominator and both endpoint signs. -/

noncomputable section
namespace ContinuumCoulomb.CalibrationRationalBracket

theorem exists_coulomb_brackets {freq : ℝ} (hfreq : 0 < freq)
    (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (A B : ℕ) (kmin : ℝ) :
    ∃ (c : ℚ) (k : ℕ), 0 < c ∧ 0 < k ∧ kmin ≤ (k : ℝ) ∧
      ∀ N : ℕ, 2 ≤ N →
        let D := (k : ℝ) * Real.log (N : ℝ)
        let p := endpoints ε (RationalLogScale.value c k N)
        (1 - (ε : ℝ)) * D ≤ p.1 ∧ p.2 ≤ (1 + (ε : ℝ)) * D ∧
          5 ≤ (1 - (ε : ℝ)) * D ∧
          (∀ r : ℝ, (p.1 : ℝ) ≤ r → localizedGramConstant freq ≤
            localizedCoulombProfile freq 0 - localizedCoulombProfile freq r) ∧
          (∀ K : ℚ, ((N : ℝ) ^ A)⁻¹ ≤ K → (K : ℝ) ≤ (N : ℝ) ^ A →
            0 ≤ (N : ℝ) ^ k * planarHopping p.1 -
              coulombHoppingTarget freq ((N : ℝ) ^ B)⁻¹ K p.1 ∧
            (N : ℝ) ^ k * planarHopping p.2 -
              coulombHoppingTarget freq ((N : ℝ) ^ B)⁻¹ K p.2 ≤ 0) := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hεR1 : (ε : ℝ) < 1 := by exact_mod_cast hε1
  obtain ⟨L, _, hrange⟩ := exists_coulomb_target_polynomial_bounds hfreq A B
  obtain ⟨k₀, _, hspacing⟩ := exists_localizedGram_spacing hfreq 1
  obtain ⟨c, k, hc, hk, hkmin, hbracket⟩ := exists_rational_hopping_brackets
    ε hε hε1 (B + A + L) (max kmin ((k₀ : ℝ) / (1 - (ε : ℝ))))
  have hkmin' : kmin ≤ (k : ℝ) := (le_max_left _ _).trans hkmin
  have hkspacing : (k₀ : ℝ) / (1 - (ε : ℝ)) ≤ k := (le_max_right _ _).trans hkmin
  refine ⟨c, k, hc, hk, hkmin', fun N hN => ?_⟩
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith)
  let D : ℝ := (k : ℝ) * Real.log (N : ℝ)
  let p := endpoints ε (RationalLogScale.value c k N)
  obtain ⟨ha0, ha1, hb0, hb1, haHop, hbHop⟩ := hbracket N hN
  have hlength : (k₀ : ℝ) * Real.log (N : ℝ) ≤ (1 - (ε : ℝ)) * D := by
    have hm := mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (sub_pos.mpr hεR1)).mp hkspacing) hlogN
    nlinarith only [hm]
  obtain ⟨hfive, hleak⟩ := hspacing N hNR
  have hleak₂ : 2 * localLeakageBound freq ((k₀ : ℝ) * Real.log (N : ℝ)) ≤
      localDualMass freq / 2 := by
    have hm := mul_le_mul_of_nonneg_right hNR
      (localLeakageBound_nonnegative freq ((k₀ : ℝ) * Real.log (N : ℝ)))
    exact hm.trans (by simpa only [pow_one] using hleak)
  have hsepA : (k₀ : ℝ) * Real.log (N : ℝ) ≤ (p.1 : ℝ) := hlength.trans ha0
  have hD0 : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) hlogN
  have hab : (p.1 : ℝ) ≤ p.2 := by
    have horder : (1 - (ε : ℝ) / 4) * D ≤ (1 + (ε : ℝ) / 4) * D := by
      nlinarith [mul_nonneg hεR.le hD0]
    exact ha1.trans (horder.trans hb0)
  change (1 - (ε : ℝ)) * D ≤ (p.1 : ℝ) ∧ _
  refine ⟨ha0, hb1, hfive.trans hlength, ?_, ?_⟩
  · intro r hr
    exact localizedCoulombProfile_gap hfreq hfive hleak₂ (hsepA.trans hr)
  · intro K hKlo hKhi
    have hK : (0 : ℝ) ≤ K := (inv_nonneg.mpr (pow_nonneg hNp.le A)).trans hKlo
    have hτ : 0 ≤ ((N : ℝ) ^ B)⁻¹ := inv_nonneg.mpr (pow_nonneg hNp.le B)
    obtain ⟨htlo, hthi⟩ := hrange N hNR K hKlo hKhi
    have htargetA := coulombHoppingTarget_bounds hfreq hfive hleak₂ hsepA hτ hK
    have htargetB := coulombHoppingTarget_bounds hfreq hfive hleak₂ (hsepA.trans hab) hτ hK
    exact ⟨sub_nonneg.mpr ((htargetA.2.trans hthi).trans haHop),
      sub_nonpos.mpr (hbHop.trans (htlo.trans htargetB.1))⟩

end ContinuumCoulomb.CalibrationRationalBracket

end

end OAI

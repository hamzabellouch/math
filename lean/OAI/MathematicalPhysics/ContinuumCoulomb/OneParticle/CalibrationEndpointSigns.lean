import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CalibrationRationalBracket
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarScaleChoice

namespace OAI

/-! The rational endpoints retain the analytic polynomial hopping brackets.
This uses the proved exponential envelopes and does not require monotonicity
of the hopping function. -/

noncomputable section
namespace ContinuumCoulomb.CalibrationRationalBracket

theorem brackets_of_larger_tolerance {A k : ℕ} {ε η N : ℝ}
    (hε : 0 ≤ ε) (hεη : ε ≤ η) (hη1 : η ≤ 1) (hN : 2 ≤ N)
    (hd : 2 ≤ (1 - η) * ((k : ℝ) * Real.log N))
    (hγ : 0 ≤ (k : ℝ) * ε - ((A : ℝ) + 1))
    (hlo : (k : ℝ) + 3 ≤ planarHoppingLowerConstant *
      (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1)))
    (hhi : planarHoppingUpperConstant * (2 * (k : ℝ) + 1) ≤
      (2 : ℝ) ^ ((k : ℝ) * ε - ((A : ℝ) + 1))) :
    N ^ A ≤ N ^ k * planarHopping ((1 - η) * ((k : ℝ) * Real.log N)) ∧
      N ^ k * planarHopping ((1 + η) * ((k : ℝ) * Real.log N)) ≤ (N ^ A)⁻¹ := by
  have he : (k : ℝ) * ε - ((A : ℝ) + 1) ≤ (k : ℝ) * η - ((A : ℝ) + 1) :=
    sub_le_sub_right (mul_le_mul_of_nonneg_left hεη (Nat.cast_nonneg _)) _
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  have h := planar_polynomial_brackets (hε.trans hεη) hη1 hN hd (hγ.trans he)
    (hlo.trans (mul_le_mul_of_nonneg_left hp planarHoppingLowerConstant_positive.le))
    (hhi.trans hp)
  have heq : Real.exp ((k : ℝ) * Real.log N) = N ^ k := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  simpa only [heq] using h

theorem exists_rational_hopping_brackets (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1)
    (A : ℕ) (kmin : ℝ) :
    ∃ (c : ℚ) (k : ℕ), 0 < c ∧ 0 < k ∧ kmin ≤ (k : ℝ) ∧
      ∀ N : ℕ, 2 ≤ N →
        let D := (k : ℝ) * Real.log (N : ℝ)
        let p := endpoints ε (RationalLogScale.value c k N)
        (1 - (ε : ℝ)) * D ≤ p.1 ∧ p.1 ≤ (1 - (ε : ℝ) / 4) * D ∧
          (1 + (ε : ℝ) / 4) * D ≤ p.2 ∧ p.2 ≤ (1 + (ε : ℝ)) * D ∧
          (N : ℝ) ^ A ≤ (N : ℝ) ^ k * planarHopping p.1 ∧
          (N : ℝ) ^ k * planarHopping p.2 ≤ ((N : ℝ) ^ A)⁻¹ := by
  have hεR : (0 : ℝ) < ε := by exact_mod_cast hε
  have hεR1 : (ε : ℝ) < 1 := by exact_mod_cast hε1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c, hcpos, hc⟩ := RationalLogScale.exists_logTwo_approximation
    (show (0 : ℝ) < (ε : ℝ) / 16 by positivity)
    (show (ε : ℝ) / 16 ≤ 1 by linarith)
  have hc' : |(c : ℝ) - Real.log 2| ≤ (ε : ℝ) / 64 * Real.log 2 := by
    convert hc using 1; ring
  let B : ℝ := max kmin (max (128 / (ε : ℝ)) (2 / ((1 - (ε : ℝ)) * Real.log 2)))
  obtain ⟨k, hkpos, hkB, hγ, _hd, hlo, hhi⟩ := exists_planar_scale_conditions_above
    B A (show (0 : ℝ) < (ε : ℝ) / 4 by positivity)
    (show (ε : ℝ) / 4 < 1 by linarith)
  have hkmin : kmin ≤ (k : ℝ) := (le_max_left _ _).trans hkB
  have hkcount : 128 ≤ (ε : ℝ) * (k : ℝ) := by
    have hb : 128 / (ε : ℝ) ≤ (k : ℝ) :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hkB)
    nlinarith [(div_le_iff₀ hεR).mp hb]
  have hkfloor : 2 ≤ (1 - (ε : ℝ)) * ((k : ℝ) * Real.log 2) := by
    have hb : 2 / ((1 - (ε : ℝ)) * Real.log 2) ≤ (k : ℝ) :=
      (le_max_right _ _).trans ((le_max_right _ _).trans hkB)
    have hm := (div_le_iff₀ (mul_pos (sub_pos.mpr hεR1) hlog)).mp hb
    nlinarith
  refine ⟨c, k, hcpos, hkpos, hkmin, fun N hN => ?_⟩
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log (by norm_num) hNR
  let D : ℝ := (k : ℝ) * Real.log (N : ℝ)
  let p := endpoints ε (RationalLogScale.value c k N)
  have hD : 0 < D := mul_pos (by exact_mod_cast hkpos) (hlog.trans_le hlogN)
  have hfloor : 2 ≤ (1 - (ε : ℝ)) * D := by
    have hm := mul_le_mul_of_nonneg_left hlogN (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    exact hkfloor.trans (mul_le_mul_of_nonneg_left hm (sub_pos.mpr hεR1).le)
  obtain ⟨ha0, ha1, hb0, hb1⟩ := rational_endpoint_bounds ε c hε hε1.le hc' k N hN hkcount
  have har0 : 1 - (ε : ℝ) ≤ (p.1 : ℝ) / D := (le_div_iff₀ hD).mpr ha0
  have har1 : (p.1 : ℝ) / D ≤ 1 - (ε : ℝ) / 4 := (div_le_iff₀ hD).mpr ha1
  have hbr0 : 1 + (ε : ℝ) / 4 ≤ (p.2 : ℝ) / D := (le_div_iff₀ hD).mpr hb0
  have hbr1 : (p.2 : ℝ) / D ≤ 1 + (ε : ℝ) := (div_le_iff₀ hD).mpr hb1
  let ηa : ℝ := 1 - (p.1 : ℝ) / D
  let ηb : ℝ := (p.2 : ℝ) / D - 1
  have hηa : (ε : ℝ) / 4 ≤ ηa ∧ ηa ≤ (ε : ℝ) := by dsimp only [ηa]; constructor <;> linarith
  have hηb : (ε : ℝ) / 4 ≤ ηb ∧ ηb ≤ (ε : ℝ) := by dsimp only [ηb]; constructor <;> linarith
  have haeq : (1 - ηa) * D = (p.1 : ℝ) := by
    dsimp only [ηa]
    field_simp [hD.ne']; ring
  have hbeq : (1 + ηb) * D = (p.2 : ℝ) := by
    dsimp only [ηb]
    field_simp [hD.ne']; ring
  have hshort := brackets_of_larger_tolerance (show (0 : ℝ) ≤ (ε : ℝ) / 4 by positivity)
    hηa.1 (hηa.2.trans hεR1.le) hNR
    (hfloor.trans (mul_le_mul_of_nonneg_right (by linarith : 1 - (ε : ℝ) ≤ 1 - ηa) hD.le))
    hγ hlo hhi
  have hlong := brackets_of_larger_tolerance (show (0 : ℝ) ≤ (ε : ℝ) / 4 by positivity)
    hηb.1 (hηb.2.trans hεR1.le) hNR
    (hfloor.trans (mul_le_mul_of_nonneg_right (by linarith : 1 - (ε : ℝ) ≤ 1 - ηb) hD.le))
    hγ hlo hhi
  change (1 - (ε : ℝ)) * D ≤ (p.1 : ℝ) ∧ _
  refine ⟨ha0, ha1, hb0, hb1, ?_, ?_⟩
  · have hs : (N : ℝ) ^ A ≤ (N : ℝ) ^ k * planarHopping ((1 - ηa) * D) := hshort.1
    rwa [haeq] at hs
  · have hl : (N : ℝ) ^ k * planarHopping ((1 + ηb) * D) ≤ ((N : ℝ) ^ A)⁻¹ := hlong.2
    rwa [hbeq] at hl

end ContinuumCoulomb.CalibrationRationalBracket

end

end OAI

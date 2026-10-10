import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullLowGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullHighGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFullMiddleGrowth

namespace OAI

/-! # One explicit envelope for the three original second-Poisson corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticCorrectionEnvelope (C ε ξ M J : ℝ) (N Q K L : ℕ)
    (v w : ℕ → ℂ) : ℝ :=
  (2 * L + 1) * (J * ((Nat.log 2 K + 1 : ℕ) : ℝ) *
    ((Nat.log 2 Q + 2 : ℕ) : ℝ) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
      (C * (4 * (K : ℝ) * N) ^ ε * (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
        (Real.sqrt (quadraticDivisorMoment (2 * N) v) *
          Real.sqrt (quadraticDivisorMoment (2 * N) w))))

theorem quadraticCorrectionEnvelope_nonneg {C ε ξ M J : ℝ}
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hJ : 0 ≤ J) (N Q K L : ℕ) (v w : ℕ → ℂ) :
    0 ≤ quadraticCorrectionEnvelope C ε ξ M J N Q K L v w := by
  unfold quadraticCorrectionEnvelope
  positivity

theorem quadratic_second_combination_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε ξ M H J : ℝ,
      0 ≤ C → 0 ≤ ε → 1 / 2 ≤ ξ → ξ ≤ 2 → ∀ e N Q K L : ℕ,
      0 < M → 0 < H → H ≤ N → (N : ℝ) ≤ 2 * H → 0 < e →
      0 < N → 1 ≤ Q → 0 < K → 1 ≤ J →
      ∀ R : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ B : ℕ, 0 < B → B ≤ K → ∀ i ≤ Nat.log 2 (2 * N),
        QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
          (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖(-𝓕 ρ 0 / 2 * ((M / e : ℝ) : ℂ)) *
          quadraticFullLowCorrection M H J e N Q K R v w -
        (((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
          ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)) *
          quadraticFullHighCorrection M H J e N Q K R v w +
        (((1 : ℂ) / 2) * ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ)) *
          quadraticFullMiddleCorrection ρ a ha M H J e N Q K L R v w‖ ≤
        A * quadraticCorrectionEnvelope C ε ξ M J N Q K L v w := by
  obtain ⟨Cu, Cb, hCu, hCb, hc⟩ := quadratic_full_middle_growth ρ a ha
  let F := ‖-𝓕 ρ 0 / 2‖
  let P := ‖((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
    ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2‖
  let A := 1 + 960 * F + 7680 * P + 2560 * (Cu + Cb)
  have hF : 0 ≤ F := norm_nonneg _
  have hP : 0 ≤ P := norm_nonneg _
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro C ε ξ M H J hC hε hξ hξ' e N Q K L hM hH hHN hNH he hN hQ hK hJ R v w hv hw hmat
  let T := C * (4 * (K : ℝ) * N) ^ ε * (M + Real.sqrt M * (K : ℝ) ^ (ξ - 1 / 2)) *
    (Real.sqrt (quadraticDivisorMoment (2 * N) v) * Real.sqrt (quadraticDivisorMoment (2 * N) w))
  let W := J * ((Nat.log 2 K + 1 : ℕ) : ℝ) * ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
    ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T
  let E := quadraticCorrectionEnvelope C ε ξ M J N Q K L v w
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hE : 0 ≤ E := quadraticCorrectionEnvelope_nonneg hC hM.le (by linarith) _ _ _ _ _ _
  have hWE : W ≤ E := by
    change W ≤ (2 * (L : ℝ) + 1) * W
    nlinarith [show 0 ≤ (L : ℝ) by positivity]
  have hl := quadratic_full_low_growth hC hε hξ hξ' hM hH hHN he hN hQ hK hJ R v w hv hw hmat
  have hh := quadratic_full_high_growth hC hε hξ hξ' hM hH hNH he hN hQ hK hJ R v w hmat
  have hm := hc C ε ξ M H J hC hε hξ hξ' e N Q K L hM hH hNH he hN hQ hK hJ R v w hv hw hmat
  have hlow : ‖((M / e : ℝ) : ℂ) * quadraticFullLowCorrection M H J e N Q K R v w‖ ≤ 960 * E := by
    apply hl.trans
    calc
      _ = 960 * W := by dsimp [W, T]; ring
      _ ≤ 960 * E := by gcongr
  have hhigh : ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
      quadraticFullHighCorrection M H J e N Q K R v w‖ ≤ 7680 * E := by
    apply hh.trans
    calc
      _ = 7680 * W := by dsimp [W, T]; ring
      _ ≤ 7680 * E := by gcongr
  have hbracket : Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) * (Cu + Cb) := by
    push_cast
    nlinarith [show 0 ≤ (Nat.log 2 Q : ℝ) by positivity]
  have hmiddle : ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
      quadraticFullMiddleCorrection ρ a ha M H J e N Q K L R v w‖ ≤ 2560 * (Cu + Cb) * E := by
    apply hm.trans
    calc
      _ = (2560 * J * (2 * L + 1) * ((Nat.log 2 K + 1 : ℕ) : ℝ) *
        ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T) *
          (Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb) := by dsimp [T]; ring
      _ ≤ (2560 * J * (2 * L + 1) * ((Nat.log 2 K + 1 : ℕ) : ℝ) *
        ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 * T) *
          (((Nat.log 2 Q + 2 : ℕ) : ℝ) * (Cu + Cb)) := by gcongr
      _ = 2560 * (Cu + Cb) * E := by dsimp [E, quadraticCorrectionEnvelope, T]; ring
  have hhalf : ‖(1 : ℂ) / 2‖ ≤ 1 := by norm_num
  let l := ((M / e : ℝ) : ℂ) * quadraticFullLowCorrection M H J e N Q K R v w
  let h := ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) * quadraticFullHighCorrection M H J e N Q K R v w
  let m := ((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
    quadraticFullMiddleCorrection ρ a ha M H J e N Q K L R v w
  simp only [mul_assoc]
  change ‖(-𝓕 ρ 0 / 2) * l -
    (((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
      ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2) * h + ((1 : ℂ) / 2) * m‖ ≤ A * E
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_sub_le _ _) (le_refl _)).trans
  rw [norm_mul (-𝓕 ρ 0 / 2) l,
    norm_mul (((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
      ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2) h, norm_mul ((1 : ℂ) / 2) m]
  have hmid' := mul_le_mul hhalf hmiddle (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hlo' := mul_le_mul_of_nonneg_left hlow hF
  have hhi' := mul_le_mul_of_nonneg_left hhigh hP
  change F * ‖l‖ + P * ‖h‖ + ‖(1 : ℂ) / 2‖ * ‖m‖ ≤ A * E
  dsimp only [A]
  nlinarith

end Ostmann

end OAI

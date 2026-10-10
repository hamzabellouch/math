import OAI.Analysis.LipschitzHilbert.Estimates.PlanarProfileBounds

namespace OAI

/-! The common profile constants remain uniform under the four unit
phases used in complex polarization. The proof uses their actual
weighted Schwartz seminorm definition, without taking a maximum over
the finite packet family. -/

noncomputable section

namespace LipschitzHilbert

theorem planarVerticalDerivative_add (f g : SchwartzMap (ℝ × ℝ) ℂ) :
    planarVerticalDerivative (f + g) = planarVerticalDerivative f + planarVerticalDerivative g := by
  unfold planarVerticalDerivative
  rw [map_add, map_add]

theorem planarHorizontalDerivative_add (f g : SchwartzMap (ℝ × ℝ) ℂ) :
    planarHorizontalDerivative (f + g) =
      planarHorizontalDerivative f + planarHorizontalDerivative g := by
  unfold planarHorizontalDerivative
  rw [map_add, map_add]

theorem planarVerticalJet_add (f g : SchwartzMap (ℝ × ℝ) ℂ) (i : Fin 3) :
    planarVerticalJet (f + g) i = planarVerticalJet f i + planarVerticalJet g i := by
  fin_cases i <;> simp [planarVerticalJet, planarVerticalDerivative_add]

theorem planarVerticalJet_smul (c : ℂ) (f : SchwartzMap (ℝ × ℝ) ℂ) (i : Fin 3) :
    planarVerticalJet (c • f) i = c • planarVerticalJet f i := by
  fin_cases i <;> simp [planarVerticalJet, planarVerticalDerivative_smul]

theorem planarEnvelopeConstant_add_smul_le (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (n : ℕ) :
    planarEnvelopeConstant (f + c • g) n ≤
      planarEnvelopeConstant f n + ‖c‖ * planarEnvelopeConstant g n := by
  let W := SchwartzMap.smulLeftCLM ℂ (fun z : ℝ × ℝ => (planarPolynomialWeight n z : ℂ))
  let p := SchwartzMap.seminorm ℂ (E := ℝ × ℝ) (F := ℂ) 0 0
  change p (W (f + c • g)) + 1 ≤ (p (W f) + 1) + ‖c‖ * (p (W g) + 1)
  rw [map_add, map_smul]
  have h := map_add_le_add p (W f) (c • W g)
  rw [map_smul_eq_mul] at h
  nlinarith [norm_nonneg c]

/-- The precise common profile constant is subadditive under
polarization, with the expected modulus of the scalar coefficient. -/
theorem planarProfileConstant_add_smul_le (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (n : ℕ) :
    planarProfileConstant (f + c • g) n ≤
      planarProfileConstant f n + ‖c‖ * planarProfileConstant g n := by
  simp only [planarProfileConstant, planarVerticalJet_add, planarVerticalJet_smul,
    planarHorizontalDerivative_add, planarHorizontalDerivative_smul,
    planarVerticalDerivative_add, planarVerticalDerivative_smul]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h0 := planarEnvelopeConstant_add_smul_le (planarVerticalJet f i)
    (planarVerticalJet g i) c n
  have hx := planarEnvelopeConstant_add_smul_le (planarHorizontalDerivative (planarVerticalJet f i))
    (planarHorizontalDerivative (planarVerticalJet g i)) c n
  have hy := planarEnvelopeConstant_add_smul_le (planarVerticalDerivative (planarVerticalJet f i))
    (planarVerticalDerivative (planarVerticalJet g i)) c n
  nlinarith

theorem planarProfileConstant_add_unit_smul_le (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ) :
    planarProfileConstant (f + c • g) n ≤
      planarProfileConstant f n + planarProfileConstant g n := by
  simpa only [hc, one_mul] using planarProfileConstant_add_smul_le f g c n

/-- Two profiles with the same bound have polarization profiles bounded
by twice that constant, uniformly for every unit complex phase. -/
theorem planarProfileConstant_polarization_bound (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (n : ℕ) (C : ℝ)
    (hf : planarProfileConstant f n ≤ C) (hg : planarProfileConstant g n ≤ C) :
    planarProfileConstant (f + c • g) n ≤ 2 * C := by
  exact (planarProfileConstant_add_unit_smul_le f g c hc n).trans (by linarith)

end LipschitzHilbert

end

end OAI

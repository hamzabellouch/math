import OAI.NumberTheory.TwoPoint.Circuits.CircuitPolynomialAlgebra

namespace OAI

/-! The finite algebraic steps of Braverman's Lemmas 11–12. A polynomial
that vanishes off a Boolean event gives a pointwise minorant after applying
`p ↦ 1 - (1-p)^2`; the uniform squared error is exactly the minorant gap.
Only the approximation construction, not this expectation argument, needs
the circuit-depth estimates. -/

namespace TwoPointCorrelations

variable {n : ℕ}

noncomputable def semiExactMinorant (P : BooleanCube n → ℝ) (x : BooleanCube n) : ℝ :=
  1 - (1 - P x) ^ 2

lemma semiExactMinorant_le {F P : BooleanCube n → ℝ}
    (hF : ∀ x, F x = 0 ∨ F x = 1) (hzero : ∀ x, F x = 0 → P x = 0) :
    ∀ x, semiExactMinorant P x ≤ F x := by
  intro x
  rcases hF x with hx | hx
  · simp [semiExactMinorant, hzero x hx, hx]
  · rw [hx]
    unfold semiExactMinorant
    nlinarith [sq_nonneg (1 - P x)]

lemma semiExactMinorant_gap {F P : BooleanCube n → ℝ}
    (hF : ∀ x, F x = 0 ∨ F x = 1) (hzero : ∀ x, F x = 0 → P x = 0) :
    ∀ x, F x - semiExactMinorant P x = (F x - P x) ^ 2 := by
  intro x
  rcases hF x with hx | hx
  · simp [semiExactMinorant, hzero x hx, hx]
  · simp only [semiExactMinorant, hx]
    ring

lemma WalshDegreeLE.minorant {P : BooleanCube n → ℝ} {d : ℕ}
    (hP : WalshDegreeLE P d) : WalshDegreeLE (semiExactMinorant P) (d + d) := by
  have hp := (WalshDegreeLE.const (n := n) 1 d).sub hP
  have hs := hp.mul hp
  have hq := (WalshDegreeLE.const (n := n) 1 (d + d)).sub hs
  change WalshDegreeLE (fun x => 1 - (1 - P x) ^ 2) (d + d)
  simpa only [pow_two] using hq

/-- A small exceptional set and a semi-exact low-degree approximation give
the required one-sided comparison of the original Boolean expectation. -/
theorem TWiseUniformDensity.semiExact_lower {t : ℕ}
    {g F F₀ P : BooleanCube n → ℝ}
    (hg : TWiseUniformDensity g t) (hn : ∀ x, 0 ≤ g x)
    (hF₀ : ∀ x, F₀ x = 0 ∨ F₀ x = 1)
    (hzero : ∀ x, F₀ x = 0 → P x = 0)
    (hdeg : WalshDegreeLE (semiExactMinorant P) t)
    {δu δg ε : ℝ}
    (hu : cubeAverage (fun x => |F x - F₀ x|) ≤ δu)
    (hmu : cubeAverage (fun x => g x * |F x - F₀ x|) ≤ δg)
    (herr : cubeAverage (fun x => (F₀ x - P x) ^ 2) ≤ ε) :
    cubeAverage F - (δu + δg + ε) ≤ cubeAverage (fun x => g x * F x) := by
  have hu' : cubeAverage F ≤ cubeAverage F₀ + δu := by
    have hb : ∀ x, F x ≤ F₀ x + |F x - F₀ x| := by
      intro x
      linarith [le_abs_self (F x - F₀ x)]
    have h := cubeAverage_mono hb
    rw [cubeAverage_add] at h
    linarith
  have hgap : cubeAverage F₀ - cubeAverage (semiExactMinorant P) ≤ ε := by
    rw [← cubeAverage_sub]
    simpa only [semiExactMinorant_gap hF₀ hzero] using herr
  have hlow : cubeAverage (semiExactMinorant P) ≤
      cubeAverage (fun x => g x * F₀ x) := by
    have h := cubeAverage_mono (fun x => mul_le_mul_of_nonneg_left
      (semiExactMinorant_le hF₀ hzero x) (hn x))
    rw [hg.polynomial_expectation hdeg] at h
    exact h
  have hmu' : cubeAverage (fun x => g x * F₀ x) ≤
      cubeAverage (fun x => g x * F x) + δg := by
    have hb : ∀ x, g x * F₀ x ≤ g x * F x + g x * |F x - F₀ x| := by
      intro x
      have h : F₀ x ≤ F x + |F x - F₀ x| := by
        have ha := le_abs_self (F₀ x - F x)
        rw [abs_sub_comm] at ha
        linarith
      have h' := mul_le_mul_of_nonneg_left h (hn x)
      nlinarith only [h']
    have h := cubeAverage_mono hb
    rw [cubeAverage_add] at h
    linarith
  linarith

end TwoPointCorrelations

end OAI

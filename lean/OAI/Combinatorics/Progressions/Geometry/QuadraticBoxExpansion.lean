import OAI.Combinatorics.Progressions.Estimates.QuadraticAntisymmetricOrbit

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_box_expansion (k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ V : NativeAntisymmetricOrbitFactors M N q,
                Real.exp (-q) ≤ (finiteBoxCorrelation (fun x y : ZMod N =>
                  star (M.evalCyclic N V.leftIndex (correlationInput x y)) *
                    M.evalCyclic N V.rightIndex (correlationInput y x))).re ∧
                ∃ F : (Fin 4 → ℤ) → ℂ,
                  Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 1 ((p + C) ^ C) F) ∧
                  (𝔼 x : Fin 4 → ZMod N,
                    ‖M.antisymmetricBoxValue V.leftIndex V.rightIndex
                        (fun j => ((x j).val : ℤ)) -
                      F (fun j => ((x j).val : ℤ))‖) ≤ Real.exp (-(4 * q + (p + 2) ^ k)) := by
  obtain ⟨A, _, hbiased⟩ := exists_quadratic_biased_orbit
  obtain ⟨B, _, hprecise⟩ := exists_antisymmetric_orbit_approximation
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let E := 4 * Q + (X + 2) ^ k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + E + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let a := (p + A) ^ A
  let e := 4 * a + (p + 2) ^ k
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hsum : a + (a + e + B) ^ B ≤ (p + C) ^ C := by
    simpa [Q, E, X, a, e, Polynomial.eval₂_pow] using hbudget p hp
  have haC : a ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (a + e + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ha).trans hsum
  obtain ⟨H, hH, hdense, M, i, hcorr, V, hbox⟩ :=
    hbiased hp ((Real.exp_le_exp.mpr haC).trans hN) f hf hG
  obtain ⟨F, ⟨EF⟩, herr⟩ := hprecise M V ha he
    ((Real.exp_le_exp.mpr hBC).trans hN)
  exact ⟨a, ha, haC, H, hH, hdense, M, i, hcorr, V, hbox, F, ⟨EF.mono hBC⟩, herr⟩

end Erdos3

end

end OAI

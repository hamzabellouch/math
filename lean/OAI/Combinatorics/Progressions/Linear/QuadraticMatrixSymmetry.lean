import OAI.Combinatorics.Progressions.Estimates.CommonWeightedExchange
import OAI.Combinatorics.Progressions.Estimates.QuadraticWeightedSymmetry

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_matrix_symmetry (k : ℕ) :
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
              ∃ w : (Fin 2 → ℤ) → ℝ,
                ∃ G : Fin M.outputDim → Fin M.outputDim → (Fin 2 → ℤ) → ℂ,
                  (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
                  Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
                    (fun z => (w z : ℂ))) ∧
                  (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1
                    ((p + C) ^ C) (G a b))) ∧
                  Real.exp (-(2 * q + 1)) ≤
                    (𝔼 z : Fin 2 → ZMod N, w (fun j => ((z j).val : ℤ))) ∧
                  (𝔼 z : Fin 2 → ZMod N, Real.sqrt (∑ a, ∑ b,
                    ‖M.antisymmetricKernel a b ((z 0).val : ℤ) ((z 1).val : ℤ) *
                      (w (fun j => ((z j).val : ℤ)) : ℂ) - G a b (fun j => ((z j).val : ℤ))‖ ^ 2)) ≤
                    Real.exp (-(2 * q + 1 + (p + 2) ^ k)) := by
  obtain ⟨A, _, hselected⟩ := exists_quadratic_weighted_symmetry_approximation k
  obtain ⟨B, _, hcommon⟩ := exists_common_weighted_exchange
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (2 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsum : t + (2 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (2 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  obtain ⟨q, hq, hqt, H, hH, hdense, M, i, hcorr, i', j', w, G, hw, ⟨EW⟩,
    ⟨EG⟩, _hmass, henergy, herr⟩ :=
    hselected hp ((Real.exp_le_exp.mpr htC).trans hN) f hf hG
  obtain ⟨v, U, hv, ⟨EV⟩, hU, hmass, herror⟩ :=
    hcommon M i' j' w G ht EW EG hw henergy herr
  have hcost : (q + t + B) ^ B ≤ (p + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (by linarith : q + t + B ≤ 2 * t + B) B).trans hBC
  refine ⟨q, hq, hqt.trans htC, H, hH, hdense, M, i, hcorr, v, U, hv,
    ⟨EV.mono hcost⟩, ?_, hmass, herror⟩
  intro a b
  obtain ⟨E⟩ := hU a b
  exact ⟨E.mono hcost⟩

end Erdos3

end

end OAI

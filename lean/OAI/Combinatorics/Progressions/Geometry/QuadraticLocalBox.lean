import OAI.Combinatorics.Progressions.Estimates.QuadraticAntisymmetricOrbit

namespace OAI

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

theorem exists_quadratic_antisymmetric_frozen_descent :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ V : NativeAntisymmetricOrbitFactors M N q,
                Nonempty (NativeAntisymmetricFrozenDescent V ((p + C) ^ C)) := by
  obtain ⟨A, _, horbit⟩ := exists_quadratic_antisymmetric_orbit_factors
  obtain ⟨B, _, hdescent⟩ := exists_antisymmetric_frozen_descent
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsum : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (q + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hsum
  obtain ⟨H, hH, hdense, M, i, hcorr, V⟩ :=
    horbit hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  obtain ⟨V⟩ := V
  obtain ⟨R⟩ := hdescent M V hq
  refine ⟨H, hH, ?_, q, hq, hqC, M, i, ?_, V, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact ⟨R.mono hBC⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_local_box_models :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ V : NativeAntisymmetricOrbitFactors M N q,
                ∃ R : NativeAntisymmetricFrozenDescent V ((p + C) ^ C),
                  Nonempty (NativeAntisymmetricLocalModels R ((p + C) ^ C)) := by
  obtain ⟨A, _, hfrozen⟩ := exists_quadratic_antisymmetric_frozen_descent
  obtain ⟨B, _, hlocal⟩ := exists_antisymmetric_local_models
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let a := (p + A) ^ A
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hsum : a + (a + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, a, Polynomial.eval₂_pow] using hbudget p hp
  have haC : a ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (a + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ha).trans hsum
  obtain ⟨H, hH, hdense, q, hq, hqa, M, i, hcorr, V, R⟩ :=
    hfrozen hp ((Real.exp_le_exp.mpr haC).trans hN) f hf hG
  obtain ⟨R⟩ := R
  let R' := R.mono haC
  obtain ⟨P, hP, hPb, hmodels⟩ := hlocal R'
  have hqC : (q + B) ^ B ≤ (p + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (by linarith : q + B ≤ a + B) B).trans hBC
  refine ⟨H, hH, ?_, q, hq, hqa.trans haC, M, i, ?_, V, R', ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg haC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg haC)).trans (hcorr h hh)
  · refine ⟨{
      period := P
      period_pos := hP
      period_bound := hPb.trans (Real.exp_le_exp.mpr hqC)
      local_model := ?_ }⟩
    intro y hy
    obtain ⟨S, hSo, hSc, hSe⟩ := hmodels y hy
    refine ⟨S, hSo, hSc, ?_⟩
    intro x δ hδ hx hres hnear
    exact (hSe x δ hδ hx hres hnear).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hqC) hδ)

end Erdos3

end

end OAI

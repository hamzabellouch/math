import OAI.Combinatorics.Progressions.Estimates.DiagonalRowTransfer

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quadratic_pair_frozen_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q r u : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧ 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                ∃ V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 r
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ)),
                  ∃ R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
                    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
                    (fun _ : Fin 2 => (N : ℝ)) u,
                    R.HasPairProjectionControl ((p + C) ^ C) ∧
                    R.HasPairFrozenReduction ((p + C) ^ C) := by
  obtain ⟨A, _, hprojected⟩ := exists_quadratic_pair_projected_factors
  obtain ⟨B, _, hfrozen⟩ := exists_antisymmetric_pair_frozen_reduction
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (3 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcost : t + (3 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hcost
  have hBC : (3 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hcost
  obtain ⟨q, r, u, hq, hqt, hr, hrt, hu, hut, H, hH, hdense, M, i, hderiv,
      i', j', V, R, hproj⟩ :=
    hprojected hp ((Real.exp_le_exp.mpr htC).trans hN) f hf hG
  have hbound : (q + r + u + B) ^ B ≤ (p + C) ^ C := by
    apply le_trans _ hBC
    apply pow_le_pow_left₀ (by positivity)
    change q + r + u + B ≤ 3 * t + B
    linarith
  exact ⟨q, r, u, hq, hqt.trans htC, hr, hrt.trans htC, hu, hut.trans htC,
    H, hH, hdense, M, i, hderiv, i', j', V, R,
    R.hasPairProjectionControl_mono hproj htC,
    R.hasPairFrozenReduction_mono (hfrozen R hu) hbound⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quadratic_pair_correlating_anchor :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ q r u : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧ 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        0 ≤ u ∧ u ≤ (p + C) ^ C ∧
        ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
          ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) q,
            ∃ i : Fin M.outputDim,
              (∀ h ∈ H, Real.exp (-q) ≤
                ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                  star (M.evalCyclic N i (correlationInput h n))‖) ∧
              ∃ i' j' : Fin M.outputDim,
                ∃ V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 r
                  Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
                  (fun z => M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ)),
                  ∃ R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
                    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
                    (fun _ : Fin 2 => (N : ℝ)) u,
                    R.HasPairProjectionControl ((p + C) ^ C) ∧
                    R.HasPairFrozenReduction ((p + C) ^ C) ∧
                    R.HasCorrelatingAnchor f H i ((p + C) ^ C) := by
  obtain ⟨A, _, hpair⟩ := exists_quadratic_pair_frozen_factors
  obtain ⟨B, _, hlocal⟩ := exists_antisymmetric_pair_local_approximation
  obtain ⟨K, _, hanchor⟩ := exists_antisymmetric_pair_correlating_anchor
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  let U := T + (3 * T + Polynomial.C B) ^ B + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (U + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  let b := (3 * t + B) ^ B
  let v := t + b + 2
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htv : t ≤ v := by dsimp [v]; linarith
  have hbv : b ≤ v := by dsimp [v]; linarith
  have hsum : t + (v + K) ^ K ≤ (p + C) ^ C := by
    simpa [X, T, U, t, v, b, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hvC : (v + K) ^ K ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  obtain ⟨q, r, u, hq, hqt, hr, hrt, hu, hut, H, hH, hdense, M, i, hderiv,
      i', j', V, R, hproj, hred⟩ := hpair hp ((Real.exp_le_exp.mpr htC).trans hN) f hf hG
  have hLB : (q + r + u + B) ^ B ≤ b := by
    apply pow_le_pow_left₀ (by positivity)
    change q + r + u + B ≤ 3 * t + B
    linarith
  have hloc : R.HasPairLocalApproximation b :=
    R.hasPairLocalApproximation_mono (hlocal R hu) hLB
  have hderiv' : ∀ h ∈ H, Real.exp (-q) ≤
      ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (M.eval i (correlationInput (h.val : ℤ) (n.val : ℤ)))‖ := by
    intro h hh
    have heval (n : ZMod N) : M.evalCyclic N i (correlationInput h n) =
        M.eval i (correlationInput (h.val : ℤ) (n.val : ℤ)) :=
      congrArg (M.eval i) (map_correlationInput (fun a : ZMod N => (a.val : ℤ)) h n)
    simpa only [heval] using hderiv h hh
  have hcor := hanchor R hloc hred hv (hqt.trans htv) hbv htv
    ((Real.exp_le_exp.mpr hvC).trans hN) f H i hf hdense hderiv'
  exact ⟨q, r, u, hq, hqt.trans htC, hr, hrt.trans htC, hu, hut.trans htC,
    H, hH, hdense, M, i, hderiv, i', j', V, R,
    R.hasPairProjectionControl_mono hproj htC, R.hasPairFrozenReduction_mono hred htC,
    NativePolynomialOrbitFactors.hasCorrelatingAnchor_mono hcor hvC⟩

end Erdos3

end

end OAI

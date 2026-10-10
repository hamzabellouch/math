import OAI.Combinatorics.Progressions.Estimates.QuarticPairPartitionedModel

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace QuarticMixedRowData

variable {N : ℕ} [NeZero N] {m p u q r d b δ β t : ℝ} {f : ZMod N → ℂ}
  {M : NativeMixedCorrelation 3 N m f}
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
  {E : NativeIntegerVectorEquivalence 3 u M.mixed.eval
    (fun out x => W.eval out (quarticInput (x 0) (fun _ => x 1)))}
  {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}
  (D : QuarticMixedRowData M W E d)

theorem correlatingAnchor_of_partition (P : NativeQuarticPointwisePartition R b δ β)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hb : 0 ≤ b) (hbt : b ≤ t)
    (hprod : positiveCyclicTripleBudget b ≤ t) (hloss : 2 * d + b + 4 ≤ t)
    (herr : δ + 4 * β ≤ Real.exp (-(2 * d)) / 2) :
    R.HasQuarticCorrelatingAnchor D.row D.shifts D.output t := by
  obtain ⟨cell, S, hSH, hS, hsize, hcorr⟩ := P.exists_correlating_anchor
    D.output D.row D.shifts (D.row_norm hf) (Real.exp_pos _) D.row_mass herr
  exact P.partition.correlatingAnchor_of_cell hb hbt hprod hloss
    D.row D.shifts D.output cell S hSH hS hsize hcorr

end QuarticMixedRowData

theorem exists_quartic_mixed_correlating_anchor :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {m p u q r d : ℝ} {f : ZMod N → ℂ}
      {M : NativeMixedCorrelation 3 N m f}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {E : NativeIntegerVectorEquivalence 3 u M.mixed.eval
        (fun out x => W.eval out (quarticInput (x 0) (fun _ => x 1)))}
      {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r)
      (D : QuarticMixedRowData M W E d), 0 ≤ r → 0 ≤ d → (∀ n, ‖f n‖ ≤ 1) →
      Real.exp ((tensorPowerBudget 6 p + q + r + d + C) ^ C) ≤ (N : ℝ) →
      R.HasQuarticCorrelatingAnchor D.row D.shifts D.output
        ((tensorPowerBudget 6 p + q + r + d + C) ^ C) := by
  obtain ⟨a, _, hlocal⟩ := exists_quartic_pair_local_approximation
  obtain ⟨b, _, hred⟩ := exists_quartic_pair_frozen_reduction
  obtain ⟨c, _, hpart⟩ := exists_quartic_diagonal_partition
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b
  let Q := (T + 2 * X + 2 + Polynomial.C c) ^ c
  let raise := fun Z : Polynomial ℕ => Z + (Z + 2) ^ 2 + 3
  let prod := fun Z : Polynomial ℕ => (Z + 2) ^ 2 + Z + (Z + (Z ^ 2 + Z + 3) ^ 2) + Z ^ 2 + 4
  let B := prod (raise (prod (raise Q)))
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + B + 2 * X + 4)
  refine ⟨C, hC, ?_⟩
  intro N _ m p u q r d f M W E i j V R D hr hd hf hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hk : 0 ≤ tensorPowerBudget 6 p := hp.trans (tensorPowerBudget_bounds 6 hp).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget 6 p + q + r + d
  let t := (v + a) ^ a + (v + b) ^ b
  let z := (t + 2 * v + 2 + c) ^ c
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hdv : d ≤ v := by dsimp [v]; linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hB : 0 ≤ positiveCyclicTripleBudget z := by
    have h0 := hz.trans (le_raisedNiltestBudget z)
    have h1 := h0.trans (le_productNiltestBudget h0)
    have h2 := h1.trans (le_raisedNiltestBudget _)
    exact h2.trans (le_productNiltestBudget h2)
  have hsum : z + positiveCyclicTripleBudget z + 2 * v + 4 ≤ (v + C) ^ C := by
    simpa [X, T, Q, B, raise, prod, z, t, positiveCyclicTripleBudget,
      raisedNiltestBudget, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget v hv
  have hzC : z ≤ (v + C) ^ C := by linarith only [hsum, hB, hv]
  have hBC : positiveCyclicTripleBudget z ≤ (v + C) ^ C := by linarith only [hsum, hz, hv]
  have hloss : 2 * d + z + 4 ≤ (v + C) ^ C := by linarith only [hsum, hB, hdv]
  have ha : (tensorPowerBudget 6 p + q + r + a) ^ a ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    gcongr
    dsimp [v]
    linarith
  have hb : (tensorPowerBudget 6 p + q + r + b) ^ b ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    gcongr
    dsimp [v]
    linarith
  have hpartN : Real.exp ((t + (2 * v + 2) + c) ^ c) ≤ (N : ℝ) := by
    have heq : (t + (2 * v + 2) + c) ^ c = z := by dsimp [z]; congr 1; ring
    rw [heq]
    exact (Real.exp_le_exp.mpr hzC).trans hN
  obtain ⟨δ, β, P, herr⟩ := hpart R (hlocal (W := W) R hr) (hred (W := W) R hr)
    ht (by positivity : 0 ≤ 2 * v + 2) ha hb hpartN
  have hPbudget : (t + (2 * v + 2) + c) ^ c = z := by dsimp [z]; congr 1; ring
  have herror : δ + 4 * β ≤ Real.exp (-(2 * d)) / 2 :=
    herr.trans ((Real.exp_le_exp.mpr (show -(2 * v + 2) ≤ -(2 * d) - 1 by linarith)).trans
      (exp_sub_one_le_half_exp (-(2 * d))))
  apply D.correlatingAnchor_of_partition P hf
  · rw [hPbudget]; exact hz
  · rw [hPbudget]; exact hzC
  · rw [hPbudget]; exact hBC
  · rw [hPbudget]; exact hloss
  · exact herror

theorem exists_quartic_anchored_mixed_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ M : NativeMixedCorrelation 3 N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) q,
        W.dim ≤ 16 * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        ∃ E : NativeIntegerVectorEquivalence 3 q M.mixed.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))),
        NativeIntegerVectorEquivalence 3 q (M.mixed.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ i j : Fin (W.tensorPower 6).outputDim,
        ∃ V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
          Finset.univ (fun x : Fin 4 → ZMod N => fun k => ((x k).val : ℤ))
          (fun x => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ))),
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
        ∃ R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
          V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
          (fun _ : Fin 4 => (N : ℝ)) r,
        ∃ D : QuarticMixedRowData M W E (2 * q + 3 * q),
          R.HasQuarticCorrelatingAnchor D.row D.shifts D.output ((p + C) ^ C) := by
  obtain ⟨a, _, hmodel⟩ := exists_quartic_pair_factored_model
  obtain ⟨b, _, hanchor⟩ := exists_quartic_mixed_correlating_anchor
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (14 * T + 7 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let r := (p + a) ^ a
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have hsum : r + (14 * r + 7 + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, T, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  obtain ⟨q, hq, hqr, M, W, hdim, hsymm, E, hdiff, i, j, V, ⟨R⟩⟩ :=
    hmodel hp ((Real.exp_le_exp.mpr hrC).trans hN) f hf hGowers
  change Fin (W.tensorPower 6).outputDim at i j
  obtain ⟨D⟩ := exists_quartic_mixed_row_data M W E hq
  have hkq : tensorPowerBudget 6 q = 7 * (q + 1) := by norm_num [tensorPowerBudget]
  have hcost : (tensorPowerBudget 6 q + q + r + (2 * q + 3 * q) + b) ^ b ≤ (p + C) ^ C := by
    rw [hkq]
    apply le_trans _ ((le_add_of_nonneg_left hr).trans hsum)
    apply pow_le_pow_left₀ (by positivity)
    have hqr' : q ≤ r := hqr
    linarith only [hqr']
  have hA := hanchor R D hr (by positivity : 0 ≤ 2 * q + 3 * q) hf
    ((Real.exp_le_exp.mpr hcost).trans hN)
  exact ⟨q, hq, hqr.trans hrC, M, W, hdim, hsymm, E, hdiff,
    i, j, V, r, hr, hrC, R, D, R.hasQuarticCorrelatingAnchor_mono hA hcost⟩

end Erdos3

end

end OAI

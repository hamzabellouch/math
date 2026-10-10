import OAI.Combinatorics.Progressions.Estimates.CubicDerivativeModel

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

theorem exists_cubic_precise_diagonal_exchange :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (_R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r),
      0 ≤ r → 0 ≤ e → Real.exp ((p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      ∃ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
        (∀ a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2
          ((p + q + r + e + C) ^ C) (G a c))) ∧
        (∀ a c (x : Fin 2 → ZMod N), ‖G a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
        (∀ a c, (𝔼 x : Fin 2 → ZMod N,
          ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (((x 1).val : ℤ) + shift)) *
              star (W.eval c (cubicTrilinearInput (x 1).val (x 0).val (((x 1).val : ℤ) + shift))) -
            G a c (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hlocal⟩ := exists_cubic_pair_local_approximation
  obtain ⟨B, _, hfrozen⟩ := exists_cubic_pair_frozen_reduction
  obtain ⟨D, _, hpartition⟩ := exists_cubic_diagonal_partition
  obtain ⟨E, _, hexchange⟩ := exists_cubic_diagonal_exchange
  let X : Polynomial ℕ := Polynomial.X
  let L := (X + Polynomial.C A) ^ A
  let K := (X + Polynomial.C B) ^ B
  let T := L + K + X + 2
  let Z := (T + (X + 1) + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z + (Z + Polynomial.C E) ^ E)
  refine ⟨C, hC, ?_⟩
  intro p q r e W N _ i j shift V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + e
  let b := (v + A) ^ A
  let c := (v + B) ^ B
  let t := b + c + v + 2
  let z := (t + (e + 1) + D) ^ D
  let zmax := (t + (v + 1) + D) ^ D
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hzmax : 0 ≤ zmax := by dsimp [zmax]; positivity
  have hbt : b ≤ t := by dsimp [t]; linarith
  have hct : c ≤ t := by dsimp [t]; linarith
  have hzz : z ≤ zmax := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  have hsum : zmax + (zmax + E) ^ E ≤ (p + q + r + e + C) ^ C := by
    simpa [X, L, K, T, Z, b, c, t, zmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hzC : zmax ≤ (p + q + r + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hEC : (zmax + E) ^ E ≤ (p + q + r + e + C) ^ C :=
    (le_add_of_nonneg_left hzmax).trans hsum
  have hloc : R.HasCubicPairLocalApproximation b :=
    R.hasCubicPairLocalApproximation_mono (hlocal R hr) (by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [v]
      linarith)
  have hred : R.HasCubicPairFrozenReduction c :=
    R.hasCubicPairFrozenReduction_mono (hfrozen R hr) (by
      apply pow_le_pow_left₀ (by positivity)
      dsimp [v]
      linarith)
  obtain ⟨δ, β, P, hP⟩ := hpartition R hloc hred ht (by linarith : 0 ≤ e + 1) hbt hct
    ((Real.exp_le_exp.mpr (hzz.trans hzC)).trans hN)
  obtain ⟨G, hG, _heval, hcap, herr⟩ := hexchange P hz
  have hcost : (z + E) ^ E ≤ (p + q + r + e + C) ^ C := by
    apply le_trans _ hEC
    apply pow_le_pow_left₀ (by positivity)
    linarith
  refine ⟨G, fun a c => ⟨(Classical.choice (hG a c)).mono hcost⟩, hcap, ?_⟩
  intro a c
  apply (herr a c).trans
  have hh := exp_sub_one_le_half_exp (-e)
  have hid : -(e + 1) = -e - 1 := by ring
  rw [← hid] at hh
  linarith

theorem exists_cubic_diagonal_exchange_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) q,
        ∃ W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) q,
          W.dim ≤ 8 * M.dim ∧
          (∀ (a : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) a).symm j)) =
              W.eval k x) ∧
          NativeIntegerVectorEquivalence 2 q M.eval (fun k x => W.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 q M.cubicMixedDerivative W.cubicTrilinearTriple ∧
          ∃ out : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-q) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i j : Fin W.outputDim × Fin W.outputDim),
              ∃ V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
                Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
                (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val
                  (((z 0).val : ℤ) + -(if branch then (N : ℤ) else 0))),
                ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
                ∃ _R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
                  V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
                  (fun _ : Fin 3 => (N : ℝ)) r,
                  ∃ G : Fin W.outputDim → Fin W.outputDim → (Fin 2 → ℤ) → ℂ,
                    (∀ a c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2
                      ((p + e + C) ^ C) (G a c))) ∧
                    (∀ a c (x : Fin 2 → ZMod N), ‖G a c (fun z => ((x z).val : ℤ))‖ ≤ 1) ∧
                    (∀ a c, (𝔼 x : Fin 2 → ZMod N,
                      ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val
                            (((x 1).val : ℤ) + -(if branch then (N : ℤ) else 0))) *
                          star (W.eval c (cubicTrilinearInput (x 1).val (x 0).val
                            (((x 1).val : ℤ) + -(if branch then (N : ℤ) else 0)))) -
                        G a c (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hmodel⟩ := exists_cubic_pair_factored_model
  obtain ⟨B, _, hexchange⟩ := exists_cubic_precise_diagonal_exchange
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (3 * T + X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let r := (p + A) ^ A
  let t := (p + e + A) ^ A
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [r, t]; gcongr; linarith
  have hsum : t + (3 * t + (p + e) + B) ^ B ≤ (p + e + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
  have htC : t ≤ (p + e + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hrC : r ≤ (p + C) ^ C := by
    have h : r + (3 * r + p + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, T, r, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_right (by positivity)).trans h
  obtain ⟨q, hq, hqr, H, hH, hHdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, branch, i, j, V, ⟨R⟩⟩ :=
    hmodel hp ((Real.exp_le_exp.mpr (hrt.trans htC)).trans hN) f hf hGowers
  have hcost : (q + q + r + e + B) ^ B ≤ (p + e + C) ^ C := by
    apply le_trans _ ((le_add_of_nonneg_left ht).trans hsum)
    apply pow_le_pow_left₀ (by positivity)
    have hqr' : q ≤ r := hqr
    linarith
  obtain ⟨G, hG, hcap, herr⟩ := hexchange R hr he ((Real.exp_le_exp.mpr hcost).trans hN)
  exact ⟨q, hq, hqr.trans hrC, H, hH, hHdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, branch, i, j, V, r, hr, hrC, R, G,
    fun a c => ⟨(Classical.choice (hG a c)).mono hcost⟩, hcap, herr⟩

end Erdos3

end

end OAI

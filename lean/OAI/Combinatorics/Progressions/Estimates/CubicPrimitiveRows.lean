import OAI.Combinatorics.Progressions.Dynamics.CubicCyclicErrorBudget
import OAI.Combinatorics.Progressions.Estimates.CubicOriginalDiagonalComparison

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

theorem exists_cubic_precise_unshifted_exchange :
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
          ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
              star (W.eval c (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
            G a c (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hlocal⟩ := exists_cubic_pair_local_approximation
  obtain ⟨B, _, hfrozen⟩ := exists_cubic_pair_frozen_reduction
  obtain ⟨D, _, hpartition⟩ := exists_cubic_diagonal_partition
  obtain ⟨E, _, hexchange⟩ := exists_cubic_unshifted_exchange
  let X : Polynomial ℕ := Polynomial.X
  let L := (X + Polynomial.C A) ^ A
  let K := (X + Polynomial.C B) ^ B
  let T := L + K + X + 2
  let Z := (T + (3 * X + 1) + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Z + (X + Z + Polynomial.C E) ^ E)
  refine ⟨C, hC, ?_⟩
  intro p q r e W N _ i j shift V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + e
  let b := (v + A) ^ A
  let c := (v + B) ^ B
  let t := b + c + v + 2
  let z := (t + (e + 2 * p + 1) + D) ^ D
  let zmax := (t + (3 * v + 1) + D) ^ D
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
  have hsum : zmax + (v + zmax + E) ^ E ≤ (p + q + r + e + C) ^ C := by
    simpa [X, L, K, T, Z, b, c, t, zmax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hzC : zmax ≤ (p + q + r + e + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hEC : (v + zmax + E) ^ E ≤ (p + q + r + e + C) ^ C :=
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
  obtain ⟨δ, β, P, hP⟩ := hpartition R hloc hred ht (by linarith : 0 ≤ e + 2 * p + 1) hbt hct
    ((Real.exp_le_exp.mpr (hzz.trans hzC)).trans hN)
  obtain ⟨G, hG, hcap, herr⟩ := hexchange P hz
  have hcost : (p + z + E) ^ E ≤ (p + q + r + e + C) ^ C := by
    apply le_trans _ hEC
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  refine ⟨G, fun a c => ⟨(Classical.choice (hG a c)).mono hcost⟩, hcap, ?_⟩
  intro a c
  apply (herr a c).trans
  calc
    Real.exp (2 * p) * (2 * (δ + 4 * β)) ≤ Real.exp (2 * p) * Real.exp (-(e + 2 * p)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      have hh := exp_sub_one_le_half_exp (-(e + 2 * p))
      have hid : -(e + 2 * p + 1) = -(e + 2 * p) - 1 := by ring
      rw [← hid] at hh
      linarith
    _ = Real.exp (-e) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem exists_cubic_unshifted_exchange_model :
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
                      ‖W.eval a (cubicTrilinearInput (x 0).val (x 1).val (x 1).val) *
                          star (W.eval c (cubicTrilinearInput (x 1).val (x 0).val (x 1).val)) -
                        G a c (fun z => ((x z).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hmodel⟩ := exists_cubic_pair_factored_model
  obtain ⟨B, _, hexchange⟩ := exists_cubic_precise_unshifted_exchange
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

section

namespace Erdos3

open scoped BigOperators NNReal

theorem exists_cubic_cyclic_comparison_model :
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
            ∃ K : (Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) →
                (Fin 7 → Fin W.cubicRoot.outputDim) → (Fin 2 → ℤ) → ℂ,
              (∀ a b, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2
                ((p + e + C) ^ C) (K a b))) ∧
              (∀ a b, (𝔼 x : Fin 2 → ZMod N,
                ‖W.cubicRoot.cubicCyclicDiagonalDerivative a x *
                    star (W.cubicRoot.cubicSymmetricSeven b (fun k => ((x k).val : ℤ))) -
                  K a b (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hmodel⟩ := exists_cubic_unshifted_exchange_model
  obtain ⟨B, _, hroot⟩ := NativeMultidegreeNilcharacter.exists_cubicRootCyclicCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := (X + 362 * U + 500 + Polynomial.C A) ^ A
  let S := (U + T + X + 500 + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + X + 500 + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + A) ^ A
  let umax := (v + A) ^ A
  let accuracy := e + 362 * u + 500
  let t := (p + accuracy + A) ^ A
  let tmax := (v + 362 * umax + 500 + A) ^ A
  let b := e + 500
  let smax := (umax + tmax + v + 500 + B) ^ B
  let δ : ℝ≥0 := ⟨Real.exp (-b), (Real.exp_pos _).le⟩
  have hδval : (δ : ℝ) = Real.exp (-b) := rfl
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t, accuracy]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hδ : 0 < δ := Real.exp_pos _
  have hinv : (δ : ℝ)⁻¹ ≤ Real.exp b := by rw [hδval, ← Real.exp_neg, neg_neg]
  have hsum : umax + tmax + v + 500 + smax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, umax, tmax, smax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by dsimp [accuracy]; positivity)
    dsimp [accuracy, v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hsC : smax ≤ (p + e + C) ^ C := by linarith
  have hbC : b ≤ (p + e + C) ^ C := by dsimp [b, v] at *; linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + 362 * u + 500 + A) ^ A + p + 500 +
        (u + (p + 362 * u + 500 + A) ^ A + p + 500 + B) ^ B ≤ (p + C) ^ C := by
      simpa [X, U, T, S, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + 362 * u + 500 + A) ^ A := by positivity
    have h2 : 0 ≤ (u + (p + 362 * u + 500 + A) ^ A + p + 500 + B) ^ B := by positivity
    linarith
  obtain ⟨q, hq, hqu, H, hH, hdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, branch, i, j, V, r, hr, hrbound, R, G, hG, hcap, herr⟩ :=
    hmodel hp (by dsimp [accuracy]; positivity : 0 ≤ accuracy)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax : q ≤ umax := hqu.trans hum
  have hcost : (q + t + b + B) ^ B ≤ (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    dsimp [b, v]
    linarith
  have herror := cubic_cyclic_error_bound (Nat.cast_nonneg W.outputDim) hu
    (W.output_bound.trans (Real.exp_le_exp.mpr hqu)) ((Real.exp_le_exp.mpr hbC).trans hN)
  refine ⟨q, hq, hqu.trans huC, H, hH, hdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, W.cubicRootCyclicCorrection N δ G, ?_, ?_⟩
  · intro a c
    exact ⟨(Classical.choice (hroot W N δ hδ ht hb hinv hsymm G hG a c)).mono hcost⟩
  · intro a c
    apply (W.cubicRootCyclicCorrection_mean_error δ hδ G hcap herr a c).trans
    have hrootDim : W.cubicRoot.outputDim = W.outputDim ^ 9 := rfl
    simpa only [hrootDim, Nat.cast_pow, hδval, b, accuracy] using herror

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_cubic_original_integration :
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
            ∃ K : (Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) → Fin M.outputDim →
                (Fin 3 → Fin W.cubicRoot.outputDim) → Fin W.cubicRoot.outputDim → (Fin 2 → ℤ) → ℂ,
              (∀ a i b c, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 2
                ((p + e + C) ^ C) (K a i b c))) ∧
              (∀ a i b c, (𝔼 x : Fin 2 → ZMod N,
                ‖W.cubicRoot.cubicCyclicDiagonalDerivative a x *
                    (M.eval i (fun k => ((x k).val : ℤ)) *
                      (W.cubicRoot.cubicHhnTensor b (fun k => ((x k).val : ℤ)) *
                        W.cubicRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
                  K a i b c (fun k => ((x k).val : ℤ))‖) ≤ Real.exp (-e)) := by
  obtain ⟨A, _, hmodel⟩ := exists_cubic_cyclic_comparison_model
  obtain ⟨B, _, hexpansion⟩ := NativeMultidegreeNilcharacter.exists_cubicOriginalDiagonalCorrection_expansion
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let T := (X + 27 * U + Polynomial.C A) ^ A
  let S := (U + T + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + T + S)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let v := p + e
  let u := (p + A) ^ A
  let umax := (v + A) ^ A
  let accuracy := e + 27 * u
  let t := (p + accuracy + A) ^ A
  let tmax := (v + 27 * umax + A) ^ A
  let smax := (umax + tmax + B) ^ B
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have humax : 0 ≤ umax := by dsimp [umax]; positivity
  have ht : 0 ≤ t := by dsimp [t, accuracy]; positivity
  have htmax : 0 ≤ tmax := by dsimp [tmax]; positivity
  have hsmax : 0 ≤ smax := by dsimp [smax]; positivity
  have hsum : umax + tmax + smax ≤ (p + e + C) ^ C := by
    simpa [X, U, T, S, umax, tmax, smax, v, Polynomial.eval₂_pow] using hbudget v hv
  have hum : u ≤ umax :=
    pow_le_pow_left₀ (by positivity) (by dsimp [v]; linarith) A
  have htm : t ≤ tmax := by
    apply pow_le_pow_left₀ (by dsimp [accuracy]; positivity)
    dsimp [accuracy, v]
    linarith
  have htC : tmax ≤ (p + e + C) ^ C := by linarith
  have hsC : smax ≤ (p + e + C) ^ C := by linarith
  have huC : u ≤ (p + C) ^ C := by
    have hh : u + (p + 27 * u + A) ^ A + (u + (p + 27 * u + A) ^ A + B) ^ B ≤
        (p + C) ^ C := by
      simpa [X, U, T, S, u, Polynomial.eval₂_pow] using hbudget p hp
    have h1 : 0 ≤ (p + 27 * u + A) ^ A := by positivity
    have h2 : 0 ≤ (u + (p + 27 * u + A) ^ A + B) ^ B := by positivity
    linarith
  obtain ⟨q, hq, hqu, H, hH, hdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, K, hK, herr⟩ := hmodel hp (by dsimp [accuracy]; positivity : 0 ≤ accuracy)
      ((Real.exp_le_exp.mpr (htm.trans htC)).trans hN) f hf hGowers
  have hqmax : q ≤ umax := hqu.trans hum
  have hcost : (q + t + B) ^ B ≤ (p + e + C) ^ C := by
    apply le_trans _ hsC
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hd : (W.outputDim : ℝ) ≤ Real.exp u :=
    W.output_bound.trans (Real.exp_le_exp.mpr hqu)
  have hpow : (W.outputDim : ℝ) ^ 27 ≤ Real.exp (27 * u) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hd 27).trans_eq (Real.exp_nat_mul u 27).symm
  have hrootDim : W.cubicRoot.outputDim = W.outputDim ^ 9 := rfl
  have hcube : (W.cubicRoot.outputDim : ℝ) ^ 3 ≤ Real.exp (27 * u) := by
    simpa only [hrootDim, Nat.cast_pow, ← pow_mul, Nat.reduceMul] using hpow
  have herror : (W.cubicRoot.outputDim : ℝ) ^ 3 * Real.exp (-accuracy) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp (27 * u) * Real.exp (-accuracy) :=
        mul_le_mul_of_nonneg_right hcube (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [accuracy]; ring
  refine ⟨q, hq, hqu.trans huC, H, hH, hdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, M.cubicOriginalDiagonalCorrection W K, ?_, ?_⟩
  · intro a i b c
    exact ⟨(Classical.choice (hexpansion M W ht hdiag K hK a i b c)).mono hcost⟩
  · intro a i b c
    exact (M.cubicOriginalDiagonalCorrection_mean_error W K herr a i b c).trans herror

end Erdos3

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem cubicCyclicDiagonalDerivative_unit {p : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p) (x : Fin 2 → ZMod N) :
    ∑ a : Fin W.outputDim × Fin W.outputDim, ‖W.cubicCyclicDiagonalDerivative a x‖ ^ 2 = 1 := by
  simp only [cubicCyclicDiagonalDerivative, Fintype.sum_prod_type, norm_mul, norm_star,
    mul_pow, ← Finset.mul_sum, W.unit_eval, mul_one]

theorem cubicCyclicDiagonalDerivative_norm {p : ℝ} {N : ℕ} [NeZero N]
    (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
    (a : Fin W.outputDim × Fin W.outputDim) (x : Fin 2 → ZMod N) :
    ‖W.cubicCyclicDiagonalDerivative a x‖ ≤ 1 := by
  rw [cubicCyclicDiagonalDerivative, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans
    (W.norm_eval _ _)

theorem cubic_original_row_correlation_bound {p ε : ℝ} {N : ℕ} [NeZero N]
    (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) p)
    (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)
    (i : Fin M.outputDim) (χ : ZMod N → AddChar (ZMod N) ℂ)
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (K : (Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) →
      (Fin 3 → Fin W.cubicRoot.outputDim) → Fin W.cubicRoot.outputDim → (Fin 2 → ℤ) → ℂ)
    (herr : ∀ a b c, (𝔼 x : Fin 2 → ZMod N,
      ‖W.cubicRoot.cubicCyclicDiagonalDerivative a x *
          (M.eval i (fun k => ((x k).val : ℤ)) *
            (W.cubicRoot.cubicHhnTensor b (fun k => ((x k).val : ℤ)) *
              W.cubicRoot.eval c (fun _ => ((x 0).val : ℤ)))) -
        K a b c (fun k => ((x k).val : ℤ))‖) ≤ ε) :
    (𝔼 h : ZMod N, ‖finiteFourierCoeff
      (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N i (correlationInput h n))) (χ h)‖) ≤
      (∑ abc : ((Fin W.cubicRoot.outputDim × Fin W.cubicRoot.outputDim) ×
          (Fin 3 → Fin W.cubicRoot.outputDim)) × Fin W.cubicRoot.outputDim,
        𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
          (multiplicativeDerivative f h n * star (χ h n)) *
            (W.cubicRoot.cubicCyclicDiagonalDerivative abc.1.1 ![h, n] *
              W.cubicRoot.cubicHhnTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)]) *
                star (K abc.1.1 abc.1.2 abc.2 ![(h.val : ℤ), (n.val : ℤ)])‖) +
          (W.cubicRoot.outputDim : ℝ) ^ 6 * ε := by
  let R := W.cubicRoot
  let I := (Fin R.outputDim × Fin R.outputDim) × (Fin 3 → Fin R.outputDim)
  have hinput (h n : ZMod N) : (fun k => ((![h, n] k).val : ℤ)) = ![(h.val : ℤ), (n.val : ℤ)] := by
    funext k
    fin_cases k <;> rfl
  have heval (h n : ZMod N) : M.evalCyclic N i (correlationInput h n) =
      M.eval i ![(h.val : ℤ), (n.val : ℤ)] := by
    unfold evalCyclic
    congr 1
    funext k
    fin_cases k <;> rfl
  have hunit (h n : ZMod N) : ∑ ab : I,
      ‖R.cubicCyclicDiagonalDerivative ab.1 ![h, n] *
        R.cubicHhnTensor ab.2 ![(h.val : ℤ), (n.val : ℤ)]‖ ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [norm_mul, mul_pow, ← Finset.mul_sum, R.cubicHhnTensor_unit, mul_one]
    exact R.cubicCyclicDiagonalDerivative_unit _
  have hF (h n : ZMod N) : ‖multiplicativeDerivative f h n * star (χ h n)‖ ≤ 1 := by
    simpa only [norm_mul, norm_star, AddChar.norm_apply, mul_one] using
      multiplicativeDerivative_norm_le_one f hf h n
  have hh := unit_row_correlation_bound
    (fun h n => multiplicativeDerivative f h n * star (χ h n))
    (fun h n => M.eval i ![(h.val : ℤ), (n.val : ℤ)])
    (fun ab : I => fun h n => R.cubicCyclicDiagonalDerivative ab.1 ![h, n] *
      R.cubicHhnTensor ab.2 ![(h.val : ℤ), (n.val : ℤ)])
    (fun c h => R.eval c (fun _ => (h.val : ℤ)))
    (fun ab c h n => K ab.1 ab.2 c ![(h.val : ℤ), (n.val : ℤ)]) hF hunit
    (fun h => R.unit_eval _) (fun ab h n => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (R.cubicCyclicDiagonalDerivative_norm _ _)).trans
          (R.cubicHhnTensor_norm _ _)) (fun c h => R.norm_eval _ _) (ε := ε) (by
      intro ab c
      have he := herr ab.1 ab.2 c
      rw [expect_fin_two] at he
      simpa only [hinput, Matrix.cons_val_zero, mul_assoc, mul_comm, mul_left_comm] using he)
  have hrow (h : ZMod N) :
      (𝔼 n : ZMod N, (multiplicativeDerivative f h n * star (χ h n)) *
        star (M.eval i ![(h.val : ℤ), (n.val : ℤ)])) =
      finiteFourierCoeff (fun n => multiplicativeDerivative f h n *
        star (M.evalCyclic N i (correlationInput h n))) (χ h) := by
    unfold finiteFourierCoeff
    apply Finset.expect_congr rfl
    intro n _
    dsimp only
    rw [heval]
    ring
  have hcard : (Fintype.card (I × Fin R.outputDim) : ℝ) = (R.outputDim : ℝ) ^ 6 := by
    simp only [I, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
    ring
  simpa only [hrow, hcard] using hh

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped BigOperators

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p)

noncomputable def cubicPrimitiveFactor {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (i : Fin W.outputDim) (n : ZMod N) : ℂ :=
  f n * W.eval i (fun _ => (n.val : ℤ))

theorem cubicPrimitiveFactor_norm {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (i : Fin W.outputDim) (n : ZMod N) :
    ‖W.cubicPrimitiveFactor f i n‖ ≤ 1 := by
  rw [cubicPrimitiveFactor, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hf n)).trans (W.norm_eval _ _)

theorem cubicPrimitiveFactor_cross {N : ℕ} [NeZero N] (f : ZMod N → ℂ)
    (a : Fin W.outputDim × Fin W.outputDim) (h n : ZMod N) :
    multiplicativeDerivative f h n * W.cubicCyclicDiagonalDerivative a ![h, n] =
      W.cubicPrimitiveFactor f a.1 n * star (W.cubicPrimitiveFactor f a.2 (n + h)) := by
  simp only [multiplicativeDerivative, cubicCyclicDiagonalDerivative, cubicPrimitiveFactor,
    Matrix.cons_val_zero, Matrix.cons_val_one, star_mul]
  rw [add_comm h n]
  ring

end NativeMultidegreeNilcharacter

theorem exists_cubic_primitive_rows :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) q,
        ∃ a : Fin W.outputDim × Fin W.outputDim, ∃ b : Fin 3 → Fin W.outputDim,
        ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
          Nonempty (NativeMeanRowCorrelation (fun _ : Fin 2 => 1) 2 ((p + C) ^ C)
            (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
            (fun h n => (W.cubicPrimitiveFactor f a.1 n *
                star (W.cubicPrimitiveFactor f a.2 (n + h))) *
              W.cubicHhnTensor b ![(h.val : ℤ), (n.val : ℤ)] * star (χ h n))) := by
  obtain ⟨A, _, hintegrate⟩ := exists_cubic_original_integration
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let R := 10 * (U + 1)
  let E := 2 * U + 6 * R + 4
  let T := (X + E + Polynomial.C A) ^ A
  let V := 2 * U + 2 + 6 * R + T
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + R + E + T + V)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let r := 10 * (u + 1)
  let e := 2 * u + 6 * r + 4
  let t := (p + e + A) ^ A
  let v := 2 * u + 2 + 6 * r + t
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hsum : u + r + e + t + v ≤ (p + C) ^ C := by
    simpa [X, U, R, E, T, V, u, r, e, t, v, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := by linarith
  have hrC : r ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, H, hH, hdense, M, W, hdim, hsymm, hdiag, hdiff,
    out, χ, hcorr, K, hK, herr⟩ :=
    hintegrate hp he ((Real.exp_le_exp.mpr htC).trans hN) f hf hGowers
  let B := W.cubicRoot
  have hroot : tensorPowerBudget 9 q ≤ r := by
    norm_num only [tensorPowerBudget, Nat.cast_ofNat]
    dsimp [r]
    linarith
  have hroot0 : 0 ≤ tensorPowerBudget 9 q := by unfold tensorPowerBudget; positivity
  have hD : (B.outputDim : ℝ) ≤ Real.exp r :=
    B.output_bound.trans (Real.exp_le_exp.mpr hroot)
  have hD6 : (B.outputDim : ℝ) ^ 6 ≤ Real.exp (6 * r) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hD 6).trans_eq (Real.exp_nat_mul r 6).symm
  let J := ((Fin B.outputDim × Fin B.outputDim) × (Fin 3 → Fin B.outputDim)) × Fin B.outputDim
  let z (abc : J) := 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
    (multiplicativeDerivative f h n * star (χ h n)) *
      (B.cubicCyclicDiagonalDerivative abc.1.1 ![h, n] *
        B.cubicHhnTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)]) *
          star (K abc.1.1 out abc.1.2 abc.2 ![(h.val : ℤ), (n.val : ℤ)])‖
  have hcard : (Fintype.card J : ℝ) ≤ Real.exp (6 * r) := by
    have hc : (Fintype.card J : ℝ) = (B.outputDim : ℝ) ^ 6 := by
      simp only [J, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
      ring
    rw [hc]
    exact hD6
  have hmass : Real.exp (-(2 * u)) ≤ 𝔼 h : ZMod N, ‖finiteFourierCoeff
      (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖ := by
    have hh := dense_set_mean_lower_bound H _ (fun _ => norm_nonneg _) (Real.exp_nonneg (-q))
      (by simpa only [ZMod.card] using hdense) hcorr
    have heq : Real.exp (-q) * Real.exp (-q) = Real.exp (-(2 * q)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hh
    exact (Real.exp_le_exp.mpr (by linarith)).trans hh
  have htransfer := M.cubic_original_row_correlation_bound W out χ f hf
    (fun a b c => K a out b c) (fun a b c => herr a out b c)
  change _ ≤ (∑ abc : J, z abc) + (B.outputDim : ℝ) ^ 6 * Real.exp (-e) at htransfer
  let δ := Real.exp (-(2 * u + 2))
  have hδ : 0 < δ := Real.exp_pos _
  have herror : (B.outputDim : ℝ) ^ 6 * Real.exp (-e) ≤ δ := by
    calc
      _ ≤ Real.exp (6 * r) * Real.exp (-e) :=
        mul_le_mul_of_nonneg_right hD6 (Real.exp_nonneg _)
      _ = Real.exp (-(2 * u + 4)) := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
      _ ≤ δ := Real.exp_le_exp.mpr (by linarith)
  have htwo : 2 * δ ≤ Real.exp (-(2 * u)) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hmass' : δ ≤ ∑ abc : J, z abc := by linarith
  obtain ⟨abc, habc⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ)) z
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hmass')
  have habc' : Real.exp (-(2 * u + 2 + 6 * r)) ≤ z abc := by
    have heq : δ / Real.exp (6 * r) = Real.exp (-(2 * u + 2 + 6 * r)) := by
      dsimp [δ]; rw [← Real.exp_sub]; congr 1; ring
    rwa [heq] at habc
  let expansion := Classical.choice (hK abc.1.1 out abc.1.2 abc.2)
  obtain ⟨P⟩ := NativeMeanRowCorrelation.exists_of_expansion expansion
    (by positivity : 0 ≤ 2 * u + 2 + 6 * r) habc'
  have heq : (fun h n : ZMod N => (multiplicativeDerivative f h n * star (χ h n)) *
      (B.cubicCyclicDiagonalDerivative abc.1.1 ![h, n] *
        B.cubicHhnTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)])) =
      (fun h n => (B.cubicPrimitiveFactor f abc.1.1.1 n *
          star (B.cubicPrimitiveFactor f abc.1.1.2 (n + h))) *
        B.cubicHhnTensor abc.1.2 ![(h.val : ℤ), (n.val : ℤ)] * star (χ h n)) := by
    funext h n
    rw [← B.cubicPrimitiveFactor_cross f abc.1.1 h n]
    ring
  refine ⟨tensorPowerBudget 9 q, hroot0, hroot.trans hrC, B, abc.1.1, abc.1.2, χ, ?_⟩
  exact ⟨heq ▸ P.mono hvC⟩

end Erdos3

end

end OAI

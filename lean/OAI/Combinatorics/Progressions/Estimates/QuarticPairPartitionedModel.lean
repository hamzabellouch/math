import OAI.Combinatorics.Progressions.Linear.QuarticKernelCorrelatedModel

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

theorem NativeSampleCorrelation.normalized_reverse_correlation
    {σ X : Type*} [Fintype X] {w : σ → ℕ} {s : ℕ} {p : ℝ}
    {sample : X → σ → ℤ} {f : X → ℂ}
    (V : NativeSampleCorrelation w s p Finset.univ sample f) :
    Real.exp (-(2 * p)) ≤
      ‖𝔼 x, (V.test.expNormalize p).eval (sample x) * star (f x)‖ := by
  have hmean : (𝔼 x, (V.test.expNormalize p).eval (sample x) * star (f x)) =
      (Real.exp (-p) : ℂ) * star (𝔼 x, f x * star (V.test.eval (sample x))) := by
    rw [star_finite_expect, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro x _
    rw [Niltest.expNormalize_eval, star_mul, star_star]
    ring
  rw [hmean, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_star]
  calc
    _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left V.correlation (Real.exp_nonneg _)

namespace NativeCubicPairPartition

attribute [local instance] NativeCubicPairPartition.finite

variable {p q r b ε : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
  {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r}

theorem exists_witness_cell (P : NativeCubicPairPartition R b ε)
    (herr : 4 * ε ≤ Real.exp (-(2 * q)) / 2) :
    ∃ a : Fin 3 → P.I, Real.exp (-(2 * q)) / (2 * Real.exp b) ≤
      ‖𝔼 x : Fin 3 → ZMod N,
        (V.test.expNormalize q).eval (fun k => ((x k).val : ℤ)) *
          star ((P.cellWeight a x : ℂ) * P.cellKernel a x)‖ := by
  apply P.exists_correlating_cell _ (Real.exp_pos _) _ herr V.normalized_reverse_correlation
  intro x
  apply ((V.test.expNormalize q).norm_eval_le _).trans
  exact_mod_cast V.test.expNormalize_norm V.complexity

end NativeCubicPairPartition

theorem exists_cubic_pair_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r), 0 ≤ r → 0 ≤ e →
      Real.exp ((p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeCubicPairPartition R ((p + q + r + e + C) ^ C) (Real.exp (-e))) := by
  obtain ⟨a, _, hlocal⟩ := exists_cubic_pair_local_approximation
  obtain ⟨b, _, hfrozen⟩ := exists_cubic_pair_frozen_reduction
  obtain ⟨c, _, hpartition⟩ := exists_cubic_pair_precise_partition
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p q r e W N _ i j shift V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + e
  let t := (v + a) ^ a + (v + b) ^ b
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ha : (p + q + r + a) ^ a ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    gcongr
    exact le_add_of_nonneg_right he
  have hb : (p + q + r + b) ^ b ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    gcongr
    exact le_add_of_nonneg_right he
  have hcost : (t + e + c) ^ c ≤ (p + q + r + e + C) ^ C := by
    have hpoly : (t + v + c) ^ c ≤ (v + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hpoly
    gcongr
    dsimp [v]
    linarith
  obtain ⟨P⟩ := hpartition R (hlocal R hr) (hfrozen R hr) ht he ha hb
    ((Real.exp_le_exp.mpr hcost).trans hN)
  exact ⟨P.mono hcost le_rfl⟩

attribute [local instance] NativeCubicPairPartition.finite

theorem exists_cubic_pair_witness_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r), 0 ≤ r → 0 ≤ e →
      Real.exp ((p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      ∃ P : NativeCubicPairPartition R ((p + q + r + e + C) ^ C)
          (Real.exp (-(e + 2 * q + 10))),
        ∃ a : Fin 3 → P.I, Real.exp (-(2 * q)) / (2 * Real.exp ((p + q + r + e + C) ^ C)) ≤
          ‖𝔼 x : Fin 3 → ZMod N, (V.test.expNormalize q).eval (fun k => ((x k).val : ℤ)) *
            star ((P.cellWeight a x : ℂ) * P.cellKernel a x)‖ := by
  obtain ⟨a, _, hpartition⟩ := exists_cubic_pair_partition
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((3 * X + 10 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r e W N _ i j shift V R hr he hN
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r + e
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hcost : (p + q + r + (e + 2 * q + 10) + a) ^ a ≤ (v + C) ^ C := by
    have hpoly : (3 * v + 10 + a) ^ a ≤ (v + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hpoly
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  obtain ⟨P₀⟩ := hpartition R hr (by positivity : 0 ≤ e + 2 * q + 10)
    ((Real.exp_le_exp.mpr hcost).trans hN)
  let P := P₀.mono hcost le_rfl
  refine ⟨P, P.exists_witness_cell ?_⟩
  have h8 : (8 : ℝ) ≤ Real.exp 10 := by linarith [Real.add_one_le_exp (10 : ℝ)]
  have hsmall : 8 * Real.exp (-(e + 2 * q + 10)) ≤ Real.exp (-(2 * q)) := by
    calc
      _ ≤ Real.exp 10 * Real.exp (-(e + 2 * q + 10)) := by gcongr
      _ = Real.exp (10 - (e + 2 * q + 10)) := by simp only [← Real.exp_add, sub_eq_add_neg]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  linarith

theorem exists_cubic_pair_partitioned_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + e + C) ^ C ∧
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-q) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) q,
        ∃ V : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) q,
          V.dim ≤ 8 * M.dim ∧
          (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 2)) k x,
            V.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 2) e).symm j)) =
              V.eval k x) ∧
          NativeIntegerVectorEquivalence 2 q
            M.eval (fun k x => V.eval k (fun j => x j.1)) ∧
          NativeIntegerVectorEquivalence 2 q
            M.cubicMixedDerivative V.cubicTrilinearTriple ∧
          ∃ out : Fin M.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
            (∀ h ∈ H, Real.exp (-q) ≤ ‖finiteFourierCoeff
              (fun n => multiplicativeDerivative f h n * star (M.evalCyclic N out (correlationInput h n))) (χ h)‖) ∧
            ∃ (branch : Bool) (i j : Fin V.outputDim × Fin V.outputDim),
              ∃ S : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
                Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
                (fun z => V.cubicAntisymmetricPair i j (z 1).val (z 2).val
                  (((z 0).val : ℤ) + -(if branch then (N : ℤ) else 0))),
                ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + e + C) ^ C ∧
                  ∃ R : NativePolynomialOrbitFactors (pi S.cubicPairModels)
                    S.cubicPairPolynomial (piFrequency S.cubicPairFrequencies)
                    (fun _ : Fin 3 => (N : ℝ)) r,
                    ∃ P : NativeCubicPairPartition R ((p + e + C) ^ C)
                        (Real.exp (-(e + 2 * q + 10))),
                      ∃ a : Fin 3 → P.I, Real.exp (-(2 * q)) / (2 * Real.exp ((p + e + C) ^ C)) ≤
                        ‖𝔼 x : Fin 3 → ZMod N,
                          (S.test.expNormalize q).eval (fun k => ((x k).val : ℤ)) *
                            star ((P.cellWeight a x : ℂ) * P.cellKernel a x)‖ := by
  obtain ⟨a, _, hmodel⟩ := exists_cubic_pair_factored_model
  obtain ⟨b, _, hpartition⟩ := exists_cubic_pair_witness_partition
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (3 * T + X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let r := (p + a) ^ a
  let t := (p + e + a) ^ a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [r, t]; gcongr; linarith
  have hsum : t + (3 * t + (p + e) + b) ^ b ≤ (p + e + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
  have htC : t ≤ (p + e + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  obtain ⟨q, hq, hqr, H, hH, hHdense, M, V, hdim, hsymm, hdiag, E,
    out, χ, hcorr, branch, i, j, S, ⟨R⟩⟩ :=
    hmodel hp ((Real.exp_le_exp.mpr (hrt.trans htC)).trans hN) f hf hGowers
  have hcost : (q + q + r + e + b) ^ b ≤ (p + e + C) ^ C := by
    apply le_trans _ ((le_add_of_nonneg_left ht).trans hsum)
    apply pow_le_pow_left₀ (by positivity)
    have hqr' : q ≤ r := hqr
    linarith
  obtain ⟨P₀, cell, hcell⟩ := hpartition R hr he ((Real.exp_le_exp.mpr hcost).trans hN)
  let P := P₀.mono hcost le_rfl
  have hthreshold : Real.exp (-(2 * q)) / (2 * Real.exp ((p + e + C) ^ C)) ≤
      Real.exp (-(2 * q)) / (2 * Real.exp ((q + q + r + e + b) ^ b)) := by
    apply div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcost) (by norm_num)
  exact ⟨q, hq, hqr.trans (hrt.trans htC), H, hH, hHdense, M, V, hdim, hsymm, hdiag, E,
    out, χ, hcorr, branch, i, j, S, r, hr, hrt.trans htC, R, P, cell, hthreshold.trans hcell⟩

end Erdos3

end

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

theorem exists_quartic_pair_factored_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ R : NativeMixedCorrelation 3 N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) q,
        W.dim ≤ 16 * R.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 q R.mixed.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 q (R.mixed.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ i j : Fin (W.outputDim ^ 6),
        ∃ S : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
          Finset.univ (fun x : Fin 4 → ZMod N => fun k => ((x k).val : ℤ))
          (fun x => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ))),
          Nonempty (NativePolynomialOrbitFactors (pi S.quarticPairModels)
            S.quarticPairPolynomial (piFrequency S.quarticPairFrequencies)
            (fun _ : Fin 4 => (N : ℝ)) ((p + C) ^ C)) := by
  obtain ⟨a, _, hmodel⟩ := exists_quartic_kernel_correlated_model
  obtain ⟨b, _, hstep⟩ := exists_quartic_pair_step_drop
  obtain ⟨c, _, horbit⟩ := exists_quartic_pair_orbit_factors
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let K := 7 * (Q + 1)
  let U := (K + Q + Polynomial.C b) ^ b
  let T := (K + Q + U + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + U + T)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + a) ^ a
  let k := 7 * (q + 1)
  let u := (k + q + b) ^ b
  let t := (k + q + u + c) ^ c
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hsum : q + u + t ≤ (p + C) ^ C := by
    simpa [X, Q, K, U, T, q, k, u, t, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hsum, hu, ht]
  have huC : u ≤ (p + C) ^ C := by linarith only [hsum, hq, ht]
  have htC : t ≤ (p + C) ^ C := by linarith only [hsum, hq, hu]
  obtain ⟨R, W, hdim, hsymm, hdiag, E, i, j, ⟨S⟩⟩ :=
    hmodel hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  have hkV : tensorPowerBudget 6 ((p + a) ^ a) = k := by
    norm_num [tensorPowerBudget, k, q]
  have hstepN : Real.exp ((tensorPowerBudget 6 ((p + a) ^ a) + q + b) ^ b) ≤ (N : ℝ) := by
    rw [hkV]
    exact (Real.exp_le_exp.mpr huC).trans hN
  obtain ⟨F⟩ := hstep S hstepN
  have hFpos : 0 ≤ (tensorPowerBudget 6 ((p + a) ^ a) + q + b) ^ b := by
    rw [hkV]
    exact hu
  have hcost : (tensorPowerBudget 6 ((p + a) ^ a) + q +
      (tensorPowerBudget 6 ((p + a) ^ a) + q + b) ^ b + c) ^ c ≤ (p + C) ^ C := by
    rw [hkV]
    exact htC
  obtain ⟨O⟩ := horbit F hFpos ((Real.exp_le_exp.mpr hcost).trans hN)
  exact ⟨q, hq, hqC, R, W, hdim, hsymm, hdiag, E, i, j, S,
    ⟨O.mono hcost (fun _ => by exact_mod_cast NeZero.pos N)⟩⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {N : ℕ} [NeZero N] {m p u : ℝ} {f : ZMod N → ℂ}
  (M : NativeMixedCorrelation 3 N m f)
  (W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p)
  (E : NativeIntegerVectorEquivalence 3 u M.mixed.eval
    (fun out x => W.eval out (quarticInput (x 0) (fun _ => x 1))))

structure QuarticMixedRowData (b : ℝ) where
  mixedCoordinate : Fin M.mixed.outputDim
  output : Fin W.outputDim
  errorIndex : Fin (E.selectedExpansion mixedCoordinate output).count
  shifts : Finset (ZMod N)
  subset : shifts ⊆ M.shifts
  nonempty : shifts.Nonempty
  density : Real.exp (-b) * N ≤ (shifts.card : ℝ)
  correlation : ∀ h ∈ shifts, Real.exp (-b) ≤
    ‖𝔼 n : ZMod N, ((E.selectedExpansion mixedCoordinate output).test errorIndex).normalizedRow u
      M.normalizedResidualRow h n * star (W.eval output (quarticInput (h.val : ℤ) (fun _ => (n.val : ℤ))))‖

namespace QuarticMixedRowData

variable {M W E} {b c : ℝ} (D : QuarticMixedRowData M W E b)

noncomputable def row : ZMod N → ZMod N → ℂ :=
  ((E.selectedExpansion D.mixedCoordinate D.output).test D.errorIndex).normalizedRow u
    M.normalizedResidualRow

theorem row_norm (hf : ∀ n, ‖f n‖ ≤ 1) (h n : ZMod N) : ‖D.row h n‖ ≤ 1 :=
  Niltest.normalizedRow_norm _ ((E.selectedExpansion D.mixedCoordinate D.output).complexity D.errorIndex)
    M.normalizedResidualRow (M.normalizedResidualRow_norm hf) h n

theorem row_correlation (h : ZMod N) (hh : h ∈ D.shifts) :
    Real.exp (-b) ≤ ‖𝔼 n : ZMod N, D.row h n *
      star (W.eval D.output (quarticInput (h.val : ℤ) ![(n.val : ℤ), (n.val : ℤ), (n.val : ℤ)]))‖ := by
  have hconst (n : ℤ) : (fun _ : Fin 3 => n) = ![n, n, n] := by
    funext k
    fin_cases k <;> rfl
  simpa only [row, hconst] using D.correlation h hh

theorem row_mass : Real.exp (-(2 * b)) ≤ 𝔼 h : ZMod N, if h ∈ D.shifts then
    ‖𝔼 n : ZMod N, D.row h n *
      star (W.eval D.output (quarticInput (h.val : ℤ) ![(n.val : ℤ), (n.val : ℤ), (n.val : ℤ)]))‖ else 0 := by
  classical
  have hind : (𝔼 h : ZMod N, if h ∈ D.shifts then Real.exp (-b) else 0) =
      (D.shifts.card : ℝ) * Real.exp (-b) / N := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [ZMod.card]
    simp
  calc
    _ = Real.exp (-b) * Real.exp (-b) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ (D.shifts.card : ℝ) * Real.exp (-b) / N := by
      apply (le_div_iff₀ (Nat.cast_pos.mpr (NeZero.pos N))).mpr
      nlinarith [mul_le_mul_of_nonneg_right D.density (Real.exp_nonneg (-b))]
    _ = _ := hind.symm
    _ ≤ _ := by
      apply Finset.expect_le_expect
      intro h _
      split_ifs with hh
      · exact D.row_correlation h hh
      · exact le_rfl

noncomputable def mono (hbc : b ≤ c) : QuarticMixedRowData M W E c :=
  { D with
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbc))
      (Nat.cast_nonneg N)).trans D.density
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hbc)).trans (D.correlation h hh) }

end QuarticMixedRowData

theorem exists_quartic_mixed_row_data (hu : 0 ≤ u) :
    Nonempty (QuarticMixedRowData M W E (2 * m + 3 * u)) := by
  obtain ⟨out, H, hHM, hH, hHsize, hHcorr⟩ := M.exists_fixed_normalized_residual_coordinate
  have heval (h n : ZMod N) :
      M.mixed.eval out (correlationInput (h.val : ℤ) (n.val : ℤ)) =
        M.mixed.evalCyclic N out (correlationInput h n) := by
    apply congrArg (M.mixed.eval out)
    funext k
    fin_cases k <;> rfl
  have hc : ∀ h ∈ H, Real.exp (-(2 * m)) ≤
      ‖𝔼 n : ZMod N, M.normalizedResidualRow h n *
        star (M.mixed.eval out (correlationInput (h.val : ℤ) (n.val : ℤ)))‖ := by
    intro h hh
    simpa only [heval] using hHcorr h hh
  obtain ⟨k, l, S, hSH, hS, hsize, hcorr⟩ := E.exists_fixed_normalized_row
    (fun x => W.unit_eval _) out H hH hHsize M.normalizedResidualRow hc
  refine ⟨{
    mixedCoordinate := out
    output := k
    errorIndex := l
    shifts := S
    subset := hSH.trans hHM
    nonempty := hS
    density := ?_
    correlation := hcorr }⟩
  exact (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (show -(2 * m + 3 * u) ≤ -(2 * m + 2 * u) by linarith))
    (Nat.cast_nonneg N)).trans hsize

end Erdos3

end

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

namespace NativeQuarticPairPartition

attribute [local instance] NativeQuarticPairPartition.finite

variable {p q r b ε : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
  {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}

theorem exists_witness_cell (P : NativeQuarticPairPartition R b ε)
    (herr : 12 * ε ≤ Real.exp (-(2 * q)) / 2) :
    ∃ a : Fin 4 → P.I, Real.exp (-(2 * q)) / (2 * Real.exp b) ≤
      ‖𝔼 x : Fin 4 → ZMod N,
        (V.test.expNormalize q).eval (fun k => ((x k).val : ℤ)) *
          star ((P.cellWeight a x : ℂ) * P.cellKernel a x)‖ := by
  apply P.exists_correlating_cell _ (Real.exp_pos _) _ herr V.normalized_reverse_correlation
  intro x
  apply ((V.test.expNormalize q).norm_eval_le _).trans
  exact_mod_cast V.test.expNormalize_norm V.complexity

end NativeQuarticPairPartition

theorem exists_quartic_pair_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r), 0 ≤ r → 0 ≤ e →
      Real.exp ((tensorPowerBudget 6 p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeQuarticPairPartition R ((tensorPowerBudget 6 p + q + r + e + C) ^ C) (Real.exp (-e))) := by
  obtain ⟨a, _, hlocal⟩ := exists_quartic_pair_local_approximation
  obtain ⟨b, _, hfrozen⟩ := exists_quartic_pair_frozen_reduction
  obtain ⟨c, _, hpartition⟩ := exists_quartic_pair_precise_partition
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a + (X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p q r e W N _ i j V R hr he hN
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget 6 p := hW.trans (tensorPowerBudget_bounds 6 hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget 6 p + q + r + e
  let t := (v + a) ^ a + (v + b) ^ b
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have ha : (tensorPowerBudget 6 p + q + r + a) ^ a ≤ t := by
    apply le_trans _ (le_add_of_nonneg_right (by positivity))
    gcongr
    exact le_add_of_nonneg_right he
  have hb : (tensorPowerBudget 6 p + q + r + b) ^ b ≤ t := by
    apply le_trans _ (le_add_of_nonneg_left (by positivity))
    gcongr
    exact le_add_of_nonneg_right he
  have hcost : (t + e + c) ^ c ≤ (tensorPowerBudget 6 p + q + r + e + C) ^ C := by
    have hpoly : (t + v + c) ^ c ≤ (v + C) ^ C := by
      simpa [X, T, t, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hpoly
    gcongr
    dsimp [v]
    linarith
  obtain ⟨P⟩ := hpartition R (hlocal (W := W) R hr) (hfrozen (W := W) R hr) ht he ha hb
    ((Real.exp_le_exp.mpr hcost).trans hN)
  exact ⟨P.mono hcost le_rfl⟩

attribute [local instance] NativeQuarticPairPartition.finite

theorem exists_quartic_pair_witness_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r e : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r), 0 ≤ r → 0 ≤ e →
      Real.exp ((tensorPowerBudget 6 p + q + r + e + C) ^ C) ≤ (N : ℝ) →
      ∃ P : NativeQuarticPairPartition R ((tensorPowerBudget 6 p + q + r + e + C) ^ C)
          (Real.exp (-(e + 2 * q + 24))),
        ∃ a : Fin 4 → P.I, Real.exp (-(2 * q)) / (2 * Real.exp ((tensorPowerBudget 6 p + q + r + e + C) ^ C)) ≤
          ‖𝔼 x : Fin 4 → ZMod N, (V.test.expNormalize q).eval (fun k => ((x k).val : ℤ)) *
            star ((P.cellWeight a x : ℂ) * P.cellKernel a x)‖ := by
  obtain ⟨a, _, hpartition⟩ := exists_quartic_pair_partition
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((3 * X + 24 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r e W N _ i j V R hr he hN
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget 6 p := hW.trans (tensorPowerBudget_bounds 6 hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget 6 p + q + r + e
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hcost : (tensorPowerBudget 6 p + q + r + (e + 2 * q + 24) + a) ^ a ≤ (v + C) ^ C := by
    have hpoly : (3 * v + 24 + a) ^ a ≤ (v + C) ^ C := by
      simpa [X, Polynomial.eval₂_pow] using hbudget v hv
    apply le_trans _ hpoly
    apply pow_le_pow_left₀ (by positivity)
    dsimp [v]
    linarith
  obtain ⟨P₀⟩ := hpartition R hr (by positivity : 0 ≤ e + 2 * q + 24)
    ((Real.exp_le_exp.mpr hcost).trans hN)
  let P := P₀.mono hcost le_rfl
  refine ⟨P, P.exists_witness_cell ?_⟩
  have h24 : (24 : ℝ) ≤ Real.exp 24 := by linarith [Real.add_one_le_exp (24 : ℝ)]
  have hsmall : 24 * Real.exp (-(e + 2 * q + 24)) ≤ Real.exp (-(2 * q)) := by
    calc
      _ ≤ Real.exp 24 * Real.exp (-(e + 2 * q + 24)) := by gcongr
      _ = Real.exp (24 - (e + 2 * q + 24)) := by simp only [← Real.exp_add, sub_eq_add_neg]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  linarith

theorem exists_quartic_pair_partitioned_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p e : ℝ}, 0 ≤ p → 0 ≤ e →
      Real.exp ((p + e + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + e + C) ^ C ∧
      ∃ M : NativeMixedCorrelation 3 N q f,
      ∃ W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) q,
        W.dim ≤ 16 * M.mixed.dim ∧
        (∀ (e : ReplicatedPermutation (mixedCorrelationDegree 3)) k x,
          W.eval k (fun j => x ((replicatedPermutation (mixedCorrelationDegree 3) e).symm j)) = W.eval k x) ∧
        NativeIntegerVectorEquivalence 3 q M.mixed.eval
          (fun i x => W.eval i (quarticInput (x 0) (fun _ => x 1))) ∧
        NativeIntegerVectorEquivalence 3 q (M.mixed.mixedSecondDifferenceWithShift 0)
          (quarticSixFactorVector W.eval) ∧
        ∃ i j : Fin (W.tensorPower 6).outputDim,
        ∃ S : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
          Finset.univ (fun x : Fin 4 → ZMod N => fun k => ((x k).val : ℤ))
          (fun x => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((x k).val : ℤ))),
        ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + e + C) ^ C ∧
        ∃ R : NativePolynomialOrbitFactors (pi S.quarticPairModels)
          S.quarticPairPolynomial (piFrequency S.quarticPairFrequencies)
          (fun _ : Fin 4 => (N : ℝ)) r,
        ∃ P : NativeQuarticPairPartition R ((p + e + C) ^ C)
            (Real.exp (-(e + 2 * q + 24))),
        ∃ a : Fin 4 → P.I, Real.exp (-(2 * q)) / (2 * Real.exp ((p + e + C) ^ C)) ≤
          ‖𝔼 x : Fin 4 → ZMod N,
            (S.test.expNormalize q).eval (fun k => ((x k).val : ℤ)) *
              star ((P.cellWeight a x : ℂ) * P.cellKernel a x)‖ := by
  obtain ⟨a, _, hmodel⟩ := exists_quartic_pair_factored_model
  obtain ⟨b, _, hpartition⟩ := exists_quartic_pair_witness_partition
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (9 * T + 7 + X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro N _ p e hp he hN f hf hGowers
  let r := (p + a) ^ a
  let t := (p + e + a) ^ a
  have hr : 0 ≤ r := by dsimp only [r]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hrt : r ≤ t := by dsimp only [r, t]; gcongr; linarith
  have hsum : t + (9 * t + 7 + (p + e) + b) ^ b ≤ (p + e + C) ^ C := by
    simpa [X, T, t, Polynomial.eval₂_pow] using hbudget (p + e) (add_nonneg hp he)
  have htC : t ≤ (p + e + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  obtain ⟨q, hq, hqr, M, W, hdim, hsymm, hdiag, E, i, j, S, ⟨R⟩⟩ :=
    hmodel hp ((Real.exp_le_exp.mpr (hrt.trans htC)).trans hN) f hf hGowers
  change Fin (W.tensorPower 6).outputDim at i j
  have hkq : tensorPowerBudget 6 q = 7 * (q + 1) := by norm_num [tensorPowerBudget]
  have hcost : (tensorPowerBudget 6 q + q + r + e + b) ^ b ≤ (p + e + C) ^ C := by
    rw [hkq]
    apply le_trans _ ((le_add_of_nonneg_left ht).trans hsum)
    apply pow_le_pow_left₀ (by positivity)
    have hqr' : q ≤ r := hqr
    linarith only [hqr', hrt, hp]
  obtain ⟨P₀, cell, hcell⟩ := hpartition (W := W) (V := S) R hr he
    ((Real.exp_le_exp.mpr hcost).trans hN)
  let P := P₀.mono hcost le_rfl
  have hthreshold : Real.exp (-(2 * q)) / (2 * Real.exp ((p + e + C) ^ C)) ≤
      Real.exp (-(2 * q)) / (2 * Real.exp ((tensorPowerBudget 6 q + q + r + e + b) ^ b)) := by
    apply div_le_div_of_nonneg_left (Real.exp_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcost) (by norm_num)
  exact ⟨q, hq, hqr.trans (hrt.trans htC), M, W, hdim, hsymm, hdiag, E,
    i, j, S, r, hr, hrt.trans htC, R, P, cell, hthreshold.trans hcell⟩

end Erdos3

end

end OAI

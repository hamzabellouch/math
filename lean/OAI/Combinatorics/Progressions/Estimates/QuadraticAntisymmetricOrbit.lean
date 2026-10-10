import OAI.Combinatorics.Progressions.Geometry.AntisymmetricBoxStepDrop

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_antisymmetric_orbit_factors_indices :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      {N : ℕ} [NeZero N] (V : NativeAntisymmetricBoxFactorization W N p),
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∃ R : NativeAntisymmetricOrbitFactors W N ((p + C) ^ C),
        R.leftIndex = V.leftIndex ∧ R.rightIndex = V.rightIndex := by
  obtain ⟨a, _, hnormalize⟩ := exists_lattice_normalized_refiltered_factorization
    (∑ k, mixedCorrelationDegree 1 k)
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 8
  let T := (Q + 2) ^ 2 + Q + (Q + (Q ^ 2 + Q + 3) ^ 2) + Q ^ 2 + 4 + X + 4
  let R := (T + 4) ^ 11 + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p W N _ V hN
  have hp := V.nonnegative
  let := V.topology
  let := V.topologicalAdd
  let := V.continuousSMul
  let := V.hausdorff
  let D := pi (fun _ : Fin 8 => W.model)
  let t := productNiltestBudget (p + 8) + p + 4
  let r := (t + 4) ^ 11 + p + 4
  have hprod : 0 ≤ productNiltestBudget (p + 8) := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith
  have ht11 : 0 ≤ (t + 4) ^ 11 := by positivity
  have hTr : (t + 4) ^ 11 ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have h4r : 4 ≤ r := by dsimp [r]; linarith
  have hcost : r + (r + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, T, R, t, r, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hpow : 0 ≤ (r + a) ^ a := by positivity
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hfinal : (r + a) ^ a ≤ (p + C) ^ C := by linarith
  have hD : D.GeometryComplexityLE t :=
    (W.antisymmetricBoxNiltest_complexity hp V.leftIndex V.rightIndex).1.mono D
      (by dsimp [t]; linarith)
  obtain ⟨m₀, hm₀, hin, hout, hE⟩ := D.exists_prescribed_adapted_model
    V.basis V.weight V.adapted ht hD (fun i j => (V.height i j).trans (by linarith))
  let E := D.filtration.ofAdaptedBasis V.basis V.weight V.adapted D.lattice m₀ hm₀ hin hout
  let g := W.antisymmetricBoxPolynomial V.leftIndex V.rightIndex
  have hfactor : ∀ _j : Unit,
      E.filtration.ControlledSymbolFactorization E.basis V.weight V.adapted
        (piFrequency W.antisymmetricBoxFrequencies) (fun _ : Fin 4 => (N : ℝ))
        (E.filtration.realPolynomialSymbolHom E.basis V.weight V.adapted (fun _ => 1) g) r := by
    intro _
    have h := V.factorization
    rw [W.antisymmetricBoxNiltest_symbol] at h
    exact NilpotentLieFiltration.ControlledSymbolFactorization.mono
      D.filtration V.basis V.weight V.adapted h hpr
      (fun _ => by exact_mod_cast NeZero.pos N)
  obtain ⟨U, v, m, κ, slow, middle, rat, hv, hU, hheight, hfreq, hm, hmp, hκ,
    hproduct, hslow, hrat, hmid0, hrat0, hcoeff, _hvalues⟩ :=
    hnormalize E V.weight V.adapted (fun _ : Unit => piFrequency W.antisymmetricBoxFrequencies)
      r hr (hE.mono E hTr) (by simpa using h4r) (by norm_num; linarith)
      (fun _ : Fin 4 => (N : ℝ)) (fun _ => (Real.exp_le_exp.mpr hfinal).trans hN) g hfactor
  exact ⟨{
    leftIndex := V.leftIndex
    rightIndex := V.rightIndex
    basis := V.basis
    weight := V.weight
    adapted := V.adapted
    basis_height := fun i j => (V.height i j).trans hpC
    subalgebra := U
    generator := v
    spanning := hv
    graded := hU
    generator_height := fun i j => (hheight i j).trans hfinal
    kills_top := hfreq ()
    denominator := m
    denominator_pos := hm
    denominator_bound := hmp.trans (Real.exp_le_exp.mpr hfinal)
    latticeConstant := κ
    latticeConstant_mem := hκ
    slow := slow
    middle := middle
    rational := rat
    product := hproduct
    slow_bound := fun α i => (hslow α i).trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr hfinal)
      (monomialScale_pos (fun _ : Fin 4 => (N : ℝ))
        (fun _ => by exact_mod_cast NeZero.pos N) α).le)
    rational_grid := hrat
    middle_zero := hmid0
    rational_zero := hrat0
    middle_coefficients := hcoeff }, rfl, rfl⟩

theorem exists_antisymmetric_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      {N : ℕ} [NeZero N] (_V : NativeAntisymmetricBoxFactorization W N p),
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeAntisymmetricOrbitFactors W N ((p + C) ^ C)) := by
  obtain ⟨C, hC, h⟩ := exists_antisymmetric_orbit_factors_indices
  refine ⟨C, hC, ?_⟩
  intro p W N _ V hN
  obtain ⟨R, _, _⟩ := h W V hN
  exact ⟨R⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_antisymmetric_factorization :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            Nonempty (NativeAntisymmetricBoxFactorization M N ((p + C) ^ C)) := by
  obtain ⟨A, _, hbox⟩ := exists_quadratic_antisymmetric_box
  obtain ⟨B, _, hstep⟩ := exists_antisymmetric_box_step_drop
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + B) ^ B := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hBC : (q + B) ^ B ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, i', j', hMbox⟩ := hbox hp f hf hG
  obtain ⟨V⟩ := hstep hq M i' j' ((Real.exp_le_exp.mpr hBC).trans hN) hMbox
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, ⟨V.mono hqC hBC⟩⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_biased_orbit :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ V : NativeAntisymmetricOrbitFactors M N ((p + C) ^ C),
              Real.exp (-((p + C) ^ C)) ≤
                (finiteBoxCorrelation (fun x y : ZMod N =>
                  star (M.evalCyclic N V.leftIndex (correlationInput x y)) *
                    M.evalCyclic N V.rightIndex (correlationInput y x))).re := by
  obtain ⟨A, _, hbox⟩ := exists_quadratic_antisymmetric_box
  obtain ⟨B, _, hstep⟩ := exists_antisymmetric_box_step_drop_indices
  obtain ⟨D, _, horbit⟩ := exists_antisymmetric_orbit_factors_indices
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let T := Q + (Q + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let a := (p + A) ^ A
  let b := (a + B) ^ B
  let t := a + b
  let u := (t + D) ^ D
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ht : 0 ≤ t := add_nonneg ha hb
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : t + u ≤ (p + C) ^ C := by
    simpa [T, Q, X, t, u, a, b, Polynomial.eval₂_pow] using hbudget p hp
  have hat : a ≤ t := le_add_of_nonneg_right hb
  have hbt : b ≤ t := le_add_of_nonneg_left ha
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right hu).trans hsum
  have huC : u ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have haC := hat.trans htC
  have hbC := hbt.trans htC
  obtain ⟨H, hH, hdense, M, i, hcorr, i', j', hMbox⟩ := hbox hp f hf hG
  obtain ⟨S, hSi, hSj⟩ := hstep ha M i' j' ((Real.exp_le_exp.mpr hbC).trans hN) hMbox
  let M' := M.mono hat
  let S' := S.mono hat hbt
  obtain ⟨V, hVi, hVj⟩ := horbit M' S' ((Real.exp_le_exp.mpr huC).trans hN)
  refine ⟨H, hH, ?_, M'.mono htC, i, ?_, V.mono htC huC, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg haC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg haC)).trans (hcorr h hh)
  · change Real.exp (-((p + C) ^ C)) ≤
      (finiteBoxCorrelation (fun x y : ZMod N =>
        star (M.evalCyclic N V.leftIndex (correlationInput x y)) *
          M.evalCyclic N V.rightIndex (correlationInput y x))).re
    have hleft : V.leftIndex = i' := hVi.trans hSi
    have hright : V.rightIndex = j' := hVj.trans hSj
    rw [hleft, hright]
    exact (Real.exp_le_exp.mpr (neg_le_neg haC)).trans hMbox

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_antisymmetric_orbit_factors :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            Nonempty (NativeAntisymmetricOrbitFactors M N ((p + C) ^ C)) := by
  obtain ⟨A, _, hsymbol⟩ := exists_quadratic_antisymmetric_factorization
  obtain ⟨B, _, horbit⟩ := exists_antisymmetric_orbit_factors
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + B) ^ B := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hBC : (q + B) ^ B ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, V⟩ :=
    hsymbol hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hG
  obtain ⟨V⟩ := V
  obtain ⟨R⟩ := horbit M V ((Real.exp_le_exp.mpr hBC).trans hN)
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, ⟨R.mono hqC hBC⟩⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)

end Erdos3

end

end OAI

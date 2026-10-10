import OAI.Combinatorics.Progressions.Fourier.CrossRowCharacterDifference
import OAI.Combinatorics.Progressions.Fourier.StepOneFamilyFourier

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_cyclic_mean_row_degree_lowering :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L 2 d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p e : ℝ}, 0 ≤ p → T.ComplexityLE p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ f : ZMod N → ZMod N → ℂ, (∀ h n, ‖f h n‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        f h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ m : ℕ, 0 < m ∧ (m + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup 2)
          (Fin (m + 1)) ((p + C) ^ C),
        D.GeometryComplexityLE ((p + C) ^ C) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
          f h n * star ((V.test T.orbit 0).eval ![(h.val : ℤ), (n.val : ℤ)])‖) ∧
        ∀ (i j : Fin (m + 1)) (k : ZMod N), ∃ K : (Fin 2 → ℤ) → ℂ,
          Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + e + C) ^ C) K) ∧
          ∀ h : ℤ, (𝔼 n : ZMod N,
            ‖cyclicSecondDifference (V.test T.orbit i).eval (V.test T.orbit j).eval k h n -
              K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
  obtain ⟨A, _, hunit⟩ := exists_unit_vertical_mean_row_model 2
  obtain ⟨B, _, hcyclic⟩ := UnitVerticalObservable.exists_cyclic_second_difference_models
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + X + Polynomial.C B) ^ B + 1)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p e hp hT he N _ hN f hf hcorr
  let u := (p + A) ^ A
  let v := (p + e + A) ^ A
  let r := (v + (p + e) + B) ^ B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have huv : u ≤ v := pow_le_pow_left₀ (by positivity) (by linarith) A
  have htotal : v + r + 1 ≤ (p + e + C) ^ C := by
    simpa [X, U, v, r, Polynomial.eval₂_pow] using hbudget (p + e) (by linarith)
  have huC : u ≤ (p + C) ^ C := by
    have hb : u + (u + p + B) ^ B + 1 ≤ (p + C) ^ C := by
      simpa [X, U, u, Polynomial.eval₂_pow] using hbudget p hp
    have hn : 0 ≤ (u + p + B) ^ B := by positivity
    linarith
  have hcost : (u + e + B) ^ B ≤ (p + e + C) ^ C := by
    have hb : (u + e + B) ^ B ≤ r :=
      pow_le_pow_left₀ (by positivity) (by linarith) B
    have hv : 0 ≤ v := by dsimp [v]; positivity
    linarith
  obtain ⟨m, hm, hmcard, V, hD, hVcorr⟩ := hunit D T hp hT
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)]) f hf hcorr
  refine ⟨m, hm, hmcard.trans (Real.exp_le_exp.mpr huC), V.mono huC,
    hD.mono D huC, (Real.exp_le_exp.mpr (neg_le_neg huC)).trans hVcorr, ?_⟩
  intro i j k
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp u := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  obtain ⟨K, ⟨E⟩, herr⟩ := hcyclic D V T.orbit hu hD hcard he hN i j k
  exact ⟨K, ⟨E.mono hcost⟩, herr⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_differenced_degree_two_rows :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L 2 d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ZMod N → ℂ, (∀ h n, ‖f h n‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        f h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ K : ZMod N → (Fin 2 → ℤ) → ℂ,
        (∀ k, Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C) (K k))) ∧
        Real.exp (-((p + C) ^ C)) ≤ (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
          multiplicativeDerivative (f h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
  obtain ⟨A, _, hunit⟩ := exists_unit_vertical_mean_row_model 2
  obtain ⟨B, _, hcyclic⟩ := UnitVerticalObservable.exists_cyclic_second_difference_models
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * Q + 2 + Polynomial.C B) ^ B + 3 * Q + 20)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f hf hcorr
  classical
  let q := (p + A) ^ A
  let e := 2 * q + 2
  let r := (3 * q + 2 + B) ^ B
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : r + 3 * q + 20 ≤ (p + C) ^ C := by
    simpa [X, Q, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := by linarith
  have heC : e ≤ (p + C) ^ C := by dsimp [e]; linarith
  have hN' : Real.exp (e + 16) ≤ (N : ℝ) :=
    (Real.exp_le_exp.mpr (by dsimp [e]; linarith)).trans hN
  obtain ⟨m, _, hmcard, V, hD, hVcorr⟩ := hunit D T hp hT
    (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)]) f hf hcorr
  have hcard : (Fintype.card (Fin (m + 1)) : ℝ) ≤ Real.exp q := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using hmcard
  have hmodels (k : ZMod N) : ∃ K : (Fin 2 → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 r K) ∧
      ∀ h : ℤ, (𝔼 n : ZMod N,
        ‖cyclicSecondDifference (V.test T.orbit 0).eval (V.test T.orbit 0).eval k h n -
          K ![h, (n.val : ℤ)]‖) ≤ Real.exp (-e) := by
    have hh := hcyclic D V T.orbit hq hD hcard he hN' 0 0 k
    have hbudgeteq : ((p + A) ^ A + e + B) ^ B = r := by
      change (q + e + B) ^ B = (3 * q + 2 + B) ^ B
      congr 1
      dsimp [e]
      ring
    simpa only [hbudgeteq] using hh
  choose K hK herror using hmodels
  let g (h n : ZMod N) := (V.test T.orbit 0).eval ![(h.val : ℤ), (n.val : ℤ)]
  have hd := mean_row_correlation_sq_le_approximated_derivatives f g
    (fun k h n => K k ![(h.val : ℤ), (n.val : ℤ)]) hf
    (ε := Real.exp (-e)) (by
      intro k h
      simpa only [g, multiplicativeDerivative, cyclicSecondDifference] using herror k h.val)
  have hs : Real.exp (-(2 * q)) ≤
      (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        multiplicativeDerivative (f h) k n * star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) +
          Real.exp (-e) := by
    have hsquare := (pow_le_pow_left₀ (Real.exp_nonneg (-q)) hVcorr 2).trans hd
    have hexp : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rwa [hexp] at hsquare
  have htwo : 2 * Real.exp (-e) ≤ Real.exp (-(2 * q)) := by
    calc
      _ ≤ Real.exp 2 * Real.exp (-e) := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [e]; ring
  refine ⟨K, fun k => ⟨(Classical.choice (hK k)).mono hrC⟩, ?_⟩
  apply (Real.exp_le_exp.mpr (neg_le_neg heC)).trans
  linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_gowers_three_of_degree_two_cross_rows :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L 2 d)
      (T : D.Niltest (fun _ : Fin 2 => 1)) {p : ℝ}, 0 ≤ p → T.ComplexityLE p →
      ∀ {N : ℕ} [NeZero N], Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ (f g : ZMod N → ℂ) (χ : ZMod N → AddChar (ZMod N) ℂ),
      (∀ n, ‖f n‖ ≤ 1) → (∀ n, ‖g n‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
        characterCrossRow f g χ h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      Real.exp (-((p + C) ^ C)) ≤ gowersNorm 3 g := by
  obtain ⟨A, _, hdifference⟩ := exists_differenced_degree_two_rows
  obtain ⟨B, _, hfourier⟩ := exists_fourier_of_stepOne_cross_family
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D T p hp hT N _ hN f g χ hf hg hcorr
  let u := (p + A) ^ A
  let v := (u + B) ^ B
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have htotal : u + v ≤ (p + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget p hp
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  obtain ⟨K, hK, hKcorr⟩ := hdifference D T hp hT
    ((Real.exp_le_exp.mpr huC).trans hN) (characterCrossRow f g χ)
    (characterCrossRow_norm f g χ hf hg) hcorr
  have hclean : Real.exp (-u) ≤ (𝔼 k : ZMod N, 𝔼 h : ZMod N, ‖𝔼 n : ZMod N,
      (multiplicativeDerivative f k n * star (multiplicativeDerivative g k (n + h))) *
        star (K k ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    simpa only [characterCrossRow_derivative_correlation_norm] using hKcorr
  obtain ⟨ψ, hψ⟩ := hfourier hu (fun k => multiplicativeDerivative f k)
    (fun k => multiplicativeDerivative g k) K
    (multiplicativeDerivative_norm_le_one f hf) (multiplicativeDerivative_norm_le_one g hg)
    hK hclean
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans
    (exp_le_gowers_three_of_mean_derivative_fourier g ψ hv hψ)

end Erdos3.RationalFilteredNilmanifold

end

end OAI

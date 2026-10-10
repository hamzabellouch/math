import OAI.Combinatorics.Progressions.Geometry.QuadraticBoxExpansion

namespace OAI

section

namespace Erdos3

theorem square_weight_comparison_error_le (z d g : ℂ) (hd : ‖d‖ ≤ 1) :
    ‖z * (‖d‖ ^ 2 : ℝ) - g * star d‖ ≤ ‖z * d - g‖ := by
  have hsquare : (‖d‖ ^ 2 : ℝ) = d * star d := by
    simp only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have heq : z * (‖d‖ ^ 2 : ℝ) - g * star d = (z * d - g) * star d := by
    rw [hsquare]
    ring
  rw [heq, norm_mul, norm_star]
  exact mul_le_of_le_one_right (norm_nonneg _) hd

theorem NativeIntegerExpansion.exists_square_weight_pair :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} {w : σ → ℕ} {s : ℕ} {p : ℝ}
      {D G : (σ → ℤ) → ℂ}, 0 ≤ p →
      NativeIntegerExpansion w s p D → NativeIntegerExpansion w s p G →
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) (fun x => (‖D x‖ ^ 2 : ℝ))) ∧
      Nonempty (NativeIntegerExpansion w s ((p + C) ^ C) (fun x => G x * star (D x))) := by
  obtain ⟨C, hC, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  refine ⟨C, hC, ?_⟩
  intro σ w s p D G hp ED EG
  obtain ⟨EW⟩ := hmul hp ED ED.conjugate
  obtain ⟨EH⟩ := hmul hp EG ED.conjugate
  refine ⟨⟨?_⟩, ⟨EH⟩⟩
  simpa only [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq] using EW

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_pair_approximation (k : ℕ) :
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
              ∃ i' j' : Fin M.outputDim, ∃ D G : (Fin 2 → ℤ) → ℂ,
                Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C) D) ∧
                Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C) G) ∧
                (∀ z, ‖D z‖ ≤ 1) ∧
                Real.exp (-(2 * q + 1)) ≤
                  (𝔼 z : Fin 2 → ZMod N, ‖D (fun j => ((z j).val : ℤ))‖ ^ 2) ∧
                Real.exp (-(2 * q + 1)) ≤ (𝔼 z : Fin 2 → ZMod N,
                  ‖M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ) *
                    D (fun j => ((z j).val : ℤ))‖ ^ 2) ∧
                (𝔼 z : Fin 2 → ZMod N,
                  ‖M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ) *
                    D (fun j => ((z j).val : ℤ)) - G (fun j => ((z j).val : ℤ))‖) ≤
                  Real.exp (-(2 * q + 1 + (p + 2) ^ k)) := by
  obtain ⟨A, _, hbox⟩ := exists_quadratic_box_expansion (k + 2)
  obtain ⟨B, _, hpair⟩ := exists_antisymmetric_pair_approximation
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (T + (2 * T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  let r := (p + 2) ^ (k + 2)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsum : t + (2 * t + B) ^ B ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (2 * t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  obtain ⟨q, hq, hqt, H, hH, hdense, M, i, hcorr, V, hbias, F, ⟨EF⟩, herr⟩ :=
    hbox hp ((Real.exp_le_exp.mpr htC).trans hN) f hf hG
  have hkernel : Real.exp (-q) ≤ (finiteBoxCorrelation (fun x y : ZMod N =>
      M.antisymmetricKernel V.leftIndex V.rightIndex (x.val : ℤ) (y.val : ℤ))).re := by
    simpa only [M.antisymmetricKernel_cyclic] using hbias
  obtain ⟨D, G, ⟨ED⟩, ⟨EG⟩, hD, hmass, henergy, herror⟩ :=
    hpair M V.leftIndex V.rightIndex F ht EF (Real.exp_pos (-q))
      (Real.exp_pos (-(4 * q + r))) hkernel herr
  have hcost : (q + t + B) ^ B ≤ (p + C) ^ C :=
    (pow_le_pow_left₀ (by positivity) (by linarith : q + t + B ≤ 2 * t + B) B).trans hBC
  have hsquare : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hratio : 2 * Real.exp (-(4 * q + r)) / Real.exp (-q) ^ 2 =
      2 * Real.exp (-(2 * q + r)) := by
    rw [hsquare, mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring
  have hgap : (p + 2) ^ k + 2 ≤ r := by
    have hstep (n : ℕ) : (p + 2) ^ n + 1 ≤ (p + 2) ^ (n + 1) := by
      have hpow : (1 : ℝ) ≤ (p + 2) ^ n := one_le_pow₀ (by linarith)
      rw [pow_succ]
      nlinarith
    dsimp [r]
    linarith [hstep k, hstep (k + 1)]
  have hlower : Real.exp (-(2 * q + 1)) ≤ Real.exp (-q) ^ 2 / 2 := by
    calc
      _ = Real.exp (-(2 * q) - 1) := by congr 1; ring
      _ ≤ Real.exp (-(2 * q)) / 2 := exp_sub_one_le_half_exp _
      _ = Real.exp (-q) ^ 2 / 2 := by rw [hsquare]
  refine ⟨q, hq, hqt.trans htC, H, hH, hdense, M, i, hcorr,
    V.leftIndex, V.rightIndex, D, G, ⟨ED.mono hcost⟩, ⟨EG.mono hcost⟩, hD,
    hlower.trans hmass, hlower.trans henergy, ?_⟩
  rw [hratio] at herror
  apply herror.trans
  calc
    _ ≤ 2 * Real.exp (-(2 * q + 1 + (p + 2) ^ k) - 1) := by gcongr; linarith
    _ ≤ _ := by linarith [exp_sub_one_le_half_exp (-(2 * q + 1 + (p + 2) ^ k))]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_weighted_symmetry_approximation (k : ℕ) :
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
              ∃ i' j' : Fin M.outputDim,
                ∃ w : (Fin 2 → ℤ) → ℝ, ∃ G : (Fin 2 → ℤ) → ℂ,
                  (∀ z, 0 ≤ w z ∧ w z ≤ 1) ∧
                  Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C)
                    (fun z => (w z : ℂ))) ∧
                  Nonempty (NativeIntegerExpansion (fun _ : Fin 2 => 1) 1 ((p + C) ^ C) G) ∧
                  Real.exp (-(2 * q + 1)) ≤
                    (𝔼 z : Fin 2 → ZMod N, w (fun j => ((z j).val : ℤ))) ∧
                  Real.exp (-(2 * q + 1)) ≤ (𝔼 z : Fin 2 → ZMod N,
                    w (fun j => ((z j).val : ℤ)) *
                      ‖M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ)‖ ^ 2) ∧
                  (𝔼 z : Fin 2 → ZMod N,
                    ‖M.antisymmetricKernel i' j' ((z 0).val : ℤ) ((z 1).val : ℤ) *
                      (w (fun j => ((z j).val : ℤ)) : ℂ) - G (fun j => ((z j).val : ℤ))‖) ≤
                    Real.exp (-(2 * q + 1 + (p + 2) ^ k)) := by
  obtain ⟨A, _, hpair⟩ := exists_quadratic_pair_approximation k
  obtain ⟨B, _, hweight⟩ := NativeIntegerExpansion.exists_square_weight_pair
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hG
  let t := (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  obtain ⟨q, hq, hqt, H, hH, hdense, M, i, hcorr, i', j', D, G, ⟨ED⟩, ⟨EG⟩,
    hD, hmass, henergy, herr⟩ := hpair hp ((Real.exp_le_exp.mpr htC).trans hN) f hf hG
  obtain ⟨⟨EW⟩, ⟨EF⟩⟩ := hweight ht ED EG
  refine ⟨q, hq, hqt.trans htC, H, hH, hdense, M, i, hcorr, i', j',
    (fun z => ‖D z‖ ^ 2), (fun z => G z * star (D z)), ?_,
    ⟨EW.mono hBC⟩, ⟨EF.mono hBC⟩, hmass, ?_, ?_⟩
  · intro z
    exact ⟨sq_nonneg _, by simpa using pow_le_pow_left₀ (norm_nonneg _) (hD z) 2⟩
  · simpa only [norm_mul, mul_pow, mul_comm] using henergy
  · apply le_trans (Finset.expect_le_expect (fun z _ =>
      square_weight_comparison_error_le _ _ _ (hD (fun j => ((z j).val : ℤ))))) herr

end Erdos3

end

end OAI

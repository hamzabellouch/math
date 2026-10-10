import OAI.Combinatorics.Progressions.Polynomial.CubicResidualPhase

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem derivative_nativeMixedResidual {s N : ℕ} [NeZero N] {p : ℝ}
    (f : ZMod N → ℂ) (M : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) p)
    (h k : ZMod N) (i : Fin M.outputDim) :
    multiplicativeDerivative (nativeMixedResidual f M h i) k =
      fun n => multiplicativeDerivative (multiplicativeDerivative f k) h n *
        star (multiplicativeDerivative (fun x => M.evalCyclic N i (correlationInput h x)) k n) := by
  have heq : multiplicativeDerivative (nativeMixedResidual f M h i) k =
      fun n => multiplicativeDerivative (multiplicativeDerivative f h) k n *
        star (multiplicativeDerivative (fun x => M.evalCyclic N i (correlationInput h x)) k n) := by
    funext n
    simp only [nativeMixedResidual, multiplicativeDerivative, star_mul, star_star]
    ring
  rw [heq, multiplicativeDerivative_comm]

namespace NativeMixedCorrelation

theorem exists_differenced_residual_correlations (s : ℕ) (hs : 3 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ W : NativeMixedCorrelation s N p f,
      ∃ i : Fin W.mixed.outputDim, ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.2 ∈ W.shifts ∧
          Nonempty (NativeVectorCorrelation (s - 2) N ((p + C) ^ C)
            (fun _ : Unit => fun n =>
              multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 n *
                star (multiplicativeDerivative
                  (fun x => W.mixed.evalCyclic N i (correlationInput t.2 x)) t.1 n))) := by
  obtain ⟨A, _, hdifference⟩ := exists_many_native_derivative_correlations (s - 2) (by omega)
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + U)
  refine ⟨C, hC, ?_⟩
  intro N _ p f hp hN hf W
  classical
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 2 * p + q ≤ (p + C) ^ C := by
    simpa [X, U, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨i, H, hsub, _, hHdense, hHcorr⟩ := W.exists_fixed_residual_coordinate
  have hdata (h : ZMod N) (hh : h ∈ H) : ∃ K : Finset (ZMod N), K.Nonempty ∧
      Real.exp (-q) * N ≤ (K.card : ℝ) ∧ ∀ k ∈ K,
        Nonempty (NativeVectorCorrelation (s - 2) N q
          (fun _ : Unit => multiplicativeDerivative (nativeMixedResidual f W.mixed h i) k)) := by
    apply hdifference hp ((Real.exp_le_exp.mpr hqC).trans hN)
      (nativeMixedResidual f W.mixed h i)
    · intro n
      change ‖multiplicativeDerivative f h n * star (W.mixed.evalCyclic N i (correlationInput h n))‖ ≤ 1
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (multiplicativeDerivative_norm_le_one f hf h n)).trans (W.mixed.norm_eval _ _)
    · simpa only [show s - 2 + 1 = s - 1 by omega] using hHcorr h hh
  let K (h : ZMod N) := if hh : h ∈ H then Classical.choose (hdata h hh) else ∅
  have hK (h : ZMod N) (hh : h ∈ H) : Real.exp (-q) * N ≤ ((K h).card : ℝ) ∧
      ∀ k ∈ K h, Nonempty (NativeVectorCorrelation (s - 2) N q
        (fun _ : Unit => multiplicativeDerivative (nativeMixedResidual f W.mixed h i) k)) := by
    simpa only [K, dite_eq_left hh] using (Classical.choose_spec (hdata h hh)).2
  let Q := H.biUnion (fun h => (K h).image (fun k => (k, h)))
  have hQcard : Q.card = ∑ h ∈ H, (K h).card := by
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro h _
      exact Finset.card_image_of_injective _ (fun a b hab => (Prod.mk.inj hab).1)
    · intro a _ b _ hab
      apply Finset.disjoint_left.mpr
      intro t hta htb
      obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hta
      obtain ⟨_, _, heq⟩ := Finset.mem_image.mp htb
      exact hab (Prod.mk.inj heq).2.symm
  have hQdense : Real.exp (-(2 * p + q)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) := by
    calc
      _ = (Real.exp (-(2 * p)) * N) * (Real.exp (-q) * N) := by
        rw [neg_add, Real.exp_add]
        ring
      _ ≤ (H.card : ℝ) * (Real.exp (-q) * N) :=
        mul_le_mul_of_nonneg_right hHdense (by positivity)
      _ = ∑ h ∈ H, Real.exp (-q) * (N : ℝ) := by simp
      _ ≤ ∑ h ∈ H, ((K h).card : ℝ) := Finset.sum_le_sum (fun h hh => (hK h hh).1)
      _ = (Q.card : ℝ) := by rw [hQcard, Nat.cast_sum]
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le (by positivity : 0 < Real.exp (-(2 * p + q)) * (N : ℝ) ^ 2) hQdense
  refine ⟨i, Q, hQ, (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg htotal)) (sq_nonneg _)).trans hQdense, ?_⟩
  intro t ht
  obtain ⟨h, hh, ht⟩ := Finset.mem_biUnion.mp ht
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp ht
  cases heq
  refine ⟨hsub hh, ?_⟩
  obtain ⟨V⟩ := (hK h hh).2 k hk
  simpa only [derivative_nativeMixedResidual] using (show Nonempty _ from ⟨V.mono hqC⟩)

end NativeMixedCorrelation

end Erdos3

end

end OAI

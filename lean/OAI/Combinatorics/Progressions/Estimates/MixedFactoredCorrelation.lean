import OAI.Combinatorics.Progressions.Geometry.MixedAntisymmetricBox
import OAI.Combinatorics.Progressions.Geometry.MixedBoxFactorizationTransport

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem NativeMultidegreeNilcharacter.exists_mixed_sum_box_factorization (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p)
      {N : ℕ} [NeZero N] (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ (i : Fin W.outputDim) (A : Fin (n + 2) → (Fin (n + 2) → ZMod N) → ℂ),
      (∀ j x, ‖A j x‖ ≤ 1) → (∀ j, MissesBoxCoordinate (A j) j) →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      Real.exp (-p) ≤ ‖𝔼 u : Fin n → ZMod N, 𝔼 m : ZMod N, 𝔼 h : ZMod N,
        f (m + h + ∑ j, u j) * star (W.eval i (mixedSlotInput (h.val : ℤ) m.val (fun j => (u j).val))) *
          ∏ j, A j (Fin.cons h (Fin.cons m u))‖ →
      ∃ hpC : p ≤ (p + C) ^ C,
        Nonempty (NativeMixedBoxFactorization (W.mono hpC) N ((p + C) ^ C)) := by
  obtain ⟨a, _, hbox⟩ := NativeMultidegreeNilcharacter.exists_mixed_sum_antisymmetric_box n
  obtain ⟨b, _, hstep⟩ := exists_mixed_box_step_drop_indices n
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C a) ^ a
  let R := X + Q + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W N _ f hf i A hA hmiss hN hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  let r := p + q + 2
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpr : p ≤ r := by dsimp only [r]; linarith
  have hqr : q ≤ r := by dsimp only [r]; linarith
  have hr : 0 ≤ r := hp.trans hpr
  have hsum : r + (r + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + b) ^ b := by positivity
  have hrC : r ≤ (p + C) ^ C := by linarith
  have hcost : (r + b) ^ b ≤ (p + C) ^ C := by linarith
  obtain ⟨j, k, hmoment⟩ := hbox W f hf i A hA hmiss hcorr
  have hmono (x : Fin (n + 2) → ℤ) :
      (W.mono hpr).mixedAntisymmetric j k x = W.mixedAntisymmetric j k x := rfl
  have hinput : Real.exp (-r) ≤
      (boxPhaseMoment (n + 2) (fun x : Fin (n + 2) → ZMod N =>
        (W.mono hpr).mixedAntisymmetric j k (fun l => (x l).val))).re := by
    simpa only [hmono] using (Real.exp_le_exp.mpr (neg_le_neg hqr)).trans hmoment
  obtain ⟨S, _, _⟩ := hstep hr (W.mono hpr) j k
    ((Real.exp_le_exp.mpr hcost).trans hN) hinput
  exact ⟨hpr.trans hrC, ⟨S.mono hrC hcost⟩⟩

end Erdos3

end

end OAI

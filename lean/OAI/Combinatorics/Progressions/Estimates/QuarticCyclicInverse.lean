import OAI.Combinatorics.Progressions.Estimates.AxisCompression
import OAI.Combinatorics.Progressions.Nilpotent.QuarticPrimitiveNiltest

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_quartic_primitive_correlation_large_modulus :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 5 f →
      ∃ g ∈ nativeCyclicFunctions 4 N ((p + C) ^ C),
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  obtain ⟨A, _, hprimitive⟩ := exists_quartic_primitive_gowers_four
  obtain ⟨B, _, hinverse⟩ := exists_cyclicNativeInverse_three
  obtain ⟨D, _, hmodel⟩ := NativeMultidegreeNilcharacter.exists_quartic_primitive_niltest_budget
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let V := (U + 2 + Polynomial.C B) ^ B
  let R := U + V + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + V + (R + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let v := (u + 2 + B) ^ B
  let r := u + v + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have htotal : u + v + (r + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, U, V, R, u, v, r, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (r + D) ^ D := by positivity
  have huC : u ≤ (p + C) ^ C := by linarith
  have hvC : v ≤ (p + C) ^ C := by linarith
  have hmC : (r + D) ^ D ≤ (p + C) ^ C := by linarith
  obtain ⟨q, hq, hqu, W, i, hW⟩ :=
    hprimitive hp ((Real.exp_le_exp.mpr huC).trans hN) f hf hGowers
  obtain ⟨g, ⟨G⟩, hg⟩ := hinverse (by linarith : 2 ≤ u + 2)
    (W.quarticPrimitiveFactor f i) (W.quarticPrimitiveFactor_norm f hf i)
    ((Real.exp_le_exp.mpr (by linarith : -(u + 2) ≤ -u)).trans hW)
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hvr : v ≤ r := by dsimp [r]; linarith
  have hgmodel : g ∈ nativeCyclicFunctions 3 N r :=
    ⟨{ G with complexity := G.complexity.mono hvr }⟩
  have hm := hmodel hr (W.mono hqr) i g hgmodel
  have hm' : (fun n : ZMod N => star (W.eval i (fun _ => (n.val : ℤ))) * g n) ∈
      nativeCyclicFunctions 4 N ((r + D) ^ D) := by
    simpa only [NativeMultidegreeNilcharacter.mono_eval] using hm
  obtain ⟨M⟩ := hm'
  refine ⟨fun n => star (W.eval i (fun _ => (n.val : ℤ))) * g n,
    ⟨{ M with complexity := M.complexity.mono hmC }⟩, ?_⟩
  have heq : (𝔼 n : ZMod N, f n * star (star (W.eval i (fun _ => (n.val : ℤ))) * g n)) =
      𝔼 n : ZMod N, W.quarticPrimitiveFactor f i n * star (g n) := by
    apply Finset.expect_congr rfl
    intro n _
    simp only [NativeMultidegreeNilcharacter.quarticPrimitiveFactor, star_mul, star_star]
    ring
  rw [heq]
  exact (Real.exp_le_exp.mpr (neg_le_neg hvC)).trans hg

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra NativeCyclicModel.topology
  NativeCyclicModel.topologicalAdd NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_cyclicNativeInverse_four : ∃ C : ℕ, 2 ≤ C ∧ CyclicNativeInverse 4 C := by
  obtain ⟨A, _, hlarge⟩ := exists_quartic_primitive_correlation_large_modulus
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + 32 * X + 211)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hGowers
  have hp0 : 0 ≤ p := by linarith
  let u := (p + A) ^ A
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + 32 * p + 211 ≤ (p + C) ^ C := by
    simpa [X, u, Polynomial.eval₂_pow] using hbudget p hp0
  have huC : u ≤ (p + C) ^ C := by linarith
  by_cases hN : Real.exp u ≤ (N : ℝ)
  · obtain ⟨g, ⟨M⟩, hcorr⟩ := hlarge hp0 hN f hf hGowers
    exact ⟨g, ⟨{ M with complexity := M.complexity.mono huC }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg huC)).trans hcorr⟩
  · obtain ⟨g, ⟨M⟩, hcorr⟩ :=
      exists_native_cyclic_small_modulus_correlation 4 (by omega) (not_le.mp hN).le f hf hGowers
    have h211 : (211 : ℝ) ≤ (p + C) ^ C := by linarith
    have hc : 32 * p + u ≤ (p + C) ^ C := by linarith
    exact ⟨g, ⟨{ M with complexity := M.complexity.mono h211 }⟩,
      (Real.exp_le_exp.mpr (neg_le_neg hc)).trans hcorr⟩

end Erdos3

end

end OAI

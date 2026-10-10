import OAI.Combinatorics.Progressions.Estimates.CubicFrozenLinearRows
import OAI.Combinatorics.Progressions.Estimates.CubicPrimitiveRows
import OAI.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction

namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeMeanRowCorrelation.lie NativeMeanRowCorrelation.algebra
  NativeMeanRowCorrelation.topology NativeMeanRowCorrelation.topologicalAdd
  NativeMeanRowCorrelation.continuousSMul NativeMeanRowCorrelation.hausdorff

theorem exists_cubic_primitive_fourier_rows :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
        ∃ W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) q,
        ∃ a : Fin W.outputDim × Fin W.outputDim, ∃ χ : ZMod N → AddChar (ZMod N) ℂ,
          Nonempty (NativeMeanRowCorrelation (fun _ : Fin 2 => 1) 2 ((p + C) ^ C)
            (fun h n : ZMod N => ![(h.val : ℤ), (n.val : ℤ)])
            (fun h n => (W.cubicPrimitiveFactor f a.1 n *
              star (W.cubicPrimitiveFactor f a.2 (n + h))) * star (χ h n))) := by
  obtain ⟨A, _, hrows⟩ := exists_cubic_primitive_rows
  obtain ⟨B, _, hlinear⟩ := NativeMultidegreeNilcharacter.exists_cubicHhnTensor_row_expansion
  obtain ⟨D, _, heliminate⟩ := exists_characters_of_stepOne_rows
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C A) ^ A
  let Q := (P + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Q + Polynomial.C D) ^ D)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let u := (p + A) ^ A
  let t := (u + B) ^ B
  let r := u + t
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hur : u ≤ r := le_add_of_nonneg_right ht
  have htr : t ≤ r := le_add_of_nonneg_left hu
  have hsum : u + (r + D) ^ D ≤ (p + C) ^ C := by
    simpa [X, P, Q, u, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have huc : u ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hrc : (r + D) ^ D ≤ (p + C) ^ C := (le_add_of_nonneg_left hu).trans hsum
  obtain ⟨q, hq, hqu, W, a, b, χ, ⟨V⟩⟩ :=
    hrows hp ((Real.exp_le_exp.mpr huc).trans hN) f hf hGowers
  let F : ZMod N → ZMod N → ℂ := fun h n =>
    (W.cubicPrimitiveFactor f a.1 n * star (W.cubicPrimitiveFactor f a.2 (n + h))) *
      star (χ h n) * star (V.test.eval ![(h.val : ℤ), (n.val : ℤ)])
  let g : ZMod N → (Unit → ℤ) → ℂ := fun h x => star (W.cubicHhnTensor b ![(h.val : ℤ), x ()])
  have hF (h n : ZMod N) : ‖F h n‖ ≤ Real.exp r := by
    dsimp only [F]
    rw [norm_mul, norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans
      ((V.test.eval_budget V.complexity _).trans (Real.exp_le_exp.mpr hur))
    rw [norm_mul, norm_star, AddChar.norm_apply, mul_one, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (W.cubicPrimitiveFactor_norm f hf _ _)).trans
      (W.cubicPrimitiveFactor_norm f hf _ _)
  have hg (h n : ZMod N) : ‖g h (fun _ => (n.val : ℤ))‖ ≤ 1 := by
    dsimp only [g]
    rw [norm_star]
    exact W.cubicHhnTensor_norm _ _
  have hqt : (q + B) ^ B ≤ t := pow_le_pow_left₀ (by positivity) (by linarith) B
  have hE (h : ZMod N) : Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) 1 r (g h)) :=
    ⟨(Classical.choice (hlinear W h.val b)).conjugate.mono (hqt.trans htr)⟩
  have hcorr : Real.exp (-r) ≤ 𝔼 h : ZMod N,
      ‖𝔼 n : ZMod N, F h n * star (g h (fun _ => (n.val : ℤ)))‖ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hur)).trans
    simpa only [F, g, star_star, mul_assoc, mul_comm, mul_left_comm] using V.correlation
  obtain ⟨ψ, hψ⟩ := heliminate hr F g hF hg hE hcorr
  let χ' (h : ZMod N) : AddChar (ZMod N) ℂ := χ h * ψ h
  have hrow (h : ZMod N) : finiteFourierCoeff (F h) (ψ h) =
      𝔼 n : ZMod N, (W.cubicPrimitiveFactor f a.1 n *
        star (W.cubicPrimitiveFactor f a.2 (n + h))) * star (χ' h n) *
          star (V.test.eval ![(h.val : ℤ), (n.val : ℤ)]) := by
    unfold finiteFourierCoeff
    apply Finset.expect_congr rfl
    intro n _
    change ((W.cubicPrimitiveFactor f a.1 n * star (W.cubicPrimitiveFactor f a.2 (n + h))) *
      star (χ h n) * star (V.test.eval ![(h.val : ℤ), (n.val : ℤ)])) * star (ψ h n) =
        (W.cubicPrimitiveFactor f a.1 n * star (W.cubicPrimitiveFactor f a.2 (n + h))) *
          star (χ h n * ψ h n) * star (V.test.eval ![(h.val : ℤ), (n.val : ℤ)])
    rw [star_mul]
    ring
  refine ⟨q, hq, hqu.trans huc, W, a, χ', ⟨{
    L := V.L
    dim := V.dim
    model := V.model
    test := V.test
    complexity := V.complexity.mono huc
    correlation := ?_ }⟩⟩
  exact (Real.exp_le_exp.mpr (neg_le_neg hrc)).trans (by simpa only [hrow] using hψ)

end Erdos3

end

end OAI

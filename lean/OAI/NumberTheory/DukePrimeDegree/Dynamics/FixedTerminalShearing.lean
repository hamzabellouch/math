import OAI.NumberTheory.DukePrimeDegree.Geometry.RightObservableUniformity
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingWindow

namespace OAI

/-!
# A fixed terminal fraction for every eventual shearing limit

The fraction is chosen using only the fixed displacement scale, the
compact set of possible limits and the finite test family. It does not
shrink along the sequence. Hence a previously chosen generic set gives
valid control at the pair-dependent stopping times.
-/

noncomputable section
open Matrix Set Filter MeasureTheory
open scoped Topology Classical

namespace DukePrimeDegree
open PrimeDegreePackets

lemma slMatrixDifference_triangle {n : ℕ} (g h k : G n) :
    slMatrixDifference g k ≤ slMatrixDifference g h + slMatrixDifference h k := by
  simp only [slMatrixDifference, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact abs_sub_le (g.val i j) (h.val i j) (k.val i j)

lemma slMatrixDifference_le_of_entries {n : ℕ} (g h : G n) (C : ℝ)
    (hC : ∀ i j, |g.val i j - h.val i j| ≤ C) :
    slMatrixDifference g h ≤ (n : ℝ) * n * C := by
  calc
    slMatrixDifference g h ≤ ∑ _i : Fin n, ∑ _j : Fin n, C := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun j _ => hC i j)
    _ = (n : ℝ) * n * C := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The same fixed fraction works for all roots and every sequence with
the specified bounded stopping intervals. -/
theorem exists_fixed_terminal_observable_fraction {n : ℕ}
    (F : Finset (CompactlySupportedContinuousMap (X n) ℝ))
    (K : Set (G n)) (hK : IsCompact K)
    (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (i j : Fin n) (hij : i ≠ j)
        (g : ℕ → G n) (T : ℕ → ℝ),
        (∀ k, 0 < T k) →
        (∀ k, ∀ t ∈ Icc 0 (T k), rootShearSize hij (g k) t ≤ a) →
        ∀ h ∈ K,
          Tendsto (fun k => Matrix.SpecialLinearGroup.transvection hij (T k) * g k *
            Matrix.SpecialLinearGroup.transvection hij (-(T k))) atTop (𝓝 h) →
          ∀ᶠ k in atTop, ∀ s ∈ Icc (1 - δ) 1, ∀ f ∈ F, ∀ x : X n,
            |f (rightAction x (Matrix.SpecialLinearGroup.transvection hij (s * T k) *
                g k * Matrix.SpecialLinearGroup.transvection hij (-(s * T k)))) -
              f (rightAction x h)| < ε := by
  obtain ⟨η, hη, hηtest⟩ :=
    exists_finite_uniform_right_observable_tolerance F K hK ε hε
  let C : ℝ := (n : ℝ) * n * (17 * a)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let δ := min (1 / 2 : ℝ) (η / (4 * (C + 1)))
  have hden : 0 < 4 * (C + 1) := by positivity
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hη hden)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hCδ : C * δ < η / 2 := by
    have hb : δ * (4 * (C + 1)) ≤ η :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    nlinarith
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro i j hij g T hT hbound h hh hlim
  let A (k : ℕ) := Matrix.SpecialLinearGroup.transvection hij (T k) * g k *
    Matrix.SpecialLinearGroup.transvection hij (-(T k))
  have hdist : Tendsto (fun k => slMatrixDifference (A k) h) atTop (𝓝 0) := by
    simpa only [A, Function.comp_def, slMatrixDifference_self] using
      continuous_slMatrixDifference.continuousAt.tendsto.comp
        (hlim.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => h) atTop (𝓝 h)))
  filter_upwards [hdist.eventually (gt_mem_nhds (half_pos hη))] with k hk
  intro s hs f hf x
  let B := Matrix.SpecialLinearGroup.transvection hij (s * T k) * g k *
    Matrix.SpecialLinearGroup.transvection hij (-(s * T k))
  have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
  have hBA : slMatrixDifference B (A k) ≤ C * δ := by
    have hentry := slMatrixDifference_le_of_entries B (A k) (17 * a * (1 - s))
      (root_conjugation_terminal_window hij (g k) (hT k) (hbound k) s hs01)
    have heq : (n : ℝ) * n * (17 * a * (1 - s)) = C * (1 - s) := by
      dsimp only [C]
      ring
    rw [heq] at hentry
    exact hentry.trans (mul_le_mul_of_nonneg_left (by linarith [hs.1]) hC)
  apply hηtest f hf B h hh _ x
  exact (slMatrixDifference_triangle B (A k) h).trans_lt (by linarith)

end DukePrimeDegree

end

end OAI

import OAI.Geometry.Immersion.ClosedSurface.FiniteMean

namespace OAI

/-! A uniform version of finite mean substitution: the admissible size is
chosen from the majorants before the actual mean operator is chosen. -/
noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteMean
open ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_substitution_uniform_inputs {r0 r1 : ℝ} (hgap : r0 < r1) {L : ℕ}
    {B K : ℕ → ℝ → ℝ}
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (n : ℕ) :
    ∃ η0 : ℝ, 0 < η0 ∧ η0 ≤ 1 ∧
      ∀ (U : Set E), UniqueDiffOn ℝ U → ∀ s : ℝ, 0 ≤ s → ∀ reference H : E → F,
      ContDiffOn ℝ ∞ H U → (∀ p ∈ U, ‖H p - reference p‖ ≤ r0) →
      (∀ m, WeightedBound U s m (C m) H) →
      ∀ (T : ℝ → (E → F) → E → F), MeanBounds U s reference r1 L T B K →
      ∀ η, 0 < η → η ≤ η0 →
      ∀ j ≤ n, ContDiffOn ℝ ∞ (trial H T η j) U ∧
        InTrialBall U reference r1 (trial H T η j) ∧
        (∀ m, WeightedBound U s m (sizeBound L C B j m) (trial H T η j)) ∧
        (∀ m, WeightedBound U s m (differenceBound L C B K j m * η ^ (j + 1))
          (trial H T η j + T η (trial H T η j) - H)) := by
  obtain ⟨D, hD, hbD⟩ := finite_upper (fun j => B 0 (sizeBound L C B j L)) n
  let η0 := min 1 ((r1 - r0) / (2 * D))
  have hη0 : 0 < η0 := lt_min (by norm_num) (div_pos (sub_pos.mpr hgap) (by linarith))
  refine ⟨η0, hη0, min_le_left _ _, ?_⟩
  intro U hU s hs reference H hH hH0 hbH T hT η hη hsmall
  have hη1 : η ≤ 1 := hsmall.trans (min_le_left _ _)
  have hηD : r0 + η * D < r1 := by
    have hh : η ≤ (r1 - r0) / (2 * D) := hsmall.trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by linarith : 0 < 2 * D)).mp hh
    nlinarith
  have hstates : ∀ j ≤ n + 1,
      ContDiffOn ℝ ∞ (trial H T η j) U ∧ InTrialBall U reference r1 (trial H T η j) ∧
      ∀ m, WeightedBound U s m (sizeBound L C B j m) (trial H T η j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨hH, fun p hp => (hH0 p hp).trans_lt hgap, hbH⟩
    | succ j ih =>
      intro hj
      obtain ⟨hjS, hjBall, hjB⟩ := ih (by omega)
      have hTS := hT.smooth η hη hη1 _ hjS hjBall
      have hVal (m : ℕ) := hT.value η hη hη1 m (sizeBound L C B j (m + L))
        (trial H T η j) (sizeBound_ge_one hC hT.B_pos _ _) hjS hjBall (hjB (m + L))
      refine ⟨hH.sub hTS, ?_, ?_⟩
      · intro p hp
        calc
          ‖trial H T η (j + 1) p - reference p‖ =
              ‖(H p - reference p) - T η (trial H T η j) p‖ := by
            congr 1
            dsimp [trial]
            abel
          _ ≤ ‖H p - reference p‖ + ‖T η (trial H T η j) p‖ := norm_sub_le _ _
          _ ≤ r0 + η * D := by
            apply add_le_add (hH0 p hp)
            exact ((hVal 0).norm_le hp).trans (mul_le_mul_of_nonneg_left (by simpa using hbD j (by omega)) hη.le)
          _ < r1 := hηD
      · intro m
        have hh := (hbH m).sub hU hs hH hTS (hVal m)
        apply hh.mono_const
        dsimp only [sizeBound]
        have hp : 0 ≤ B m (sizeBound L C B j (m + L)) :=
          le_trans zero_le_one (hT.B_pos m _ (sizeBound_ge_one hC hT.B_pos j (m + L)))
        nlinarith
  have hdiff : ∀ j ≤ n, ∀ m,
      WeightedBound U s m (differenceBound L C B K j m * η ^ (j + 1))
        (trial H T η (j + 1) - trial H T η j) := by
    intro j
    induction j with
    | zero =>
      intro hj m
      have hBall : InTrialBall U reference r1 H := fun p hp => (hH0 p hp).trans_lt hgap
      have hTS := hT.smooth η hη hη1 H hH hBall
      have hh := (hT.value η hη hη1 m (C (m + L)) H (hC _) hH hBall (hbH _)).neg hU hTS
      have he : trial H T η (0 + 1) - trial H T η 0 = -(T η H) := by
        funext p; simp only [trial, Pi.sub_apply, Pi.neg_apply]; abel
      rw [he]
      have hh' : WeightedBound U s m (η * B m (C (m + L))) (-(T η H)) :=
        hh.congr (by intro p hp; rfl)
      convert hh' using 1
      try rfl
      dsimp only [differenceBound]
      simp only [Nat.zero_add, pow_one]
      ring
    | succ j ih =>
      intro hj m
      obtain ⟨hf, hfBall, hbf⟩ := hstates (j + 1) (by omega)
      obtain ⟨hg, hgBall, hbg⟩ := hstates j (by omega)
      let C' := max (sizeBound L C B (j + 1) (m + L)) (sizeBound L C B j (m + L))
      have hC' : 1 ≤ C' := (sizeBound_ge_one hC hT.B_pos _ _).trans (le_max_left _ _)
      have hD' : 0 ≤ differenceBound L C B K j (m + L) * η ^ (j + 1) :=
        mul_nonneg (differenceBound_nonneg hC hT.B_pos hT.K_pos _ _) (pow_nonneg hη.le _)
      have hh := hT.difference η hη hη1 m C' _ _ _ hC' hD' hf hg hfBall hgBall
        ((hbf (m + L)).mono_const (le_max_left _ _))
        ((hbg (m + L)).mono_const (le_max_right _ _)) (ih (by omega) (m + L))
      have hTF := hT.smooth η hη hη1 _ hf hfBall
      have hTG := hT.smooth η hη hη1 _ hg hgBall
      have hn := hh.neg hU (hTF.sub hTG)
      rw [show j + 1 + 1 = j + 2 by omega, trial_difference]
      convert hn using 1
      try rfl
      dsimp only [differenceBound, C']
      rw [pow_succ]
      ring
  intro j hj
  obtain ⟨hjS, hjBall, hjB⟩ := hstates j (by omega)
  refine ⟨hjS, hjBall, hjB, ?_⟩
  intro m
  rw [trial_residual]
  have hnext := (hstates (j + 1) (by omega)).1
  exact (hdiff j hj m).neg hU (hnext.sub hjS)

theorem finite_substitution_uniform {U : Set E} (hU : UniqueDiffOn ℝ U) {s : ℝ} (hs : 0 ≤ s)
    {reference H : E → F} {r0 r1 : ℝ} (hgap : r0 < r1) {L : ℕ}
    {B K : ℕ → ℝ → ℝ}
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (hH : ContDiffOn ℝ ∞ H U)
    (hH0 : ∀ p ∈ U, ‖H p - reference p‖ ≤ r0)
    (hbH : ∀ m, WeightedBound U s m (C m) H) (n : ℕ) :
    ∃ η0 : ℝ, 0 < η0 ∧ η0 ≤ 1 ∧
      ∀ (T : ℝ → (E → F) → E → F), MeanBounds U s reference r1 L T B K →
      ∀ η, 0 < η → η ≤ η0 →
      ∀ j ≤ n, ContDiffOn ℝ ∞ (trial H T η j) U ∧
        InTrialBall U reference r1 (trial H T η j) ∧
        (∀ m, WeightedBound U s m (sizeBound L C B j m) (trial H T η j)) ∧
        (∀ m, WeightedBound U s m (differenceBound L C B K j m * η ^ (j + 1))
          (trial H T η j + T η (trial H T η j) - H)) := by
  obtain ⟨η0,hη0,hη1,ht⟩ := finite_substitution_uniform_inputs (E := E) (F := F)
    (B := B) (K := K) hgap hC n
  exact ⟨η0,hη0,hη1,ht U hU s hs reference H hH hH0 hbH⟩

end ClosedSurfaceR4.FiniteMean

end

end OAI

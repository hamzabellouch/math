import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfilePhysicalPath
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.LocalUniformSubsequence
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace OAI

/-! # Local space-time compactness of the actual expanding-torus flow -/

open Set Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] expandingProfileTrajectory expandingTorusFunction expandingSpacetimePath

theorem exists_expandingProfile_localUniform_limit (a b k Q M T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hT : 0 ≤ T) (m : ℕ) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (q : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ n t, ‖q n t‖ ≤ Q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) :
    ∃ v : C(Icc (0 : ℝ) T × E, ℂ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => expandingProfilePhysicalPath a b (k + 2) (L (φ n)) T
        ha ha1 (by linarith) (hL (φ n)) hT m Q hQ (q (φ n)) (hq (φ n)) (f (φ n)))
        atTop (𝓝 v) := by
  let F := fun n => expandingProfilePhysicalPath a b (k + 2) (L n) T
    ha ha1 (by linarith) (hL n) hT m Q hQ (q n) (hq n) (f n)
  let U := fun n => expandingProfileTrajectory a b (k + 2) (L n) T
    ha ha1 (by linarith) (hL n) hT m Q hQ (q n) (hq n) (f n)
  obtain ⟨K, hK, hKb⟩ := exists_expandingProfileTrajectory_bound a b (k + 2)
    ha ha1 (by linarith) m Q hQ
  let A := (K + 1) * Real.exp ((K + 1) * T) * M
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hU (n : ℕ) (t : Icc (0 : ℝ) T) : ‖U n t‖ ≤ A := by
    apply (ContinuousMap.norm_coe_le_norm (U n) t).trans
    exact (hKb (L n) T (hL n) hT (q n) (hq n) (f n)).trans
      (mul_le_mul_of_nonneg_left (hf n) (by positivity))
  have hspace (n : ℕ) (t : Icc (0 : ℝ) T) (x y : E) :
      ‖F n (t, x) - F n (t, y)‖ ≤ expandingJetBound a k * A * ‖x - y‖ :=
    expandingSpacetimePath_space_bound a k (L n) T A ha ha1 hk (hL n) (U n) (hU n) t x y
  have hJA : 0 ≤ expandingJetBound a k * A :=
    mul_nonneg (by dsimp [expandingJetBound, expandingEmbeddingBound]; positivity) hA
  have heq : Equicontinuous (fun n => (F n : Icc (0 : ℝ) T × E → ℂ)) := by
    intro p
    obtain ⟨C, hC, hCb⟩ := exists_expandingProfile_time_bound a b k Q M T ‖p.2‖
      ha ha1 hk hQ hM hT (norm_nonneg _) m
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun z => (C + expandingJetBound a k * A) * dist p z)
      (by
        have hc : Continuous (fun z : Icc (0 : ℝ) T × E =>
            (C + expandingJetBound a k * A) * dist p z) :=
          continuous_const.mul (continuous_const.dist continuous_id)
        simpa only [dist_self, mul_zero] using hc.tendsto p)
    filter_upwards [] with z n
    rw [dist_eq_norm]
    have ht : ‖F n p - F n (z.1, p.2)‖ ≤ C * |(p.1 : ℝ) - z.1| := by
      simpa only [F, expandingProfilePhysicalPath, expandingSpacetimePath_apply] using
        hCb (L n) (hL n) (q n) (hq n) (f n) (hf n) z.1 p.1 p.2 le_rfl
    have hd₁ : |(p.1 : ℝ) - z.1| ≤ dist p z :=
      le_max_left _ _
    have hd₂ : ‖p.2 - z.2‖ ≤ dist p z := by
      change dist p.2 z.2 ≤ max (dist p.1 z.1) (dist p.2 z.2)
      exact le_max_right _ _
    calc
      _ ≤ ‖F n p - F n (z.1, p.2)‖ + ‖F n (z.1, p.2) - F n z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C * |(p.1 : ℝ) - z.1| + expandingJetBound a k * A * ‖p.2 - z.2‖ :=
        add_le_add ht (hspace n z.1 p.2 z.2)
      _ ≤ C * dist p z + expandingJetBound a k * A * dist p z :=
        add_le_add (mul_le_mul_of_nonneg_left hd₁ hC)
          (mul_le_mul_of_nonneg_left hd₂ hJA)
      _ = _ := (add_mul _ _ _).symm
  apply exists_localUniform_subsequence F heq
  intro p
  exact ⟨expandingEmbeddingBound a (k + 2) * A, fun n =>
    expandingSpacetimePath_norm_le a (k + 2) (L n) T A ha ha1 (by linarith)
      (hL n) (U n) (hU n) p⟩

end DefocusingNLS

end OAI

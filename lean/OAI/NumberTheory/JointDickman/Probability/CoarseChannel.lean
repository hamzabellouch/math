import OAI.NumberTheory.JointDickman.Probability.CenteredKernelRows
import Mathlib.Topology.MetricSpace.Lipschitz

namespace OAI

/-!
# Coarse centering of a smooth mixture kernel

A bounded Lipschitz profile changes little inside each coarse cell. Its
common-variable mixture is consequently close to a kernel depending only
on the coarse indices. Combining this fact with a discarded row bound
gives the finite coarse-channel estimate.
-/

namespace JointDickman

open scoped BigOperators NNReal

noncomputable def smoothMixtureKernel {C A : Type*} [Fintype C]
    (w : C → ℝ) (f : C → ℝ → ℝ) (location : A → ℝ) (a b : A) : ℝ :=
  ∑ c, w c * f c (location a) * f c (location b)

/-- Oscillation of the genuine mixture follows from the Lipschitz
profiles, rather than from an assumed kernel oscillation estimate. -/
theorem smoothMixtureKernel_oscillation {C A : Type*} [Fintype C]
    (w : C → ℝ) (f : C → ℝ → ℝ) (location : A → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    {M mesh : ℝ} {L₀ : ℝ≥0} (hM : 0 ≤ M) (hmesh : 0 ≤ mesh)
    (hf : ∀ c x, |f c x| ≤ M) (hLip : ∀ c, LipschitzWith L₀ (f c))
    (a a' b b' : A) (ha : |location a - location a'| ≤ mesh)
    (hb : |location b - location b'| ≤ mesh) :
    |smoothMixtureKernel w f location a b - smoothMixtureKernel w f location a' b'| ≤
      2 * M * (L₀ : ℝ) * mesh := by
  have hLM : 0 ≤ (L₀ : ℝ) * mesh := mul_nonneg L₀.coe_nonneg hmesh
  have hpoint (c : C) :
      |f c (location a) * f c (location b) - f c (location a') * f c (location b')| ≤
        2 * M * (L₀ : ℝ) * mesh := by
    have ha' : |f c (location a) - f c (location a')| ≤ (L₀ : ℝ) * mesh := by
      have h := (hLip c).dist_le_mul (location a) (location a')
      rw [Real.dist_eq, Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left ha L₀.coe_nonneg)
    have hb' : |f c (location b) - f c (location b')| ≤ (L₀ : ℝ) * mesh := by
      have h := (hLip c).dist_le_mul (location b) (location b')
      rw [Real.dist_eq, Real.dist_eq] at h
      exact h.trans (mul_le_mul_of_nonneg_left hb L₀.coe_nonneg)
    calc
      _ = |(f c (location a) - f c (location a')) * f c (location b) +
          f c (location a') * (f c (location b) - f c (location b'))| := by congr 1; ring
      _ ≤ |(f c (location a) - f c (location a')) * f c (location b)| +
          |f c (location a') * (f c (location b) - f c (location b'))| := abs_add_le _ _
      _ = |f c (location a) - f c (location a')| * |f c (location b)| +
          |f c (location a')| * |f c (location b) - f c (location b')| := by
        rw [abs_mul, abs_mul]
      _ ≤ ((L₀ : ℝ) * mesh) * M + M * ((L₀ : ℝ) * mesh) := add_le_add
        (mul_le_mul ha' (hf c _) (abs_nonneg _) hLM)
        (mul_le_mul (hf c _) hb' (abs_nonneg _) hM)
      _ = _ := by ring
  calc
    _ = |∑ c, w c *
        (f c (location a) * f c (location b) - f c (location a') * f c (location b'))| := by
      unfold smoothMixtureKernel
      rw [← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ ∑ c, |w c *
        (f c (location a) * f c (location b) - f c (location a') * f c (location b'))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, w c *
        |f c (location a) * f c (location b) - f c (location a') * f c (location b')| := by
      simp_rw [abs_mul, abs_of_nonneg (hw _)]
    _ ≤ ∑ c, w c * (2 * M * (L₀ : ℝ) * mesh) :=
      Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hpoint c) (hw c)
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

/-- A chosen representative in each coarse fibre gives a genuinely
coarse-only kernel, with the derived oscillation error. -/
theorem smoothMixtureKernel_coarse_error {C D R : Type*} [Fintype C]
    (w : C → ℝ) (f : C → ℝ → ℝ) (location : D × R → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    {M mesh : ℝ} {L₀ : ℝ≥0} (hM : 0 ≤ M) (hmesh : 0 ≤ mesh)
    (hf : ∀ c x, |f c x| ≤ M) (hLip : ∀ c, LipschitzWith L₀ (f c))
    (hdiam : ∀ d r s, |location (d, r) - location (d, s)| ≤ mesh)
    (r₀ : R) (d e : D) (r s : R) :
    |smoothMixtureKernel w f location (d, r) (e, s) -
      smoothMixtureKernel w f location (d, r₀) (e, r₀)| ≤ 2 * M * (L₀ : ℝ) * mesh :=
  smoothMixtureKernel_oscillation w f location hw hw1 hM hmesh hf hLip
    (d, r) (d, r₀) (e, s) (e, r₀) (hdiam d r r₀) (hdiam e s r₀)

/-- The finite coarse-channel estimate. The channel kernel is actually
decomposed, and only its retained part is approximated by the displayed
smooth mixture. Centering is in the fine index inside each coarse cell. -/
theorem coarseChannel_square_bound {Ω C D R : Type*}
    [Fintype Ω] [Fintype C] [Fintype D] [Fintype R] [Nonempty R]
    (wΩ : Ω → ℝ) (p : Ω → D × R → ℝ) (w : C → ℝ)
    (f : C → ℝ → ℝ) (location : D × R → ℝ)
    (discarded retained : D × R → D × R → ℝ)
    (hwΩ : ∀ x, 0 ≤ wΩ x) (hw : ∀ c, 0 ≤ w c) (hw1 : ∑ c, w c = 1)
    {m B ε M mesh : ℝ} {L₀ : ℝ≥0}
    (hm : 0 < m) (hB : 0 ≤ B) (hε : 0 ≤ ε) (hM : 0 ≤ M) (hmesh : 0 ≤ mesh)
    (hf : ∀ c x, |f c x| ≤ M) (hLip : ∀ c, LipschitzWith L₀ (f c))
    (hdiam : ∀ d r s, |location (d, r) - location (d, s)| ≤ mesh)
    (hdiscarded : ∀ a b, 0 ≤ discarded a b)
    (hrows : ∀ a, (∑ b : D × R, m * discarded a b) ≤ B)
    (hdecomp : ∀ a b, finiteTwoSplitKernel wΩ (fun _ => m) p a b =
      discarded a b + retained a b)
    (happrox : ∀ a b, |retained a b - smoothMixtureKernel w f location a b| ≤ ε)
    (g : Ω → ℝ) :
    (∑ a : D × R, m *
      (finiteChannel wΩ (fun _ => m) p g a - finiteResidueAverage (fun r =>
        finiteChannel wΩ (fun _ => m) p g (a.1, r))) ^ 2) ≤
      (4 * B + 4 * (ε + 2 * M * (L₀ : ℝ) * mesh) * ∑ _a : D × R, m) *
        ∑ x, wΩ x * g x ^ 2 := by
  let r₀ : R := Classical.choice inferInstance
  let G : D → D → ℝ := fun d e => smoothMixtureKernel w f location (d, r₀) (e, r₀)
  have hflat (d e : D) (r s : R) : |retained (d, r) (e, s) - G d e| ≤
      ε + 2 * M * (L₀ : ℝ) * mesh := by
    have hosc := smoothMixtureKernel_coarse_error w f location hw hw1 hM hmesh hf hLip
      hdiam r₀ d e r s
    calc
      _ = |(retained (d, r) (e, s) - smoothMixtureKernel w f location (d, r) (e, s)) +
          (smoothMixtureKernel w f location (d, r) (e, s) - G d e)| := by congr 1; ring
      _ ≤ |retained (d, r) (e, s) - smoothMixtureKernel w f location (d, r) (e, s)| +
          |smoothMixtureKernel w f location (d, r) (e, s) - G d e| := abs_add_le _ _
      _ ≤ _ := add_le_add (happrox (d, r) (e, s)) hosc
  exact residueChannel_square_of_discarded wΩ (fun _ : D => m) p discarded retained G
    hwΩ (fun _ => hm) hdiscarded hdecomp hB
    (add_nonneg hε (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM)
      L₀.coe_nonneg) hmesh)) hrows hflat g

end JointDickman

end OAI

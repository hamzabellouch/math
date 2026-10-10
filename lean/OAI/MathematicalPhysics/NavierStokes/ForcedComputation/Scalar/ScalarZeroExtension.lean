import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.ScalarGlobalExistence

namespace OAI

/-! The detector starts after time two. Its scalar solution therefore admits
a smooth zero extension across the initial time. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set Filter
open scoped ContDiff Topology

def scalarZeroExtension (w : ℝ → Plane → ℝ) (t : ℝ) (x : Plane) : ℝ :=
  if 0 ≤ t then w t x else 0

theorem GlobalTorusScalarSolution.smoothAt_positive {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : GlobalTorusScalarSolution ν a h w w₀) {t : ℝ} (ht : 0 < t) (x : Plane) :
    ContDiffAt ℝ ∞ (Function.uncurry w) (t, x) := by
  have hT : 0 ≤ t + 1 := by linarith
  have hp : (t, x) ∈ Icc 0 (t + 1) ×ˢ (univ : Set Plane) :=
    ⟨⟨ht.le, by linarith⟩, mem_univ _⟩
  exact ((hw (t + 1) hT).smooth (t, x) hp).contDiffAt
    (prod_mem_nhds (Icc_mem_nhds ht (by linarith)) univ_mem)

theorem GlobalTorusScalarSolution.zero_before_one {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalTorusScalarSolution ν a h w (fun _ => 0)) (hν : 0 ≤ ν)
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, h t x = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, w t x = 0 := by
  have hb := (hw 1 (by norm_num)).absolute_bound (by norm_num) hν
    (M := 0) (A := 0) (fun t ht x => by simp only [hh t ht x, abs_zero, le_refl])
    (fun _ => by simp)
  intro t ht x
  have ha : |w t x| ≤ 0 := by simpa only [zero_mul, zero_add] using hb t ht x
  exact abs_eq_zero.mp (le_antisymm ha (abs_nonneg _))

theorem GlobalTorusScalarSolution.zeroExtension {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ} {w₀ : Plane → ℝ}
    (hw : GlobalTorusScalarSolution ν a h w w₀) :
    GlobalTorusScalarSolution ν a h (scalarZeroExtension w) w₀ := by
  intro T hT
  apply (hw T hT).congr hT
  intro t ht
  funext x
  dsimp only [scalarZeroExtension]
  split_ifs with h
  · rfl
  · exact (h ht.1).elim

theorem GlobalTorusScalarSolution.zeroExtension_smooth {ν : ℝ}
    {a : ℝ → Plane → Plane} {h w : ℝ → Plane → ℝ}
    (hw : GlobalTorusScalarSolution ν a h w (fun _ => 0)) (hν : 0 ≤ ν)
    (hh : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, h t x = 0) :
    ContDiff ℝ ∞ (Function.uncurry (scalarZeroExtension w)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y.1 < 1
  · have he : Function.uncurry (scalarZeroExtension w) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      have hn : ∀ᶠ z : ℝ × Plane in 𝓝 y, z.1 < 1 :=
        (continuous_fst.tendsto y).eventually (eventually_lt_nhds hy)
      filter_upwards [hn] with z hz
      change (if 0 ≤ z.1 then w z.1 z.2 else 0) = 0
      split_ifs with h₀
      · exact hw.zero_before_one hν hh z.1 ⟨h₀, hz.le⟩ z.2
      · rfl
    exact contDiff_const.contDiffAt.congr_of_eventuallyEq he
  · have ht : 0 < y.1 := by linarith
    have he : Function.uncurry (scalarZeroExtension w) =ᶠ[𝓝 y] Function.uncurry w := by
      have hn : ∀ᶠ z : ℝ × Plane in 𝓝 y, 0 < z.1 :=
        (continuous_fst.tendsto y).eventually (eventually_gt_nhds ht)
      filter_upwards [hn] with z hz
      change (if 0 ≤ z.1 then w z.1 z.2 else 0) = w z.1 z.2
      split_ifs with h
      · rfl
      · exact (h hz.le).elim
    exact (hw.smoothAt_positive ht y.2).congr_of_eventuallyEq he

end ForcedComputation.VelocityDetector

end

end OAI

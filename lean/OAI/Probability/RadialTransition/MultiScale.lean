import OAI.Probability.RadialTransition.Propagation

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma multiscale_pressure_balls {P Q : ℕ → Pressure} {a δ : ℕ → ℝ} {U C C₀ k l : ℝ}
    (ha : ∀ n, 0 < a n) (hδ : ∀ n, 0 ≤ δ n) (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hk : 0 < k) (hl : 0 < l)
    (hP : ∀ n, ConvexOn ℝ positiveParameters (onParameters (P n)))
    (hQ : ∀ n, ConvexOn ℝ positiveParameters (onParameters (Q n)))
    (hnext : ∀ n, P (n+1)=idealAttraction (Q n) (a n))
    (happ : ∀ n x, x ∈ phaseWindow (1/4) → |onParameters (Q n) x-onParameters (P n) x| ≤ δ n)
    (hlip : ∀ n x, x ∈ phaseWindow (1/4) → ∀ y ∈ phaseWindow (1/4),
      |onParameters (P n) x-onParameters (P n) y| ≤ C*dist x y)
    (hinc : ∀ n x, x ∈ phaseWindow (1/4) → |onParameters (P (n+1)) x-onParameters (Q n) x| ≤ C₀*a n)
    (hact : ∀ n β h, 0 < β → ∃ u, ActiveShift (Q n) (a n) β h u)
    (hcut : ∀ n x, x ∈ phaseWindow (1/2) → ∃ u ∈ Icc (0:ℝ) U, ActiveShift (Q n) (a n) (x 0) (x 1) u)
    (hinit : ∀ x ∈ phaseWindow (1/4), HasPhaseGroups (P 0) x (phaseRadius/2) ∧
      |onParameters (P 0) x-onParameters threePlane x| ≤ pressureRadius/64)
    (hdom : ∀ n, (5/4*U+k+l+1)*(∑ j ∈ Finset.range n, a j) ≤ 1/8)
    (hrad : ∀ n, ∑ j ∈ Finset.range n, (2*δ j/(l*a j)+a j*U^2/2) ≤ phaseRadius/2)
    (hband : ∀ n, 2*(k+2*δ n/(k*a n)+2*C*l/k+phaseRadius)<packingDensity)
    (hpress : ∀ n, ∑ j ∈ Finset.range n, (δ j+C₀*a j) ≤ pressureRadius/64) :
    ∀ n, ∃ x ∈ Metric.ball phaseCenter (1/8),
      Metric.closedBall targetSlope pressureRadius ⊆ supportSet (onParameters (P n)) positiveParameters x := by
  let S := 5/4*U+k+l+1
  let s := fun n => 1/4-S*(∑ j ∈ Finset.range n, a j)
  let r := fun n => phaseRadius/2+∑ j ∈ Finset.range n, (2*δ j/(l*a j)+a j*U^2/2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hs (n : ℕ) : 1/8 ≤ s n ∧ s n ≤ 1/4 := by
    have hn := hdom n
    have hm : 0 ≤ S*(∑ j ∈ Finset.range n, a j) :=
      mul_nonneg hS (Finset.sum_nonneg (fun j _ => (ha j).le))
    dsimp [s,S] at *
    constructor <;> linarith
  have hr (n : ℕ) : 0 ≤ r n ∧ r n ≤ phaseRadius := by
    have hnon : 0 ≤ ∑ j ∈ Finset.range n, (2*δ j/(l*a j)+a j*U^2/2) := by
      apply Finset.sum_nonneg
      intro j _
      have := ha j
      have := hδ j
      positivity
    have hb := hrad n
    dsimp [r]
    constructor <;> linarith [phaseRadius_pos]
  have hsr (n : ℕ) : s (n+1)=s n-S*a n := by
    dsimp [s]
    rw [Finset.sum_range_succ]
    ring
  have hrr (n : ℕ) : r (n+1)=r n+2*δ n/(l*a n)+a n*U^2/2 := by
    dsimp [r]
    rw [Finset.sum_range_succ]
    ring
  have hgroups : ∀ n x, x ∈ phaseWindow (s n) → HasPhaseGroups (P n) x (r n) := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simpa [r] using (hinit x (by simpa [s] using hx)).1
    | succ n ih =>
      intro x hx
      rw [hnext n,hrr n]
      rw [hsr] at hx
      exact propagate_phase_groups (hP n) (hQ n) (ha n) (hδ n) hC hU hk hl (hr n).1 (hs n).2
        (by have := hband n; linarith [(hr n).2]) ih (happ n) (hlip n) (hact n) (hcut n) x hx
  have hclose : ∀ n x, x ∈ phaseWindow (1/4) →
      |onParameters (P n) x-onParameters threePlane x| ≤
        pressureRadius/64+∑ j ∈ Finset.range n, (δ j+C₀*a j) := by
    intro n
    induction n with
    | zero =>
      intro x hx
      simpa using (hinit x hx).2
    | succ n ih =>
      intro x hx
      have h1 := abs_sub_le (onParameters (P (n+1)) x) (onParameters (Q n) x) (onParameters (P n) x)
      have h2 := abs_sub_le (onParameters (P (n+1)) x) (onParameters (P n) x) (onParameters threePlane x)
      rw [Finset.sum_range_succ]
      linarith [hinc n x hx,happ n x hx,ih x hx]
  intro n
  apply pressure_ball_exists (hP n)
  · intro x hx
    have hh := hclose n x (phaseWindow_mono (by norm_num) hx)
    linarith [hpress n]
  · intro x hx
    exact ⟨r n,(hr n).2,hgroups n x (phaseWindow_mono (hs n).1 hx)⟩

lemma pressure_ball_limit {P : ℕ → Pressure} {Q : Pressure} {C : ℝ}
    (hQ : ConvexOn ℝ positiveParameters (onParameters Q))
    (hball : ∀ n, ∃ x ∈ Metric.ball phaseCenter (1/8),
      Metric.closedBall targetSlope pressureRadius ⊆ supportSet (onParameters (P n)) positiveParameters x)
    (hlip : ∀ n x, x ∈ phaseWindow (1/4) → ∀ y ∈ phaseWindow (1/4),
      |onParameters (P n) x-onParameters (P n) y| ≤ C*dist x y)
    (hlim : ∀ x ∈ phaseWindow (1/4), Tendsto (fun n => onParameters (P n) x) atTop (nhds (onParameters Q x))) :
    ∃ x ∈ phaseWindow (1/8), Metric.closedBall targetSlope pressureRadius ⊆
      supportSet (onParameters Q) positiveParameters x := by
  choose x hx hs using hball
  have hx' (n : ℕ) : x n ∈ phaseWindow (1/8) := Metric.ball_subset_closedBall (hx n)
  obtain ⟨z,hz,σ,hσ,hlimx⟩ := (isCompact_closedBall phaseCenter (1/8)).tendsto_subseq hx'
  have hzq : z ∈ phaseWindow (1/4) := phaseWindow_mono (by norm_num) hz
  have hdist : Tendsto (fun n => dist (x (σ n)) z) atTop (nhds 0) := by
    simpa using hlimx.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (nhds z))
  have hdiff : Tendsto (fun n => onParameters (P (σ n)) (x (σ n))-onParameters (P (σ n)) z) atTop (nhds 0) := by
    apply squeeze_zero_norm
    · intro n
      simpa only [Real.norm_eq_abs] using hlip (σ n) (x (σ n))
        (phaseWindow_mono (by norm_num) (hx' (σ n))) z hzq
    · simpa using hdist.const_mul C
  have hbase : Tendsto (fun n => onParameters (P (σ n)) (x (σ n))) atTop (nhds (onParameters Q z)) := by
    have hh := hdiff.add ((hlim z hzq).comp hσ.tendsto_atTop)
    simpa only [Function.comp_apply,sub_add_cancel,zero_add] using hh
  refine ⟨z,hz,?_⟩
  intro v hv
  have hsupport : SupportsOn (onParameters Q) (phaseWindow (1/4)) z v := by
    apply supportsOn_of_tendsto hlimx tendsto_const_nhds hbase
      (fun y hy => (hlim y hy).comp hσ.tendsto_atTop)
    intro n y hy
    exact hs (σ n) hv y (phaseWindow_positive (by norm_num) hy)
  apply supportsOn_of_local hQ (phaseWindow_positive (by norm_num) hz) (by norm_num : (0:ℝ)<1/16)
  intro y hy
  exact hsupport y (phaseWindow_mono (by norm_num : (1/8:ℝ)+1/16≤1/4) (phaseWindow_near hz hy.2))

end RadialTransition
end

end OAI

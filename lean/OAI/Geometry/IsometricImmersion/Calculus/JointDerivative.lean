import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

def jointDifferential (fx fy : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight fx +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight fy

theorem jointDifferential_eq_coprod (fx fy : ℝ) :
    jointDifferential fx fy =
      (ContinuousLinearMap.toSpanSingleton ℝ fx).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ fy) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [jointDifferential]

theorem hasFDerivAt_of_continuous_partials
    {s : Set (ℝ × ℝ)} (hs : IsOpen s) {f fx fy : (ℝ × ℝ) → ℝ}
    (hcx : ContinuousOn fx s) (hcy : ContinuousOn fy s)
    (hdx : ∀ p ∈ s, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hdy : ∀ p ∈ s, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2)
    {p : ℝ × ℝ} (hp : p ∈ s) :
    HasFDerivAt f (jointDifferential (fx p) (fy p)) p := by
  have hspan : Continuous (ContinuousLinearMap.toSpanSingleton ℝ :
      ℝ → (ℝ →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous
  have hfirst : ∀ᶠ q in 𝓝 p,
      HasFDerivAt (fun x => f (x, q.2))
        (ContinuousLinearMap.toSpanSingleton ℝ (fx q)) q.1 := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact (hdx q hq).hasFDerivAt
  have hsecond : ∀ᶠ q in 𝓝 p,
      HasFDerivAt (fun y => f (q.1, y))
        (ContinuousLinearMap.toSpanSingleton ℝ (fy q)) q.2 := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact (hdy q hq).hasFDerivAt
  have hfull := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ)
    (f := fun x y => f (x, y))
    (f₁ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (fx (x, y)))
    (f₂ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (fy (x, y)))
    hfirst hsecond
    (hspan.continuousAt.comp (hcx.continuousAt (hs.mem_nhds hp)))
    (hspan.continuousAt.comp (hcy.continuousAt (hs.mem_nhds hp)))
  rw [jointDifferential_eq_coprod]
  exact hfull.hasFDerivAt

theorem joint_smooth_of_partial_derivative_sequence
    {s : Set (ℝ × ℝ)} (hs : IsOpen s)
    (H : ℕ → ℕ → (ℝ × ℝ) → ℝ)
    (hc : ∀ i j, ContinuousOn (H i j) s)
    (hdx : ∀ i j p, p ∈ s →
      HasDerivAt (fun x => H i j (x, p.2)) (H (i + 1) j p) p.1)
    (hdy : ∀ i j p, p ∈ s →
      HasDerivAt (fun y => H i j (p.1, y)) (H i (j + 1) p) p.2) :
    ∀ i j, ContDiffOn ℝ ∞ (H i j) s := by
  have hd (i j : ℕ) (p : ℝ × ℝ) (hp : p ∈ s) :
      HasFDerivAt (H i j)
        (jointDifferential (H (i + 1) j p) (H i (j + 1) p)) p :=
    hasFDerivAt_of_continuous_partials hs (hc (i + 1) j) (hc i (j + 1))
      (hdx i j) (hdy i j) hp
  have hnat : ∀ n : ℕ, ∀ i j, ContDiffOn ℝ n (H i j) s := by
    intro n
    induction n with
    | zero =>
        intro i j
        simpa only [Nat.cast_zero, contDiffOn_zero] using hc i j
    | succ n hn =>
        intro i j
        have hnext : ContDiffOn ℝ ((n : ℕ∞ω) + 1) (H i j) s := by
          rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
          refine ⟨fun p hp => (hd i j p hp).differentiableAt.differentiableWithinAt,
            by simp, ?_⟩
          have hfield : ContDiffOn ℝ n
              (fun p => jointDifferential (H (i + 1) j p) (H i (j + 1) p)) s :=
            (contDiffOn_const.smulRight (hn (i + 1) j)).add
              (contDiffOn_const.smulRight (hn i (j + 1)))
          exact hfield.congr (fun p hp => (hd i j p hp).fderiv)
        simpa only [Nat.cast_add, Nat.cast_one] using hnext
  intro i j
  exact contDiffOn_infty.mpr (fun n => hnat n i j)

end SmoothLocal.ODE

end

end OAI

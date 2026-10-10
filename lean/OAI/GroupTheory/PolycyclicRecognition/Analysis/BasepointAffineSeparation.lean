import OAI.GroupTheory.PolycyclicRecognition.Analysis.ExactProfileTransport
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearProfilesOnBall

namespace OAI

/-! # Finite-label separation and center errors after changing basepoint -/

noncomputable section
namespace PolycyclicRecognition

open Filter Metric
open scoped Topology

/-- Comparing transported affine profiles identifies their finite linear
labels and measures the exact remaining center error. -/
theorem affine_labels_offsets_of_chart_transport
    {V W L : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype L] [Nonempty L]
    (q : V →L[ℝ] W) (hq : Function.Surjective q)
    (A : L → W →L[ℝ] W) (hA : Function.Injective A)
    {R S : ℝ} (hR : 0 < R) (_hS : 0 < S)
    (a a' : ℕ → L) (b b' c : ℕ → W) (v : ℕ → W) (t : ℕ → ℝ)
    (ψ : ℕ → C(closedBall (0 : V) R, closedBall (0 : V) S))
    (hheight : ∀ᶠ n in atTop, ∀ z, t n • q (ψ n z) = q z - v n)
    (hd : Tendsto (fun n => dist
      (linearBallProfile q (A (a n)) R + ContinuousMap.const _ (b n))
      (transportCompactProfile (t n) (ψ n) (c n)
        (linearBallProfile q (A (a' n)) S + ContinuousMap.const _ (b' n))))
      atTop (𝓝 0)) :
    (∀ᶠ n in atTop, a n = a' n) ∧
      Tendsto (fun n => dist (b n) (t n • b' n + c n - A (a' n) (v n))) atTop (𝓝 0) := by
  let P := fun l => linearBallProfile q (A l) R
  have hP : Function.Injective P := (linearBallProfile_injective q hq hR).comp hA
  let z₀ : closedBall (0 : V) R := ⟨0, by simpa using hR.le⟩
  have hzero : ∀ l, P l z₀ = 0 := by intro l; change A l (q 0) = 0; simp
  have he n (hn : ∀ z, t n • q (ψ n z) = q z - v n) :
      transportCompactProfile (t n) (ψ n) (c n)
      (linearBallProfile q (A (a' n)) S + ContinuousMap.const _ (b' n)) =
      P (a' n) + ContinuousMap.const _ (t n • b' n + c n - A (a' n) (v n)) := by
    ext z
    change t n • (A (a' n) (q (ψ n z)) + b' n) + c n =
      A (a' n) (q z) + (t n • b' n + c n - A (a' n) (v n))
    rw [smul_add, ← map_smul, hn, map_sub]
    abel
  have hd' : Tendsto (fun n => dist (P (a n) + ContinuousMap.const _ (b n))
      (P (a' n) + ContinuousMap.const _ (t n • b' n + c n - A (a' n) (v n))))
      atTop (𝓝 0) := by
    apply hd.congr'
    filter_upwards [hheight] with n hn
    rw [he n hn]
  exact affine_labels_and_offsets_of_distance_tendsto_zero P hP z₀ hzero a a' b _ hd'

/-- Vanishing mean offsets remove the affine constants from the comparison,
leaving precisely the normalized error in the two center heights. -/
theorem center_error_tendsto_zero_of_offsets
    {W L : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A : L → W →L[ℝ] W) (a : ℕ → L) (b b' c v : ℕ → W) (t : ℝ)
    (hb : Tendsto b atTop (𝓝 0)) (hb' : Tendsto b' atTop (𝓝 0))
    (hoff : Tendsto (fun n => dist (b n) (t • b' n + c n - A (a n) (v n)))
      atTop (𝓝 0)) :
    Tendsto (fun n => c n - A (a n) (v n)) atTop (𝓝 0) := by
  let e := fun n => t • b' n + c n - A (a n) (v n)
  have hdiff : Tendsto (fun n => b n - e n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [dist_eq_norm] using hoff)
  have ht : Tendsto (fun n => t • b' n) atTop (𝓝 0) := by
    simpa only [smul_zero] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).smul hb')
  have hh := (hb.sub hdiff).sub ht
  have hh' : Tendsto (fun n => c n - A (a n) (v n)) atTop (𝓝 (0 - 0 - 0)) :=
    hh.congr' (Eventually.of_forall (fun n => by dsimp only [e]; abel))
  simpa only [sub_zero] using hh'

end PolycyclicRecognition

end

end OAI

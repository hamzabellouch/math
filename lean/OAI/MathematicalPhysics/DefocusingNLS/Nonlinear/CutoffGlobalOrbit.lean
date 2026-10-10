import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingSlabTrajectory
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffPathContinuity

namespace OAI

/-! # A global cutoff orbit from compatible nonlinear steps

The profile is the actual sampled cutoff of the smooth stationary function.
Compatible step solutions with geometric perturbation bounds give a global
nonlinear trajectory, with vanishing error relative to that same profile.
The stable graph supplies these endpoint data in the subsequent application.
-/

open Set Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def sampledCutoffProfileAtRadius (a k : ℝ) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (R : {R : ℝ // 1 ≤ R}) : FourierL2 :=
  schwartzTorusSample a k R.1 ha1 hk R.2
    (radianFourierKernel (cutoffProfileSchwartz R.1
      (lt_of_lt_of_le zero_lt_one R.2) χ hχ Q hQ))

noncomputable def sampledCutoffProfileOrbit (a k L : ℝ)
    (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (s : ℝ) : FourierL2 :=
  sampledCutoffProfileAtRadius a k ha1 hk χ hχ Q hQ
    ⟨expandingRadius L (max 0 s),
      hL.trans (expandingRadius_ge L _ hL (le_max_left _ _))⟩

theorem continuous_sampledCutoffProfileOrbit (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (sampledCutoffProfileOrbit a k L ha1 hk hL χ hχ Q hQ) := by
  have hR : Continuous (fun s : ℝ =>
      (⟨expandingRadius L (max 0 s),
        hL.trans (expandingRadius_ge L _ hL (le_max_left _ _))⟩ : {R : ℝ // 1 ≤ R})) := by
    apply Continuous.subtype_mk
    unfold expandingRadius
    fun_prop
  exact (continuous_cutoffProfile_sample a k ha ha1 hk χ hχ Q hQ).comp hR

theorem sampledCutoffProfileOrbit_at (a k L M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hM : 0 < M)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (n : ℕ) (s : Icc (0 : ℝ) M) :
    sampledCutoffProfileOrbit a k L ha1 hk hL χ hχ Q hQ ((n : ℝ) * M + s) =
      sampledCutoffProfilePath a k (expandingRadius L ((n : ℝ) * M)) M ha ha1 hk
        (hL.trans (expandingRadius_ge L _ hL (by positivity))) χ hχ Q hQ s := by
  have hpos : 0 ≤ (n : ℝ) * M + s := add_nonneg (by positivity) s.2.1
  unfold sampledCutoffProfileOrbit
  simp only [max_eq_right hpos]
  change sampledCutoffProfileAtRadius a k ha1 hk χ hχ Q hQ _ =
    sampledCutoffProfileAtRadius a k ha1 hk χ hχ Q hQ _
  congr 1
  apply Subtype.ext
  exact (expandingRadius_add L ((n : ℝ) * M) s).symm

theorem exists_cutoffGlobal_orbit_of_steps (a b k L M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hM : 0 < M) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (x : ℕ → FourierL2) (V : ℕ → C(Icc (0 : ℝ) M, FourierL2))
    (hVM : ∀ n, V n ⟨M, hM.le, le_rfl⟩ = x (n + 1))
    (hsol : ∀ n : ℕ,
      let Ln := expandingRadius L ((n : ℝ) * M)
      let hLn := hL.trans (expandingRadius_ge L ((n : ℝ) * M) hL (by positivity))
      let q := sampledCutoffProfilePath a k Ln M ha ha1 hk hLn χ hχ Q hQ
      q + V n = expandingPicard a b k Ln M ha hk hLn hM.le
        (expandingNonlinearReaction a k Ln M ha ha1 hk hLn m)
        (q ⟨0, le_rfl, hM.le⟩ + x n) (q + V n))
    (C r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (hVbound : ∀ n, ‖V n‖ ≤ C * r ^ n) :
    ∃ u : ℝ → FourierL2, ∃ hu : ContinuousOn u (Ici 0),
      u 0 = sampledCutoffProfileOrbit a k L ha1 hk hL χ hχ Q hQ 0 + x 0 ∧
      (∀ (S : ℝ) (hS : 0 < S), expandingSlabRestriction u hu S =
        expandingPicard a b k L S ha hk hL hS.le
          (expandingNonlinearReaction a k L S ha ha1 hk hL m) (u 0)
          (expandingSlabRestriction u hu S)) ∧
      Tendsto (fun s => ‖u s - sampledCutoffProfileOrbit a k L ha1 hk hL χ hχ Q hQ s‖)
        atTop (𝓝 0) := by
  let q : ℕ → C(Icc (0 : ℝ) M, FourierL2) := fun n =>
    sampledCutoffProfilePath a k (expandingRadius L ((n : ℝ) * M)) M ha ha1 hk
      (hL.trans (expandingRadius_ge L _ hL (by positivity))) χ hχ Q hQ
  let W := fun n => q n + V n
  let qglob := sampledCutoffProfileOrbit a k L ha1 hk hL χ hχ Q hQ
  have hV0 (n : ℕ) : V n ⟨0, le_rfl, hM.le⟩ = x n := by
    have hz := congrArg (fun f : C(Icc (0 : ℝ) M, FourierL2) => f ⟨0, le_rfl, hM.le⟩)
      (hsol n)
    simp only [ContinuousMap.add_apply, expandingPicard_initial] at hz
    exact add_left_cancel hz
  have hq (n : ℕ) (s : Icc (0 : ℝ) M) :
      qglob ((n : ℝ) * M + s) = q n s :=
    sampledCutoffProfileOrbit_at a k L M ha ha1 hk hL hM χ hχ Q hQ n s
  have hqjoin (n : ℕ) : q n ⟨M, hM.le, le_rfl⟩ = q (n + 1) ⟨0, le_rfl, hM.le⟩ := by
    rw [← hq n, ← hq (n + 1)]
    congr 1
    push_cast
    ring
  have hjoinV (n : ℕ) : V n ⟨M, hM.le, le_rfl⟩ = V (n + 1) ⟨0, le_rfl, hM.le⟩ :=
    (hVM n).trans (hV0 (n + 1)).symm
  have hjoinW (n : ℕ) : W n ⟨M, hM.le, le_rfl⟩ = W (n + 1) ⟨0, le_rfl, hM.le⟩ := by
    change q n _ + V n _ = q (n + 1) _ + V (n + 1) _
    rw [hqjoin n, hjoinV n]
  let u := gluedSlabPath M hM W hjoinW
  let v := gluedSlabPath M hM V hjoinV
  have hu : ContinuousOn u (Ici 0) := continuousOn_gluedSlabPath M hM W hjoinW
  have hWsol (n : ℕ) :
      W n = expandingPicard a b k (expandingRadius L ((n : ℝ) * M)) M ha hk
        (hL.trans (expandingRadius_ge L _ hL (by positivity))) hM.le
        (expandingNonlinearReaction a k (expandingRadius L ((n : ℝ) * M)) M ha ha1 hk
          (hL.trans (expandingRadius_ge L _ hL (by positivity))) m)
        (W n ⟨0, le_rfl, hM.le⟩) (W n) := by
    simpa only [W, ContinuousMap.add_apply, hV0] using hsol n
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · have hu0 := gluedSlabPath_at M hM W hjoinW 0 ⟨0, le_rfl, hM.le⟩
    have hq0 := hq 0 ⟨0, le_rfl, hM.le⟩
    simp only [Nat.cast_zero, zero_mul, add_zero] at hu0 hq0
    change u 0 = W 0 ⟨0, le_rfl, hM.le⟩ at hu0
    change u 0 = qglob 0 + x 0
    rw [hu0]
    change q 0 _ + V 0 _ = _
    rw [hV0, hq0]
  · intro S hS
    exact expandingGluedSlabs_picard a b k L M ha ha1 hk hL hM m W hjoinW hWsol S hS
  · have hv : Tendsto v atTop (𝓝 0) := gluedSlabPath_tendsto_zero M hM V hjoinV C r hr hr1
      (fun n s => (ContinuousMap.norm_coe_le_norm (V n) s).trans (hVbound n))
    have heq : (fun s => u s - qglob s) =ᶠ[atTop] v := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      let n := ⌊t / M⌋₊
      let s : Icc (0 : ℝ) M := ⟨t - (n : ℝ) * M, by
        have hh := equalSlabInterval_floor M hM t ht
        constructor <;> dsimp [n] <;> linarith [hh.1, hh.2]⟩
      have he : (n : ℝ) * M + s = t := by dsimp [s]; ring
      have hut := gluedSlabPath_at M hM W hjoinW n s
      have hvt := gluedSlabPath_at M hM V hjoinV n s
      have hqt := hq n s
      rw [he] at hut hvt hqt
      change u t = W n s at hut
      change v t = V n s at hvt
      change u t - qglob t = v t
      rw [hut, hvt, hqt]
      change q n s + V n s - q n s = V n s
      abel
    simpa using (hv.congr' heq.symm).norm

end DefocusingNLS

end OAI

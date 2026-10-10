import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingBlowupTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingInitialData

namespace OAI

/-! # A global similarity solution identifies the actual maximal physical flow

A path satisfying the nonlinear mild equation on every finite similarity
slab determines the maximal Sobolev flow, including its point observation
and endpoint.
-/

open Set Filter Topology

namespace DefocusingNLS

noncomputable def expandingSlabRestriction (u : ℝ → FourierL2)
    (hu : ContinuousOn u (Ici 0)) (S : ℝ) : C(Icc (0 : ℝ) S, FourierL2) :=
  ⟨fun s => u s, (hu.mono (fun _ hs => hs.1)).domRestrict⟩

theorem exists_expanding_physical_slab (L t : ℝ) (hL : 0 < L)
    (ht : t ∈ Ico 0 (L ^ (-2 : ℝ))) :
    ∃ S : ℝ, 0 < S ∧ t ∈ Ico 0 (expandingFreeTime L S) := by
  let s := expandingInverseClock L t
  have hs : 0 ≤ s := expandingInverseClock_nonneg L t hL ht
  refine ⟨s + 1, by linarith, ht.1, ?_⟩
  have he : expandingFreeTime L s = t :=
    expandingFreeTime_inverseClock L t hL
      (expanding_clock_denominator_pos_of_lt L t hL ht.2)
  rw [← he]
  exact strictMono_expandingFreeTime L hL (by linarith)

section Global

variable (a b k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
  (m : ℕ) (ham : 2 * a * m = 1)
  (u : ℝ → FourierL2) (hu : ContinuousOn u (Ici 0))
  (hsol : ∀ (S : ℝ) (hS : 0 < S),
    expandingSlabRestriction u hu S =
      expandingPicard a b k L S ha hk hL hS.le
        (expandingNonlinearReaction a k L S ha ha1 hk hL m) (u 0)
        (expandingSlabRestriction u hu S))

local notation "f₀" => expandingPhysicalInitialEquiv a k L ha ha1 hk hL (u 0)

include b ham hu hsol

theorem expandingGlobal_mem_maximal (t : ℝ) (ht : t ∈ Ico 0 (L ^ (-2 : ℝ))) :
    t ∈ maximalSobolevInteractionDomain k (by linarith) m f₀ := by
  obtain ⟨S, hS, htS⟩ := exists_expanding_physical_slab L t (by linarith) ht
  let v := expandingSlabRestriction u hu S
  have h := expandingSchrodingerTrajectory_eq_maximal a b k L S ha ha1 hk hL hS
    m ham v (u 0) (hsol S hS)
  dsimp only at h
  have hinit : expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS.le v 0 = f₀ := by
    rw [expandingSchrodingerTrajectory_initial_equiv]
    rfl
  rw [hinit] at h
  exact h.1 htS

theorem expandingGlobal_maximal_observation (t : ℝ)
    (ht : t ∈ Ico 0 (L ^ (-2 : ℝ))) (x : SchrodingerTorus) :
    sobolevTorusFunction k (maximalSobolevSchrodingerFlow k (by linarith) m f₀ t) x =
      expandingPhysicalAmplitude a b L (expandingInverseClock L t) *
        expandingTorusFunction a k (expandingRadius L (expandingInverseClock L t))
          (u (expandingInverseClock L t)) x := by
  obtain ⟨S, hS, htS⟩ := exists_expanding_physical_slab L t (by linarith) ht
  let v := expandingSlabRestriction u hu S
  have h := expandingSchrodingerTrajectory_eq_maximal a b k L S ha ha1 hk hL hS
    m ham v (u 0) (hsol S hS)
  dsimp only at h
  have hinit : expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS.le v 0 = f₀ := by
    rw [expandingSchrodingerTrajectory_initial_equiv]
    rfl
  rw [hinit] at h
  rw [← h.2 htS]
  exact expandingSchrodingerTrajectory_observation a b k L S ha ha1 hk hL hS.le v t
    ⟨htS.1, htS.2.le⟩ x

/-- A stable similarity orbit transfers to a physical solution with finite-time
blowup and its prescribed limiting point observation. -/
theorem expandingGlobal_rescaled_limit
    (q : ℝ → FourierL2) (x : SchrodingerTorus) (c : ℂ)
    (hq : ∀ s, 0 ≤ s → expandingTorusFunction a k (expandingRadius L s) (q s) x = c)
    (hdecay : Tendsto (fun s => ‖u s - q s‖) atTop (𝓝 0)) :
    Tendsto (fun t => (L ^ (-2 : ℝ) - t) ^ a *
      ‖sobolevTorusFunction k (maximalSobolevSchrodingerFlow k (by linarith) m f₀ t) x‖)
      (𝓝[<] (L ^ (-2 : ℝ))) (𝓝 ‖c‖) := by
  have h := expanding_profile_rescaled_limit a b k L ha ha1 hk hL u q x c hq hdecay
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT (Real.rpow_pos_of_pos (by linarith : 0 < L)
    (-2 : ℝ))] with t ht
  rw [expandingGlobal_maximal_observation a b k L ha ha1 hk hL m ham u hu hsol t
    ⟨ht.1.le, ht.2⟩ x]

theorem expandingGlobal_lifespan
    (q : ℝ → FourierL2) (x : SchrodingerTorus) (c : ℂ) (hc : c ≠ 0)
    (hq : ∀ s, 0 ≤ s → expandingTorusFunction a k (expandingRadius L s) (q s) x = c)
    (hdecay : Tendsto (fun s => ‖u s - q s‖) atTop (𝓝 0)) :
    BddAbove (maximalSobolevInteractionDomain k (by linarith) m f₀) ∧
      sSup (maximalSobolevInteractionDomain k (by linarith) m f₀) = L ^ (-2 : ℝ) := by
  apply maximalSobolev_lifespan_of_forward_rescaled_observation k (by linarith) m f₀
    (L ^ (-2 : ℝ)) a ‖c‖ (Real.rpow_pos_of_pos (by linarith) _) ha (norm_pos_iff.mpr hc)
    (fun t ht => expandingGlobal_mem_maximal a b k L ha ha1 hk hL m ham u hu hsol t ht)
    (sobolevPointEvaluation k (by linarith) x) (sobolevPointEvaluation k (by linarith) x).continuous
  simpa only [sobolevTorusFunction_apply k (by linarith)] using
    expandingGlobal_rescaled_limit a b k L ha ha1 hk hL m ham u hu hsol q x c hq hdecay

end Global

end DefocusingNLS

end OAI

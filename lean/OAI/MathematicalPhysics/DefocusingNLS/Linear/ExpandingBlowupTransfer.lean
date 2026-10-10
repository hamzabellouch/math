import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingBlowupClock

namespace OAI

/-! # From a decaying similarity perturbation to a finite maximal endpoint

A decaying similarity perturbation gives an unbounded physical point
observation as the physical time approaches its finite endpoint.
-/

open Filter Topology Set

namespace DefocusingNLS

theorem expandingSchrodingerTrajectory_observation (a b k L S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hS : 0 ≤ S)
    (u : C(Icc (0 : ℝ) S, FourierL2)) (t : ℝ)
    (ht : t ∈ Icc 0 (expandingFreeTime L S)) (x : SchrodingerTorus) :
    sobolevTorusFunction k (expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS u t) x =
      expandingPhysicalAmplitude a b L (expandingInverseClock L t) *
        expandingTorusFunction a k (expandingRadius L (expandingInverseClock L t))
          (u ⟨expandingInverseClock L t,
            expandingInverseClock_mem_Icc L S t (by linarith) ht⟩) x := by
  let s := expandingInverseClock L t
  have hs : s ∈ Icc 0 S := expandingInverseClock_mem_Icc L S t (by linarith) ht
  have hR : 1 ≤ expandingRadius L s := hL.trans (expandingRadius_ge L s hL hs.1)
  change sobolevTorusFunction k
    (expandingPhysicalAmplitude a b L s • expandingToSobolev a k ha1 hk
      (expandingPhysicalPath a k L S ha hk hL u (projIcc 0 S hS s))) x = _
  rw [projIcc_of_mem _ hs]
  calc
    _ = expandingPhysicalAmplitude a b L s * sobolevTorusFunction k
        (expandingToSobolev a k ha1 hk
          (expandingPhysicalPath a k L S ha hk hL u ⟨s, hs⟩)) x := by
      simp only [sobolevTorusFunction_apply k (by linarith), map_smul, smul_eq_mul]
    _ = _ := by
      congr 1
      change sobolevTorusFunction k (expandingToSobolev a k ha1 hk
        (expandingInverseTransfer a k (expandingRadius L s) ha hk hR (u ⟨s, hs⟩))) x = _
      exact expandingSobolev_observation a k (expandingRadius L s) ha ha1 hk hR _ x

theorem expanding_profile_rescaled_limit (a b k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (u q : ℝ → FourierL2) (x : SchrodingerTorus) (c : ℂ)
    (hq : ∀ s, 0 ≤ s → expandingTorusFunction a k (expandingRadius L s) (q s) x = c)
    (hdecay : Tendsto (fun s => ‖u s - q s‖) atTop (𝓝 0)) :
    Tendsto (fun t => (L ^ (-2 : ℝ) - t) ^ a *
      ‖expandingPhysicalAmplitude a b L (expandingInverseClock L t) *
        expandingTorusFunction a k (expandingRadius L (expandingInverseClock L t))
          (u (expandingInverseClock L t)) x‖)
      (𝓝[<] (L ^ (-2 : ℝ))) (𝓝 ‖c‖) := by
  let g : ℝ → ℂ := fun s =>
    expandingTorusFunction a k (expandingRadius L s) (u s) x
  have hg : Tendsto g atTop (𝓝 c) :=
    expanding_observation_tendsto_of_norm_decay a k L ha ha1 hk hL u q x c hq hdecay
  exact expanding_rescaled_observation_limit a b L (by linarith) g c hg

/-- The forward maximal-flow formulation only needs existence on `[0,T)`.
Continuity of the observation excludes the endpoint itself. -/
theorem maximalSobolev_lifespan_of_forward_rescaled_observation
    {F : Type*} [NormedAddCommGroup F]
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2)
    (T β c : ℝ) (hT : 0 < T) (hβ : 0 < β) (hc : 0 < c)
    (hsub : Ico 0 T ⊆ maximalSobolevInteractionDomain k hk m f₀)
    (observe : FourierL2 → F) (hobs : Continuous observe)
    (hblowup : Tendsto (fun t => (T - t) ^ β *
      ‖observe (maximalSobolevSchrodingerFlow k hk m f₀ t)‖) (𝓝[<] T) (𝓝 c)) :
    BddAbove (maximalSobolevInteractionDomain k hk m f₀) ∧
      sSup (maximalSobolevInteractionDomain k hk m f₀) = T := by
  have hnot : T ∉ maximalSobolevInteractionDomain k hk m f₀ := by
    intro hmem
    have hcont := (continuousOn_maximalSobolevSchrodingerFlow k hk m f₀ T hmem).continuousAt
      ((isOpen_maximalSobolevInteractionDomain k hk m f₀).mem_nhds hmem)
    have hlim := hobs.continuousAt.tendsto.comp
      (hcont.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[<] T ≤ 𝓝 T))
    exact no_left_limit_of_positive_rescaled_norm
      (fun t => observe (maximalSobolevSchrodingerFlow k hk m f₀ t)) T β c hβ hc hblowup ⟨_, hlim⟩
  have hbound : ∀ t ∈ maximalSobolevInteractionDomain k hk m f₀, t ≤ T := by
    intro t ht
    by_contra hn
    apply hnot
    exact (isPreconnected_maximalSobolevInteractionDomain k hk m f₀).Icc_subset
      (zero_mem_maximalSobolevInteractionDomain k hk m f₀) ht ⟨hT.le, (lt_of_not_ge hn).le⟩
  refine ⟨⟨T, hbound⟩, ?_⟩
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    ⟨0, zero_mem_maximalSobolevInteractionDomain k hk m f₀⟩ hbound
  intro r hr
  let s := (max 0 r + T) / 2
  have hs : s ∈ Ico 0 T := by
    have hm := le_max_left (0 : ℝ) r
    have hM := max_lt hT hr
    dsimp [s]
    constructor <;> linarith
  refine ⟨s, hsub hs, ?_⟩
  have hm := le_max_right (0 : ℝ) r
  dsimp [s]
  linarith [max_lt hT hr]

end DefocusingNLS

end OAI

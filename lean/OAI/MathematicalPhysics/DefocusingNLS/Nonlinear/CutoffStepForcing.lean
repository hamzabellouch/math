import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPerturbationEquation
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffMildEquation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzProfileSampling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! # The actual sampled cutoff supplies the nonlinear step data

The profile is a forced nonlinear mild solution.  Its forcing is exactly
minus `i` times the sampled cutoff residual, with the required uniform
`L^(-2-a)` bound.
-/

open Set Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem exists_cutoffResidual_small_scale (a C δ : ℝ) (ha : 0 < a) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → C * L ^ (-2 - a) ≤ δ := by
  have ht : Tendsto (fun L : ℝ => C * L ^ (-2 - a)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 2 + a by linarith)).const_mul C
    simpa only [show -(2 + a) = -2 - a by ring, mul_zero] using h
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨max 1 L₀, le_max_left _ _, ?_⟩
  intro L hL
  exact (hL₀ L ((le_max_right _ _).trans hL)).le

noncomputable def sampledCutoffDefectPath (a k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : C(Icc (0 : ℝ) T, FourierL2) :=
  (-Complex.I) • sampledCutoffResidualPath a k L T ha ha1 hk hL χ hχ hχone hχzero m Q hQ

theorem sampledCutoffProfile_forced_mild (a b k L T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (m : ℕ) (ham : 2 * a * (m : ℝ) = 1)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hstationary : ∀ y, stationarySimilarityDefect a b m Q y = 0) :
    let q := sampledCutoffProfilePath a k L T ha ha1 hk hL
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ
    let g := sampledCutoffDefectPath a k L T ha ha1 hk hL χ hχ hχone hχzero m Q hQ
    ∀ t : Icc (0 : ℝ) T, q t =
      expandingFreeStep a b k L t ha hk hL t.2.1 (q ⟨0, le_rfl, hT⟩) +
        expandingDuhamel a b k L ha hk hL t (fun τ =>
          expandingReactionHistory T hT (expandingNonlinearReaction a k L T ha ha1 hk hL m) q τ +
            g (projIcc 0 T hT τ)) := by
  intro q g t
  have h := sampledCutoffProfile_mild a b k L T ha ha1 hk hL hT m ham
    χ hχ hχone hχzero Q hQ hstationary t t.2
  have hf : sampledCutoffForcingHistory a k L T ha ha1 hk hL hT
      χ hχ hχone hχzero m Q hQ = fun τ =>
      expandingReactionHistory T hT (expandingNonlinearReaction a k L T ha ha1 hk hL m) q τ +
        g (projIcc 0 T hT τ) := rfl
  rw [hf] at h
  simpa only [sampledCutoffProfileHistory, projIcc_of_mem hT t.2,
    projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩)] using h

theorem exists_cutoffStep_profile_forcing_bounds (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχsupport : ∀ x : E, 1 ≤ ‖x‖ → χ x = 0) :
    let hχzero := fun x : E => fun hx : 2 < ‖x‖ => hχsupport x (by linarith)
    ∃ N : ℕ, ∀ (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (D : ℝ), 0 ≤ D →
      (∀ n ≤ N, ∀ y : E, y ≠ 0 →
        ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) →
      ∃ R C : ℝ, 0 ≤ R ∧ 0 ≤ C ∧ ∀ (L T : ℝ) (hL : 1 ≤ L) (t : Icc (0 : ℝ) T),
        ‖sampledCutoffProfilePath a k L T ha ha1 hk hL
          (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Q hQ t‖ ≤ R ∧
        ‖sampledCutoffDefectPath a k L T ha ha1 hk hL χ hχ hχone hχzero m Q hQ t‖ ≤
          C * L ^ (-2 - a) := by
  intro hχzero
  have hχc : ∀ x : E, 1 ≤ ‖x‖ → (χ.postcompCLM Complex.ofRealCLM) x = 0 := by
    intro x hx
    simp [hχsupport x hx]
  obtain ⟨N₁, hN₁⟩ := exists_cutoffProfile_sampling_bound a k ha ha1 hk
    (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) hχc
  obtain ⟨N₂, hN₂⟩ := exists_sampledCutoffResidualPath_bound a k ha ha1 hk χ hχ hχone hχzero m
  refine ⟨max N₁ N₂, ?_⟩
  intro Q hQ D hD hsymbol
  obtain ⟨R, hR, hprofile⟩ := hN₁ Q hQ D hD
    (fun n hn => hsymbol n (hn.trans (le_max_left _ _)))
  obtain ⟨C, hC, hresidual⟩ := hN₂ Q hQ D hD
    (fun n hn => hsymbol n (hn.trans (le_max_right _ _)))
  refine ⟨R, C, hR, hC, ?_⟩
  intro L T hL t
  constructor
  · exact hprofile (expandingRadius L t) (hL.trans (expandingRadius_ge L t hL t.2.1))
  · change ‖(-Complex.I) • sampledCutoffResidualPath a k L T ha ha1 hk hL
      χ hχ hχone hχzero m Q hQ t‖ ≤ _
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    apply (hresidual L T hL t).trans
    apply mul_le_of_le_one_right (mul_nonneg hC (Real.rpow_nonneg (by linarith) _))
    exact Real.exp_le_one_iff.mpr (by nlinarith [t.2.1])

end DefocusingNLS

end OAI

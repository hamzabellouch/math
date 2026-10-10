import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStableSequence
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStepLinearization
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphStepDecay

namespace OAI

/-! # Actual global nonlinear orbits selected by the stable graph -/

open Set Filter Topology
open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

def HasCutoffStableOrbits {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
    ∃ ζ : F →L[ℝ] FourierL2, ∃ π : FourierL2 →L[ℝ] F,
      (∀ v, π (ζ v) = v) ∧ ∀ w₀ : FourierL2, ‖w₀‖ ≤ ρ / 4 → π w₀ = 0 →
        ∃ u : ℝ → FourierL2, ∃ hu : ContinuousOn u (Ici 0),
          stableFrameProjection ζ π
            (u 0 - sampledCutoffProfileOrbit a k L.1 ha1 hk L.2 χ hχ Qp hQp 0) = w₀ ∧
          (∀ (S : ℝ) (hS : 0 < S), expandingSlabRestriction u hu S =
            expandingPicard a b k L.1 S ha hk L.2 hS.le
              (expandingNonlinearReaction a k L.1 S ha ha1 hk L.2 m) (u 0)
              (expandingSlabRestriction u hu S)) ∧
          Tendsto (fun s => ‖u s - sampledCutoffProfileOrbit a k L.1 ha1 hk L.2 χ hχ Qp hQp s‖)
            atTop (𝓝 0)

theorem exists_cutoffStable_orbits {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (T : ℝ≥0) (hT : 0 < (T : ℝ))
    (hratio : 2 * Real.exp (-(2 + a) * T / 2) ≤ 1)
    (hlinear : HasTorusLinearStep (F := F) T
      (cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T))
    (hnonlinear : HasCutoffNonlinearSteps a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T) :
    HasCutoffStableOrbits (F := F) a b k ha ha1 hk m χ hχ Qp hQp := by
  classical
  obtain ⟨δ, Lnl, B, hδ, _, hB, hstep⟩ := hnonlinear
  obtain ⟨ρ, hρ, hρδ, Lg, hgraph⟩ := exists_cutoffStable_sequence_threshold a δ B ha hδ hB.le
    T hratio _ hlinear
  refine ⟨ρ, hρ, max Lg Lnl, ?_⟩
  intro L hL
  have hLg : Lg ≤ L.1 := (le_max_left _ _).trans hL
  have hLnl : Lnl ≤ L.1 := (le_max_right _ _).trans hL
  let Ln := expandingDiscreteRadius L T
  have hLn (n : ℕ) : Lnl ≤ (Ln n).1 := hLnl.trans (expandingDiscreteRadius_ge L T n)
  choose V h hsol hV hend hzero hlip using fun n => hstep (Ln n) (hLn n)
  obtain ⟨ζ, π, hπζ, hs⟩ := hgraph L hLg
  refine ⟨ζ 0, π 0, hπζ 0, ?_⟩
  intro w₀ hw₀ hker
  obtain ⟨z, hz0, hzstep, hzn⟩ := hs h hlip hzero w₀ hw₀ hker
  have hzδ (n : ℕ) : ‖z n‖ ≤ δ := (hzn n).trans ((mul_le_of_le_one_right
    (by positivity : 0 ≤ 2 * ρ) (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))).trans hρδ)
  let Z := fun n => (⟨z n, hzδ n⟩ : {f : FourierL2 // ‖f‖ ≤ δ})
  let W := fun n => V n (Z n)
  have hWM (n : ℕ) : W n ⟨T, T.2, le_rfl⟩ = z (n + 1) := by
    calc
      _ = cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T (Ln n) (z n) +
          h n (Z n) := hend n (Z n)
      _ = cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T (Ln n) (z n) +
          cutoffRemainderExtension δ h n (z n) := by
        rw [cutoffRemainderExtension, dite_eq_left (hzδ n)]
      _ = _ := (hzstep n).symm
  have hWbound (n : ℕ) : ‖W n‖ ≤ B * (‖z n‖ +
      (expandingRadius L.1 ((n : ℝ) * T)) ^ (-2 - a)) := hV n (Z n)
  have hr : Real.exp (-(2 + a) * T / 2) ≤ 1 / 2 := by linarith
  have hWgeo := cutoffStep_path_geometric_bound a L.1 T B (2 * ρ)
    (lt_of_lt_of_le zero_lt_one L.2) hB.le hr z W hzn hWbound
  obtain ⟨u, hu, hu0, husol, hudecay⟩ := exists_cutoffGlobal_orbit_of_steps a b k L.1 T
    ha ha1 hk L.2 hT m χ hχ Qp hQp z W hWM (fun n => hsol n (Z n))
    (B * (2 * ρ + L.1 ^ (-2 - a))) (1 / 2) (by norm_num) (by norm_num)
    hWgeo
  refine ⟨u, hu, ?_, husol, hudecay⟩
  rw [hu0, add_sub_cancel_left]
  exact hz0

end DefocusingNLS

end OAI

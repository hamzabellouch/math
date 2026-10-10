import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCutoffPointwise
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCutoffCompact
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingEnergyObservation

namespace OAI

/-! # Actual matched profiles satisfy a coercive energy estimate on large tori -/

open Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem radialMatchedCutoff_energy_observation (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1) (m : ℕ) (hm : 0 < m) :
    ∃ N : ℕ, ∃ hN : 8 < ((N + 1 : ℕ) : ℝ),
    ∃ c : ℝ, 0 < c ∧ ∃ R : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (L : Radius), (R : ℝ) ≤ L.1 → ∀ f : FourierL2,
        let a := radialShootingA n
        let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
        let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
        let q := schwartzTorusSample a (N + 1 : ℕ) L.1 ha1 hN L.2 (radianFourierKernel
          (cutoffProfileSchwartz L.1 (by linarith [L.2]) χ hχ
            (radialMatchedCartesian n z) (radialMatchedCartesian_contDiff n z hX hz)));
        -a * ‖expandingLowEnergy a (N + 1 : ℕ) L.1 L.2 f‖ ^ 2 +
          (6 - 2 * a - (N + 1 : ℕ)) * ‖expandingHighEnergy a (N + 1 : ℕ) L.1 L.2 f‖ ^ 2 +
          2 * inner ℝ f (expandingLinearizedPotential a (N + 1 : ℕ) L.1 ha ha1 hN L.2 m q f) ≤
        -c * ‖f‖ ^ 2 + C * ‖expandingPhysicalBall a (N + 1 : ℕ) L.1 R ha ha1 hN L.2 f‖ ^ 2 := by
  let a := radialShootingA n
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  obtain ⟨P, hP, hPb⟩ := radialMatchedCutoff_pointwise_bound n z hX hz χ hχ hχzero m
  obtain ⟨N, hlarge⟩ := exists_nat_gt (max 8 (6 - 2 * a + 2 * ((2 * (m : ℝ) + 1) * P)))
  have hN : 8 < ((N + 1 : ℕ) : ℝ) := by
    have he := (le_max_left (8 : ℝ) _).trans_lt hlarge
    push_cast
    linarith
  have hgap : 0 < (N + 1 : ℕ) + 2 * a - 6 - 2 * ((2 * (m : ℝ) + 1) * P) := by
    have he := (le_max_right (8 : ℝ) _).trans_lt hlarge
    push_cast
    linarith
  let q : Radius → FourierL2 := fun L =>
    schwartzTorusSample a (N + 1 : ℕ) L.1 ha1 hN L.2 (radianFourierKernel
      (cutoffProfileSchwartz L.1 (by linarith [L.2]) χ hχ
        (radialMatchedCartesian n z) (radialMatchedCartesian_contDiff n z hX hz)))
  obtain ⟨Q, hQ, hQb⟩ := radialMatchedCutoff_sampling_bound n z hX hz (N + 1 : ℕ) hN χ hχ hχzero
  have hcompact (L : ℕ → Radius) (hL : Tendsto (fun j => (L j).1) atTop atTop) :
      ExpandingCompactApproximation a (N + 1 : ℕ) ha1 hN
        (fun j => (L j).1) (fun j => (L j).2) (fun j => q (L j)) :=
    radialMatchedCutoff_compactApproximation n z hX hz (N + 1 : ℕ) hN χ hχ hχzero hχone
      (fun j => (L j).1) (fun j => (L j).2) hL
  obtain ⟨c, hc, R, C, hC, hb⟩ := exists_expandingEnergy_observation a Q N ha ha1 hN hQ q
    (fun L => hQb L.1 L.2) hcompact m hm P hP (fun L x => hPb _ hN L.1 L.2 x) hgap
  exact ⟨N, hN, c, hc, R, C, hC, hb⟩

end DefocusingNLS

end OAI

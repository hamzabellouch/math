import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedPrescribedGenerator
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedEnergyObservation

namespace OAI

/-! # One Sobolev order for the spectral and expanding-torus energy estimates -/

open Filter Topology
open scoped SchwartzMap ContDiff

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem radialMatched_exists_common_order (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z = 0) →
      ∀ (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ)),
      (∀ y : E, 1 ≤ ‖y‖ → χ y = 0) → (∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1) →
      ∃ N : ℕ, ∃ hk10 : 10 < ((N + 1 : ℕ) : ℝ),
        let hk : 8 < ((N + 1 : ℕ) : ℝ) := lt_trans (by norm_num) hk10
        let a := radialShootingA n
        let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
        let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
        let b := radialShootingB (profileMatchingParameter z)
        let m := n + radialInnerShootingThreshold
        let qt : Radius → FourierL2 := fun L => schwartzTorusSample a (N + 1 : ℕ) L.1
          ha1 hk L.2 (radianFourierKernel (cutoffProfileSchwartz L.1 (by linarith [L.2])
            χ hχ (radialMatchedCartesian n z) (radialMatchedCartesian_contDiff n z hX hz)))
        ∃ q : HomogeneousY a ((N + 1 : ℕ) : ℝ),
          (∀ x : E, homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x =
            radialMatchedCartesian n z x) ∧
          HasSymmetryContourGenerator
            (homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk m q) ∧
          (∃ Q : ℝ, 0 ≤ Q ∧ ∀ L, ‖qt L‖ ≤ Q) ∧
          ∃ c : ℝ, 0 < c ∧ ∃ R : ℕ, ∃ C : ℝ, 0 ≤ C ∧
            ∀ (L : Radius), (R : ℝ) ≤ L.1 → ∀ f : FourierL2,
              -a * ‖expandingLowEnergy a (N + 1 : ℕ) L.1 L.2 f‖ ^ 2 +
                (6 - 2 * a - (N + 1 : ℕ)) * ‖expandingHighEnergy a (N + 1 : ℕ) L.1 L.2 f‖ ^ 2 +
                2 * inner ℝ f (expandingLinearizedPotential a (N + 1 : ℕ) L.1 ha ha1 hk L.2 m (qt L) f) ≤
              -c * ‖f‖ ^ 2 + C * ‖expandingPhysicalBall a (N + 1 : ℕ) L.1 R ha ha1 hk L.2 f‖ ^ 2 := by
  filter_upwards [radialMatched_symmetry_generator_of_gap hRou] with n hgen
  intro z hX hz χ hχ hχzero hχone
  let a := radialShootingA n
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  let m := n + radialInnerShootingThreshold
  have hm : 0 < m := radialShootingInner_power_pos n (profileMatchingParameter z)
  obtain ⟨P, hP, hPb⟩ := radialMatchedCutoff_pointwise_bound n z hX hz χ hχ hχzero m
  let D := 2 * (m : ℝ) + 1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (max 10 (6 - 2 * a + 2 * (D * max P 1)))
  have hk10 : 10 < ((N + 1 : ℕ) : ℝ) := by
    have h := (le_max_left (10 : ℝ) _).trans_lt hN
    exact h.trans (by exact_mod_cast Nat.lt_succ_self N)
  have hk : 8 < ((N + 1 : ℕ) : ℝ) := lt_trans (by norm_num) hk10
  have hlarge : 6 - 2 * a + 2 * (D * max P 1) < ((N + 1 : ℕ) : ℝ) :=
    ((le_max_right (10 : ℝ) _).trans_lt hN).trans (by exact_mod_cast Nat.lt_succ_self N)
  have hgap : 0 < ((N + 1 : ℕ) : ℝ) + 2 * a - 6 - 2 * (D * P) := by
    have h := mul_le_mul_of_nonneg_left (le_max_left P 1) hD
    linarith
  have hgap1 : 0 < ((N + 1 : ℕ) : ℝ) + 2 * a - 6 - 2 * D := by
    have h := mul_le_mul_of_nonneg_left (le_max_right P 1) hD
    linarith
  let qt : Radius → FourierL2 := fun L => schwartzTorusSample a (N + 1 : ℕ) L.1
    ha1 hk L.2 (radianFourierKernel (cutoffProfileSchwartz L.1 (by linarith [L.2])
      χ hχ (radialMatchedCartesian n z) (radialMatchedCartesian_contDiff n z hX hz)))
  obtain ⟨q, hq⟩ := radialMatchedCartesian_homogeneous n z hX hz
    ((N + 1 : ℕ) : ℝ) ha ha1 hk
  have hg := hgen z hX hz N hk q hq hgap1
  obtain ⟨Q, hQ, hQb⟩ := radialMatchedCutoff_sampling_bound n z hX hz (N + 1 : ℕ) hk χ hχ hχzero
  have hcompact (L : ℕ → Radius) (hL : Tendsto (fun j => (L j).1) atTop atTop) :
      ExpandingCompactApproximation a (N + 1 : ℕ) ha1 hk
        (fun j => (L j).1) (fun j => (L j).2) (fun j => qt (L j)) :=
    radialMatchedCutoff_compactApproximation n z hX hz (N + 1 : ℕ) hk χ hχ hχzero hχone
      (fun j => (L j).1) (fun j => (L j).2) hL
  obtain ⟨c, hc, R, C, hC, hb⟩ := exists_expandingEnergy_observation a Q N ha ha1 hk hQ qt
    (fun L => hQb L.1 L.2) hcompact m hm P hP (fun L x => hPb _ hk L.1 L.2 x) hgap
  exact ⟨N, hk10, q, hq, hg, ⟨Q, hQ, fun L => hQb L.1 L.2⟩, c, hc, R, C, hC, hb⟩

end DefocusingNLS

end OAI

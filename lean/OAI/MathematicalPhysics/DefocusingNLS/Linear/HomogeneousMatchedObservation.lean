import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEssentialContraction
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedPrincipal
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedProfileBounds

namespace OAI

/-! # The actual matched profile has a contracting essential time step

The integer differentiability order is chosen after the fixed power.  Its
principal coefficient is controlled by the proved global pressure bound;
no decay or spectral estimate is assumed for the evolution.
-/

open Set Filter Topology

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatched_exists_weakNull_contraction :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z = 0) →
      ∃ N : ℕ, ∃ hk : 8 < ((N + 1 : ℕ) : ℝ),
        let a := radialShootingA n
        let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
        let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
        let b := radialShootingB (profileMatchingParameter z)
        let m := n + radialInnerShootingThreshold
        ∃ q : HomogeneousY a ((N + 1 : ℕ) : ℝ),
          (∀ x : E, homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x =
            radialMatchedCartesian n z x) ∧
          ∃ c : ℝ, 0 < c ∧ ∀ (T : ℝ) (hT : 0 ≤ T) (A : ℝ)
            (u : ℕ → HomogeneousY a ((N + 1 : ℕ) : ℝ)),
            (∀ j, ‖u j‖ ≤ A) →
            (∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
              Tendsto (fun j => ℓ (u j)) atTop (𝓝 0)) →
            ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
              ‖homogeneousLinearizedPropagator a b ((N + 1 : ℕ) : ℝ) T ha ha1 hk hT
                m q (u j) ⟨T, hT, le_rfl⟩‖ ^ 2 <
                  Real.exp (-c * T) * A ^ 2 + ε := by
  filter_upwards [radialMatched_global_pressure_bound] with n hn z hX hz
  let a := radialShootingA n
  let m := n + radialInnerShootingThreshold
  have ha : 0 < a := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have ha1 : a < 1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  have hm : 1 ≤ m := radialShootingInner_power_pos n (profileMatchingParameter z)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 8 (6 - 2 * a + 2 * (2 * (m : ℝ) + 1) + 1))
  have hk : 8 < ((N + 1 : ℕ) : ℝ) := by
    have h8 := lt_of_le_of_lt (le_max_left (8 : ℝ) _) hN
    exact lt_trans h8 (by exact_mod_cast Nat.lt_succ_self N)
  have hgap : 0 < ((N + 1 : ℕ) : ℝ) + 2 * a - 6 -
      2 * ((2 * ((m - 1 + 1 : ℕ) : ℝ) + 1) * 1) := by
    have hbound := lt_of_le_of_lt (le_max_right (8 : ℝ) _) hN
    have hsucc : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [hsucc]
    push_cast
    nlinarith
  obtain ⟨q, hq⟩ := radialMatchedCartesian_homogeneous n z hX hz
    ((N + 1 : ℕ) : ℝ) ha ha1 hk
  have hQB (x : E) : ‖homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x‖ ^
      (2 * (m - 1 + 1)) ≤ 1 := by
    rw [Nat.sub_add_cancel hm, hq x]
    exact hn z ‖x‖ (norm_nonneg x)
  obtain ⟨c, hc, hcontract⟩ := homogeneousLinearized_weakNull_contraction a
    (radialShootingB (profileMatchingParameter z)) N ha ha1 hk (m - 1) q
    1 zero_le_one hQB hgap
  refine ⟨N, hk, q, hq, c, hc, ?_⟩
  simpa only [Nat.sub_add_cancel hm] using hcontract

end DefocusingNLS

end OAI

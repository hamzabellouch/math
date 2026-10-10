import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEnergyGenerator
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymmetryGenerator

namespace OAI

/-! # The matched symmetry generator at every sufficiently coercive order -/

open Filter Topology
open scoped NNReal

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatched_symmetry_generator_of_gap (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z = 0) → ∀ (N : ℕ)
      (hk : 8 < ((N + 1 : ℕ) : ℝ)),
      let a := radialShootingA n
      let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
      let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
      let b := radialShootingB (profileMatchingParameter z)
      let m := n + radialInnerShootingThreshold
      ∀ q : HomogeneousY a ((N + 1 : ℕ) : ℝ),
      (∀ x : E, homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x =
        radialMatchedCartesian n z x) →
      0 < ((N + 1 : ℕ) : ℝ) + 2 * a - 6 - 2 * (2 * (m : ℝ) + 1) →
      HasSymmetryContourGenerator
        (homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk m q) := by
  filter_upwards [radialMatched_global_pressure_bound,
    radialMatched_contour_spectral_stability hRou] with n hpressure hs
  intro z hX hz N hk a ha ha1 b m q hq hgap
  have hm : 1 ≤ m := radialShootingInner_power_pos n (profileMatchingParameter z)
  have hsucc : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hQB (x : E) : ‖homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x‖ ^
      (2 * (m - 1 + 1)) ≤ 1 := by
    rw [hsucc, hq]
    exact hpressure z ‖x‖ (norm_nonneg x)
  have hg : 0 < ((N + 1 : ℕ) : ℝ) + 2 * a - 6 -
      2 * ((2 * ((m - 1 + 1 : ℕ) : ℝ) + 1) * 1) := by
    simpa only [hsucc, mul_one] using hgap
  have hgen := homogeneousLinearized_finite_generator_of_gap a b N ha ha1 hk
    (m - 1) q 1 zero_le_one hQB hg
  rw [hsucc] at hgen
  obtain ⟨P, hP, hfin, hcomm, hdecay, G, hG, hgapG⟩ := hgen
  obtain ⟨hspec, hJordan⟩ := hs z hX hz (N + 1) ha ha1 hk q hq P hcomm hfin G hG
  have hJ : ∀ (lam : ℂ) (v w : P.range), w ≠ 0 → G w = lam • w → G v ≠ lam • v + w := by
    intro lam v w hw he
    exact hJordan lam v w hw he (hgapG lam w hw he).le
  let : FiniteDimensional ℂ P.range := hfin
  refine ⟨P, hP, hfin, hcomm, hdecay, G, hG, ?_, ?_⟩
  · intro lam w hw he
    exact hspec lam w hw he (hgapG lam w hw he).le
  · exact generator_eigenspaces_span G.toLinearMap hJ

end DefocusingNLS

end OAI

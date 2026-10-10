import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingIdentifiedCompactness
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingStableLimitEnergy
import OAI.MathematicalPhysics.DefocusingNLS.Linear.WeakLinearCoordinates

namespace OAI

/-! # Stable whole-space decay forces contraction along every expanding sequence -/

open Set Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local irreducible] expandingProfileTrajectory

theorem expandingProfile_stable_sequence (a b k T Q C₀ c C R D η β : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 10 < k) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (hC₀ : 0 ≤ C₀) (hc : 0 ≤ c) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hβ : 0 < β) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ) (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (hCb : ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2),
      ‖homogeneousLocalizationCLM a k L ha ha1 (by linarith) hL χ f‖ ≤ C₀ * ‖f‖)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (q : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ n t, ‖q n t‖ ≤ Q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ 1) (Q₀ : HomogeneousY a k)
    (π : HomogeneousY a k →L[ℝ] F)
    (hker : ∀ n, π (homogeneousLocalizationCLM a k (L n) ha ha1 (by linarith)
      (hL n) χ (f n)) = 0)
    (hqp : ∀ (s : Icc (0 : ℝ) T) (y : E),
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n) s)
        ha ha1 (by linarith) ((hL n).trans (expandingRadius_ge (L n) s (hL n) s.2.1)) (q n s) y)
        atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 (by linarith) Q₀ y)))
    (henergy : ∀ n (s : Icc (0 : ℝ) T) (w : FourierL2),
      let l := expandingRadiusCurve (L n) T (hL n) s;
      -a * ‖expandingLowEnergy a k l.1 l.2 w‖ ^ 2 +
        (6 - 2 * a - k) * ‖expandingHighEnergy a k l.1 l.2 w‖ ^ 2 +
        2 * inner ℝ w (expandingLinearizedPotential a k l.1 ha ha1 (by linarith) l.2 m (q n s) w) ≤
      -c * ‖w‖ ^ 2 + C * ‖expandingPhysicalBall a k l.1 R ha ha1 (by linarith) l.2 w‖ ^ 2)
    (hdecay : ∀ u : HomogeneousY a k, π u = 0 → ∀ t : Icc (0 : ℝ) T,
      ‖homogeneousLinearizedTrajectory a b k T ha ha1 (by linarith) hT m Q₀ u t‖ ≤
        D * Real.exp (-η * (t : ℝ)) * ‖u‖)
    (hsmall : escapedEnergyBound c (2 * η) 1
      (C * (‖homogeneousPhysicalCLM a k ha ha1 (by linarith)‖ * (D * C₀)) ^ 2) T < β ^ 2) :
    ∀ᶠ n in atTop, ‖expandingProfileTrajectory a b k (L n) T ha ha1 (by linarith)
      (hL n) hT m Q hQ (q n) (hq n) (f n) ⟨T, hT, le_rfl⟩‖ < β := by
  have hk8 : 8 < k := by linarith
  by_contra h
  obtain ⟨ψ, hψ, hbad⟩ := extraction_of_frequently_atTop (show ∃ᶠ n in atTop,
      β ≤ ‖expandingProfileTrajectory a b k (L n) T ha ha1 hk8
        (hL n) hT m Q hQ (q n) (hq n) (f n) ⟨T, hT, le_rfl⟩‖ by
    simpa only [not_eventually, not_lt] using h)
  obtain ⟨φ, hφ, v, u₀, hu₀, hv, hphysical, hweak⟩ :=
    expandingProfile_exists_identified_limit a b k T Q 1 C₀ ha ha1 hk hT hQ
      zero_le_one hC₀ m χ ρ hρ hχ hCb (fun n => L (ψ n)) (fun n => hL (ψ n))
      (hLinf.comp hψ.tendsto_atTop) (fun n => q (ψ n)) (fun n => hq (ψ n))
      (fun n => f (ψ n)) (fun n => hf (ψ n)) Q₀
      (fun t y => (hqp t y).comp hψ.tendsto_atTop)
  let σ := fun n => ψ (φ n)
  have hu0 : ‖u₀‖ ≤ C₀ := by simpa only [mul_one] using hu₀
  have hinitial : homogeneousLinearizedTrajectory a b k T ha ha1 hk8 hT m Q₀ u₀
      ⟨0, le_rfl, hT⟩ = u₀ := by
    rw [homogeneousLinearizedTrajectory_eq]
    simp only [homogeneousDuhamel, intervalIntegral.integral_same, add_zero,
      homogeneousFreeOperator_zero]
  have hw₀ (ℓ : HomogeneousY a k →L[ℝ] ℂ) :
      Tendsto (fun n => ℓ (homogeneousLocalizationCLM a k (L (σ n)) ha ha1 hk8
        (hL (σ n)) χ (f (σ n)))) atTop (𝓝 (ℓ u₀)) := by
    simpa only [expandingProfileTrajectory_initial, expandingRadius, zero_div,
      Real.exp_zero, mul_one, hinitial] using hweak ⟨0, le_rfl, hT⟩ ℓ
  have hπ : π u₀ = 0 := weakLimit_map_eq_zero π _ u₀ hw₀ (fun n => hker (σ n))
  have hd (t : Icc (0 : ℝ) T) :
      ‖homogeneousLinearizedTrajectory a b k T ha ha1 hk8 hT m Q₀ u₀ t‖ ≤
        (D * C₀) * Real.exp (-η * (t : ℝ)) := by
    calc
      _ ≤ D * Real.exp (-η * (t : ℝ)) * ‖u₀‖ := hdecay u₀ hπ t
      _ ≤ D * Real.exp (-η * (t : ℝ)) * C₀ :=
        mul_le_mul_of_nonneg_left hu0 (by positivity)
      _ = _ := by ring
  let B := escapedEnergyBound c (2 * η) 1
    (C * (‖homogeneousPhysicalCLM a k ha ha1 hk8‖ * (D * C₀)) ^ 2) T
  have hB : B < β ^ 2 := hsmall
  have heps : 0 < (β ^ 2 - B) / 2 := by linarith
  have hb := expandingProfile_stable_limit_energy a b k T Q 1 c C R (D * C₀) η
    ha ha1 hk8 hT hQ zero_le_one hc hC m (fun n => L (σ n)) (fun n => hL (σ n))
    (fun n => q (σ n)) (fun n => hq (σ n)) (fun n => f (σ n)) (fun n => hf (σ n))
    (fun n => henergy (σ n)) v
    (fun t => homogeneousLinearizedTrajectory a b k T ha ha1 hk8 hT m Q₀ u₀ t)
    hphysical (mul_nonneg hD hC₀) hd hv ((β ^ 2 - B) / 2) heps
  obtain ⟨j, hj⟩ := hb.exists
  have hbadj := pow_le_pow_left₀ hβ.le (hbad (φ j)) 2
  change _ ≤ B + (β ^ 2 - B) / 2 at hj
  linarith

end DefocusingNLS

end OAI

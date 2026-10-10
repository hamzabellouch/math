import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexDecomposition
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexSemigroup

namespace OAI

/-! # The actual matched complex semigroup has a finite-rank contracting step

The step length is chosen after the proved energy decay rate. No spectral
splitting or semigroup decay assumption enters this construction.
-/

open Filter Topology
open scoped NNReal

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatched_exists_complex_step_decomposition :
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
          ∃ t : ℝ≥0, 0 < t ∧
            ∃ B K : (HomogeneousY a ((N + 1 : ℕ) : ℝ) ×
                HomogeneousY a ((N + 1 : ℕ) : ℝ)) →L[ℂ]
              (HomogeneousY a ((N + 1 : ℕ) : ℝ) × HomogeneousY a ((N + 1 : ℕ) : ℝ)),
              homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ)
                ha ha1 hk m q t = B + K ∧
              ‖B‖ < 1 ∧ FiniteDimensional ℂ (LinearMap.range K.toLinearMap) := by
  filter_upwards [radialMatched_exists_weakNull_contraction] with n hn z hX hz
  obtain ⟨N, hk, q, hq, c, hc, hcontract⟩ := hn z hX hz
  let a := radialShootingA n
  let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  let b := radialShootingB (profileMatchingParameter z)
  let m := n + radialInnerShootingThreshold
  let T := (Real.log 4 + 1) / c
  have hT : 0 < T := div_pos (by have := Real.log_pos (show (1 : ℝ) < 4 by norm_num); linarith) hc
  let t : ℝ≥0 := ⟨T, hT.le⟩
  have hexp : Real.exp (-c * T) < 1 / 4 := by
    have heq : -c * T = -(Real.log 4 + 1) := by
      dsimp only [T]
      field_simp
    rw [heq, Real.exp_neg, Real.exp_add, Real.exp_log (by norm_num)]
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ (by positivity)).mpr
    have h := (Real.one_lt_exp_iff).mpr (show (0 : ℝ) < 1 by norm_num)
    nlinarith
  let S := homogeneousLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk m q t
  have hvalue (v : HomogeneousY a ((N + 1 : ℕ) : ℝ)) :
      S v = homogeneousLinearizedPropagator a b ((N + 1 : ℕ) : ℝ) T ha ha1 hk
        hT.le m q v ⟨T, hT.le, le_rfl⟩ := rfl
  have hweak : ∀ u : ℕ → HomogeneousY a ((N + 1 : ℕ) : ℝ), (∀ j, ‖u j‖ ≤ 1) →
      (∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
        Tendsto (fun j => ℓ (u j)) atTop (𝓝 0)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ‖S (u j)‖ ^ 2 < Real.exp (-c * T) + ε := by
    intro u hu hw ε hε
    simp_rw [hvalue]
    simpa only [a, b, m, one_pow, mul_one] using
      hcontract T hT.le 1 u hu hw ε hε
  obtain ⟨B, K, hS, hB, hK⟩ := homogeneousOperator_complexFiniteRank_contraction a
    ((N + 1 : ℕ) : ℝ) (Real.exp (-c * T)) ha ha1 hk (Real.exp_pos _).le hexp S hweak
  exact ⟨N, hk, q, hq, t, hT, B, K, hS, hB, hK⟩

end DefocusingNLS

end OAI

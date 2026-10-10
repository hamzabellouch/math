import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteRankStep
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedObservation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLinearizedSemigroup

namespace OAI

/-! # Finite-rank decomposition of the actual matched time-one evolution -/

open Filter Topology Set

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousLinearizedTimeOne (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k) :
    HomogeneousY a k →L[ℝ] HomogeneousY a k :=
  homogeneousLinearizedStep a b k ha ha1 hk m q 1

theorem homogeneousLinearizedTimeOne_pow (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m n : ℕ) (q : HomogeneousY a k) :
    (homogeneousLinearizedTimeOne a b k ha ha1 hk m q) ^ n =
      homogeneousLinearizedStep a b k ha ha1 hk m q n :=
  (homogeneousLinearizedStep_nat a b k ha ha1 hk m q n).symm

theorem radialMatched_exists_timeOne_decomposition :
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
          ∃ B K : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ]
              HomogeneousY a ((N + 1 : ℕ) : ℝ),
            homogeneousLinearizedTimeOne a b ((N + 1 : ℕ) : ℝ) ha ha1 hk m q = B + K ∧
              ‖B‖ < 1 ∧ FiniteDimensional ℝ (LinearMap.range K.toLinearMap) ∧
                IsCompactOperator K := by
  filter_upwards [radialMatched_exists_weakNull_contraction] with n hn z hX hz
  obtain ⟨N, hk, q, hq, c, hc, hcontract⟩ := hn z hX hz
  let a := radialShootingA n
  let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  let b := radialShootingB (profileMatchingParameter z)
  let m := n + radialInnerShootingThreshold
  let T := homogeneousLinearizedTimeOne a b ((N + 1 : ℕ) : ℝ) ha ha1 hk m q
  have hvalue (v : HomogeneousY a ((N + 1 : ℕ) : ℝ)) :
      T v = homogeneousLinearizedPropagator a b ((N + 1 : ℕ) : ℝ) 1 ha ha1 hk
        zero_le_one m q v ⟨1, zero_le_one, le_rfl⟩ := rfl
  have hweak : ∀ u : ℕ → HomogeneousY a ((N + 1 : ℕ) : ℝ), (∀ j, ‖u j‖ ≤ 1) →
      (∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
        Tendsto (fun j => ℓ (u j)) atTop (𝓝 0)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ‖T (u j)‖ ^ 2 < Real.exp (-c) + ε := by
    intro u hu hw ε hε
    simp_rw [hvalue]
    simpa only [a, b, m, mul_one, one_pow] using
      hcontract 1 zero_le_one 1 u hu hw ε hε
  obtain ⟨B, K, hT, hB, hK⟩ := homogeneousOperator_finiteRank_contraction a
    ((N + 1 : ℕ) : ℝ) (Real.exp (-c)) ha1 hk (Real.exp_pos _).le
    (by rw [Real.exp_lt_one_iff]; linarith) T hweak
  exact ⟨N, hk, q, hq, B, K, hT, hB, hK,
    homogeneousOperator_isCompact_of_finiteRange a ((N + 1 : ℕ) : ℝ) K hK⟩

end DefocusingNLS

end OAI

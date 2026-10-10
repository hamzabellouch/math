import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedComplexDecomposition
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSemigroupContour
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexStrongContinuity

namespace OAI

/-! # A finite-dimensional exceptional space for the actual matched evolution

This applies the contour construction to the proved matched-profile time
step. Identification of the exceptional space with the symmetry modes is
the remaining spectral classification step.
-/

open Filter Topology
open scoped NNReal

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatched_exists_invariant_contour :
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
          ∃ t : ℝ≥0, 0 < t ∧ ∃ r : ℝ,
            Real.exp (-(t : ℝ) / 32) < r ∧ r < 1 ∧
            ∃ Q : (HomogeneousY a ((N + 1 : ℕ) : ℝ) ×
                HomogeneousY a ((N + 1 : ℕ) : ℝ)) →L[ℂ]
              (HomogeneousY a ((N + 1 : ℕ) : ℝ) × HomogeneousY a ((N + 1 : ℕ) : ℝ)),
              IsIdempotentElem Q ∧
              FiniteDimensional ℂ (LinearMap.range Q.toLinearMap) ∧
              (∀ s : ℝ≥0, Commute
                (homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk m q s) Q) ∧
              ∃ D δ : ℝ, 0 ≤ D ∧ 0 < δ ∧ ∀ s : ℝ≥0, ∀ u, Q u = 0 →
                ‖homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ)
                  ha ha1 hk m q s u‖ ≤ D * Real.exp (-δ * (s : ℝ)) * ‖u‖ := by
  filter_upwards [radialMatched_exists_complex_step_decomposition] with n hn z hX hz
  obtain ⟨N, hk, q, hq, t, ht, B, K, hstep, hB, hK⟩ := hn z hX hz
  let a := radialShootingA n
  let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  let b := radialShootingB (profileMatchingParameter z)
  let m := n + radialInnerShootingThreshold
  let S := homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk m q
  have hSc (u : HomogeneousY a ((N + 1 : ℕ) : ℝ) ×
      HomogeneousY a ((N + 1 : ℕ) : ℝ)) :
      Continuous (fun s : ℝ≥0 => S s u) := by
    exact stronglyContinuous_homogeneousComplexLinearizedStep a b
      ((N + 1 : ℕ) : ℝ) ha ha1 hk m q u
  have htR : 0 < (t : ℝ) := ht
  have hη : Real.exp (-(t : ℝ) / 32) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos htR) (by norm_num)
  obtain ⟨r, hηr, hr, Q, hQ, hfin, hcomm, hdecay⟩ :=
    semigroup_contour_decomposition S
      (show S 0 = 1 from homogeneousComplexLinearizedStep_zero a b
        ((N + 1 : ℕ) : ℝ) ha ha1 hk m q)
      (fun s t => homogeneousComplexLinearizedStep_add a b
        ((N + 1 : ℕ) : ℝ) ha ha1 hk m q s t)
      hSc t ht B K hstep hB hK (Real.exp (-(t : ℝ) / 32)) hη
  exact ⟨N, hk, q, hq, t, ht, r, hηr, hr, Q, hQ, hfin, hcomm, hdecay⟩

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousMatchedComplexDecomposition
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexStrongContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousContourGenerator

namespace OAI

/-! # The finite-dimensional generator for the actual matched profile

This is the concrete semigroup conclusion preceding identification of its
finite-dimensional modes with the symmetry modes.
-/

open Filter Topology
open scoped NNReal

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatched_exists_finite_generator :
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
          HasFiniteContourGenerator
            (homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk m q) := by
  filter_upwards [radialMatched_exists_complex_step_decomposition] with n hn z hX hz
  obtain ⟨N, hk, q, hq, t, ht, B, K, hstep, hB, hK⟩ := hn z hX hz
  let a := radialShootingA n
  let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  let b := radialShootingB (profileMatchingParameter z)
  let m := n + radialInnerShootingThreshold
  let S := homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk m q
  have hSc (u : HomogeneousY a ((N + 1 : ℕ) : ℝ) ×
      HomogeneousY a ((N + 1 : ℕ) : ℝ)) : Continuous (fun s : ℝ≥0 => S s u) :=
    stronglyContinuous_homogeneousComplexLinearizedStep a b
      ((N + 1 : ℕ) : ℝ) ha ha1 hk m q u
  have hgen := semigroup_contour_generator S
      (show S 0 = 1 from homogeneousComplexLinearizedStep_zero a b
        ((N + 1 : ℕ) : ℝ) ha ha1 hk m q)
      (fun s t => homogeneousComplexLinearizedStep_add a b
        ((N + 1 : ℕ) : ℝ) ha ha1 hk m q s t)
      hSc t ht B K hstep hB hK
  exact ⟨N, hk, q, hq, hgen⟩

end DefocusingNLS

end OAI

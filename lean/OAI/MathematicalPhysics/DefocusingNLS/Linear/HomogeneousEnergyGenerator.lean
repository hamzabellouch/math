import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEssentialContraction
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexDecomposition
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousComplexStrongContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousContourGenerator

namespace OAI

/-! # The finite contour generator at a prescribed coercive Sobolev order -/

open Filter Topology
open scoped NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousLinearized_finite_generator_of_gap (a b : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < ((N + 1 : ℕ) : ℝ))
    (m : ℕ) (q : HomogeneousY a ((N + 1 : ℕ) : ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hQB : ∀ x : E, ‖homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x‖ ^
      (2 * (m + 1)) ≤ M)
    (hgap : 0 < ((N + 1 : ℕ) : ℝ) + 2 * a - 6 -
      2 * ((2 * ((m + 1 : ℕ) : ℝ) + 1) * M)) :
    HasFiniteContourGenerator
      (homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q) := by
  obtain ⟨c, hc, hcontract⟩ :=
    homogeneousLinearized_weakNull_contraction a b N ha ha1 hk m q M hM hQB hgap
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
  let S := homogeneousLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q t
  have hvalue (v : HomogeneousY a ((N + 1 : ℕ) : ℝ)) :
      S v = homogeneousLinearizedPropagator a b ((N + 1 : ℕ) : ℝ) T ha ha1 hk
        hT.le (m + 1) q v ⟨T, hT.le, le_rfl⟩ := rfl
  have hweak : ∀ u : ℕ → HomogeneousY a ((N + 1 : ℕ) : ℝ), (∀ j, ‖u j‖ ≤ 1) →
      (∀ ℓ : HomogeneousY a ((N + 1 : ℕ) : ℝ) →L[ℝ] ℂ,
        Tendsto (fun j => ℓ (u j)) atTop (𝓝 0)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ‖S (u j)‖ ^ 2 < Real.exp (-c * T) + ε := by
    intro u hu hw ε hε
    simp_rw [hvalue]
    simpa only [one_pow, mul_one] using
      hcontract T hT.le 1 u hu hw ε hε
  obtain ⟨B, K, hS, hB, hK⟩ := homogeneousOperator_complexFiniteRank_contraction a
    ((N + 1 : ℕ) : ℝ) (Real.exp (-c * T)) ha ha1 hk (Real.exp_pos _).le hexp S hweak
  let SC := homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q
  have hSc (u : HomogeneousY a ((N + 1 : ℕ) : ℝ) ×
      HomogeneousY a ((N + 1 : ℕ) : ℝ)) : Continuous (fun s : ℝ≥0 => SC s u) :=
    stronglyContinuous_homogeneousComplexLinearizedStep a b
      ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q u
  exact semigroup_contour_generator SC
    (homogeneousComplexLinearizedStep_zero a b ((N + 1 : ℕ) : ℝ) ha ha1 hk (m + 1) q)
    (fun s t => homogeneousComplexLinearizedStep_add a b ((N + 1 : ℕ) : ℝ)
      ha ha1 hk (m + 1) q s t) hSc t hT B K hS hB hK

end DefocusingNLS

end OAI

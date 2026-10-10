import OAI.Analysis.KadisonKastler.SelfAdjointPolarCorrection

namespace OAI

/-! # Projection rounding through a selfadjoint polar factor -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]

theorem exists_projection_near_almost_symmetry
    (x : A) (hx : IsSelfAdjoint x) {r : ℝ} (hr : 0 ≤ r) (hrsmall : r < 1 / 4)
    (hn : ‖x‖ ≤ 1 + r) (hd : ‖x * x - 1‖ ≤ r) :
    ∃ q : A, IsStarProjection q ∧ ‖q - (1 / 2 : ℝ) • (x + 1)‖ ≤ 3 * r / 2 := by
  obtain ⟨u, hu, hun⟩ := exists_selfAdjoint_unitary_of_square_defect x hx hr hrsmall hn hd
  let q : A := (1 / 2 : ℝ) • ((u : A) + 1)
  have huu : (u : A) * (u : A) = 1 := by
    simpa only [hu.star_eq] using u.property.1
  have hq : IsStarProjection q := by
    constructor
    · change q * q = q
      dsimp [q]
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, add_mul, mul_add, mul_add,
        huu, mul_one, one_mul, one_mul]
      module
    · change star q = q
      simp only [q, star_smul, star_trivial, star_add, hu.star_eq, star_one]
  refine ⟨q, hq, ?_⟩
  have he : q - (1 / 2 : ℝ) • (x + 1) = (1 / 2 : ℝ) • ((u : A) - x) := by
    dsimp [q]
    module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith

end

end KadisonKastler

end OAI

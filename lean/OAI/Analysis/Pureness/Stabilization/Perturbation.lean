import OAI.Analysis.Pureness.Stabilization.OrderComparison

namespace OAI
noncomputable section
open scoped NNReal Topology
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem conjugate_cuntzBelow (b : Positive A) (v : A) :
    CuntzBelow ⟨star v * b.1 * v, star_left_conjugate_nonneg b.2 v⟩ b := by
  intro η hη
  exact ⟨v, by simpa using hη⟩

theorem cut_cuntzBelow_of_norm_sub_lt (a b : Positive A) (ε : ℝ≥0) (hε : 0 < ε)
    (hab : ‖a.1 - b.1‖ < (ε : ℝ)) : CuntzBelow (Positive.cut ε a) b := by
  obtain ⟨g, hgs, hga, hgg⟩ := fixedCut_factorization a hε
  let c := Positive.cut ε a
  let d : Positive A := ⟨star g * b.1 * g, star_left_conjugate_nonneg b.2 g⟩
  let k : ℝ := ‖a.1 - b.1‖ * (ε : ℝ)⁻¹
  have hk0 : 0 ≤ k := mul_nonneg (norm_nonneg _) (inv_nonneg.mpr ε.2)
  have hk1 : k < 1 := by
    dsimp [k]
    rw [← div_eq_mul_inv]
    exact (div_lt_one (show (0 : ℝ) < ε from hε)).mpr hab
  have hcd : c.1 - d.1 ≤ k • c.1 := by
    have h := CStarAlgebra.star_left_conjugate_le_norm_smul
      (a := g) (b := a.1 - b.1)
      ((IsSelfAdjoint.of_nonneg a.2).sub (IsSelfAdjoint.of_nonneg b.2))
    rw [hgs] at h
    have heq : c.1 - d.1 = g * (a.1 - b.1) * g := by
      dsimp [c, d]
      rw [hgs, ← hga]
      noncomm_ring
    rw [heq]
    exact h.trans (by simpa only [smul_smul] using
      smul_le_smul_of_nonneg_left hgg (norm_nonneg (a.1 - b.1)))
  have hsmall : (1 - k) • c.1 ≤ d.1 := by
    rw [sub_smul, one_smul]
    exact sub_le_iff_le_add.mpr (by
      have h := sub_le_iff_le_add.mp hcd
      simpa only [add_comm] using h)
  have hdom : c.1 ≤ (1 - k)⁻¹ • d.1 := by
    have h := smul_le_smul_of_nonneg_left hsmall (inv_nonneg.mpr (by linarith : 0 ≤ 1-k))
    simpa only [smul_smul, inv_mul_cancel₀ (by linarith : 1-k ≠ 0), one_smul] using h
  exact (CuntzBelow.of_le_smul c d (1-k)⁻¹ (inv_nonneg.mpr (by linarith)) hdom).trans
    (conjugate_cuntzBelow b g)
end CuntzTrace

end

end OAI

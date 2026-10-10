import OAI.Analysis.Pureness.Divisibility.FiniteCutComparison

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace Filter
open scoped NNReal Topology
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

theorem positive_cut_cuntzBelow_of_le_add_smul_one (a b : Positive D)
    (t ε : ℝ≥0) (htε : t < ε) (hab : a.1 ≤ b.1 + (t : ℝ) • (1 : D)) :
    CuntzBelow (Positive.cut ε a) b := by
  have hε : 0 < ε := lt_of_le_of_lt t.2 htε
  obtain ⟨g,hgs,hga,hgg⟩ := fixedCut_factorization a hε
  let c := Positive.cut ε a
  let e : Positive D := ⟨star g * b.1 * g, star_left_conjugate_nonneg b.2 g⟩
  let k : ℝ := (t : ℝ) * (ε : ℝ)⁻¹
  have hk1 : k < 1 := by
    dsimp [k]
    rw [← div_eq_mul_inv]
    exact (div_lt_one (show (0 : ℝ) < ε from hε)).mpr htε
  have hcd : c.1 - e.1 ≤ k • c.1 := by
    have hab' : a.1 - b.1 ≤ (t : ℝ) • (1 : D) := sub_le_iff_le_add.mpr (by simpa [add_comm] using hab)
    have h := star_left_conjugate_le_conjugate hab' g
    rw [hgs] at h
    have heq : c.1 - e.1 = g * (a.1 - b.1) * g := by
      dsimp [c,e]
      rw [hgs,← hga]
      noncomm_ring
    rw [heq]
    calc
      g * (a.1-b.1)*g ≤ (t : ℝ) • (g*g) := by simpa only [mul_smul_comm,smul_mul_assoc,mul_one] using h
      _ ≤ k • c.1 := by
        dsimp [k,c]
        rw [← smul_smul]
        exact smul_le_smul_of_nonneg_left hgg (show (0 : ℝ) ≤ (t : ℝ) from t.2)
  have hsmall : (1-k) • c.1 ≤ e.1 := by
    rw [sub_smul,one_smul]
    exact sub_le_iff_le_add.mpr (by simpa only [add_comm] using sub_le_iff_le_add.mp hcd)
  have hdom : c.1 ≤ (1-k)⁻¹ • e.1 := by
    have h := smul_le_smul_of_nonneg_left hsmall (inv_nonneg.mpr (by linarith : 0 ≤ 1-k))
    simpa only [smul_smul,inv_mul_cancel₀ (by linarith : 1-k ≠ 0),one_smul] using h
  exact (CuntzBelow.of_le_smul c e (1-k)⁻¹ (inv_nonneg.mpr (by linarith)) hdom).trans
    (conjugate_cuntzBelow b g)

theorem positive_cut_cuntzBelow_of_le (a b : Positive D) (hab : a ≤ b) (t : ℝ≥0) :
    CuntzBelow (Positive.cut t a) (Positive.cut t b) := by
  have hb : b.1 ≤ (Positive.cut t b).1 + (t : ℝ) • (1 : D) := by
    have hs := ((IsSelfAdjoint.of_nonneg b.2).sub (IsSelfAdjoint.of_nonneg (Positive.cut t b).2)).le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at hs
    have hn := Positive.norm_sub_cut_le t b
    have h : b.1 - (Positive.cut t b).1 ≤ (t : ℝ) • (1 : D) :=
      hs.trans (smul_le_smul_of_nonneg_right hn zero_le_one)
    simpa only [add_comm] using sub_le_iff_le_add.mp h
  apply CuntzBelow.of_tendsto (fun k => Positive.cut (Positive.rootExponent k) (Positive.cut t a))
  · apply Positive.tendsto_cut
    simpa [Positive.rootExponent] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun k : ℕ => 1/((k : ℝ)+1)) atTop (𝓝 0))
  · intro k
    rw [Positive.cut_cut]
    exact positive_cut_cuntzBelow_of_le_add_smul_one a (Positive.cut t b) t
      (t+Positive.rootExponent k) (lt_add_of_pos_right t (Positive.rootExponent_pos k))
      ((show a.1 ≤ b.1 from hab).trans hb)
end CuntzPureness

end

end OAI

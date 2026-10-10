import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimitiveHeatCusp

namespace OAI

/-! Full-group reduction and exponential decay for the truncated row heat. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaPrimitiveHeat_nonneg (p : ℂ × ℝ) (t : ℝ) :
    0≤cubicThetaPrimitiveHeat p t := tsum_nonneg (cubicThetaPrimitiveHeatTerm_nonneg p t)

lemma cubicThetaPrimitiveHeat_invariant (g : SL(2,Eisenstein))
    {p : ℂ × ℝ} (hp : 0<p.2) (t : ℝ) :
    cubicThetaPrimitiveHeat (cubicThetaMobius (cubicThetaFullComplex g) p) t=
      cubicThetaPrimitiveHeat p t := by
  unfold cubicThetaPrimitiveHeat cubicThetaPrimitiveHeatTerm
  simp_rw [←CubicThetaPrimitiveRow.height_rightMul _ g hp]
  exact (CubicThetaPrimitiveRow.rightMulEquiv g).tsum_eq
    (fun r => if r.height p≤1 then Real.exp (-t/r.height p) else (0:ℝ))

theorem cubicThetaPrimitiveHeat_uniform :
    ∃ C : ℝ, 0≤C ∧ ∀ p : ℂ × ℝ, 0<p.2 → ∀ t : ℝ, 0<t →
      cubicThetaPrimitiveHeat p t≤C*(1+t⁻¹^2) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaPrimitiveHeat_cusp_bound
  refine ⟨C,hC,?_⟩
  intro p hp t ht
  obtain ⟨g,hg⟩ := cubicThetaSiegelSet_meets_orbit hp
  have h := hbound _ hg.2.2 t ht
  rwa [cubicThetaPrimitiveHeat_invariant g hp] at h

lemma cubicThetaPrimitiveHeat_half {p : ℂ × ℝ} (hp : 0<p.2)
    {t : ℝ} (ht : 0<t) :
    cubicThetaPrimitiveHeat p t≤Real.exp (-t/2)*cubicThetaPrimitiveHeat p (t/2) := by
  have hh : 0<t/2 := by linarith
  have hs := (cubicThetaPrimitiveHeat_summable hp hh).mul_left (Real.exp (-t/2))
  calc
    _ ≤ ∑' r : CubicThetaPrimitiveRow,Real.exp (-t/2)*cubicThetaPrimitiveHeatTerm p (t/2) r := by
      apply (cubicThetaPrimitiveHeat_summable hp ht).tsum_le_tsum _ hs
      intro r
      unfold cubicThetaPrimitiveHeatTerm
      split_ifs with hr
      · rw [←Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hx := r.height_pos hp
        have hi : 1≤(r.height p)⁻¹ := (one_le_inv₀ hx).mpr hr
        simp only [div_eq_mul_inv]
        nlinarith
      · simp only [mul_zero,le_refl]
    _ = _ := by rw [tsum_mul_left]; rfl

theorem cubicThetaPrimitiveHeat_small_large :
    ∃ C : ℝ, 0≤C ∧ ∀ p : ℂ × ℝ, 0<p.2 →
      (∀ t : ℝ, 0<t → cubicThetaPrimitiveHeat p t≤C*(1+t⁻¹^2)) ∧
      (∀ t : ℝ, 1≤t → cubicThetaPrimitiveHeat p t≤5*C*Real.exp (-t/2)) := by
  obtain ⟨C,hC,hbound⟩ := cubicThetaPrimitiveHeat_uniform
  refine ⟨C,hC,?_⟩
  intro p hp
  refine ⟨hbound p hp,?_⟩
  intro t ht
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  have h := (cubicThetaPrimitiveHeat_half hp ht0).trans
    (mul_le_mul_of_nonneg_left (hbound p hp (t/2) (by linarith)) (Real.exp_pos _).le)
  have hinv : (t/2)⁻¹≤2 := by
    have hh : 0<t/2 := by linarith
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hh).mpr
    linarith
  have hpow : (t/2)⁻¹^2≤4 := by nlinarith [inv_nonneg.mpr (by linarith : 0≤t/2)]
  have hC' := mul_le_mul_of_nonneg_left (show 1+(t/2)⁻¹^2≤5 by linarith) hC
  have h' := mul_le_mul_of_nonneg_left hC' (Real.exp_pos (-t/2)).le
  exact h.trans (by nlinarith [h'])

end CubicFirstMoment

end

end OAI

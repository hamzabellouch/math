import OAI.NumberTheory.Ostmann.Tree.WeightedAffine

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

theorem weightedAffine_meanzero_bound (w : (ZMod p)ˣ → ℂ) (f : ZMod p → ℂ)
    (hw : ∑ r, ‖w r‖^2 ≤ (p:ℝ)) (hf : mean f=0) (hfn : l2Sq f ≤ 1) :
    l2Sq (weightedAffine w f) ≤ Real.sqrt (3/(p:ℝ)) := by
  have hp : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hw0 : 0 ≤ ∑ r, ‖w r‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : (∑ u, ∑ b, ‖affineUnitCoefficient w u b‖^2) ≤ 3*(p:ℝ)^2 :=
    (affineUnitCoefficient_energy w).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hw 2) (by norm_num))
  have haction : l2Sq (affineAction (affineUnitCoefficient w) f) ≤ 3*(p:ℝ)^3*l2Sq f := by
    apply (affineAction_l2Sq_le _ _ hf).trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hp.le) (l2Sq_nonneg f)
    convert hh using 1
    ring
  have hscale : ‖(p:ℂ)⁻¹*(p:ℂ)⁻¹‖^2 = ((p:ℝ)⁻¹)^4 := by
    simp only [norm_mul, norm_inv, Complex.norm_natCast]
    ring
  have hadj : l2Sq (weightedAffineAdjoint w (weightedAffine w f)) ≤
      (3/(p:ℝ))*l2Sq f := by
    rw [weightedAffine_adjoint_comp, l2Sq_const_mul, hscale]
    calc
      _ ≤ ((p:ℝ)⁻¹)^4 * (3*(p:ℝ)^3*l2Sq f) :=
        mul_le_mul_of_nonneg_left haction (by positivity)
      _ = _ := by field_simp
  have hcs := meanInner_norm_sq_le f (weightedAffineAdjoint w (weightedAffine w f))
  rw [← weightedAffine_adjoint, meanInner_self, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (l2Sq_nonneg _)] at hcs
  have hx : l2Sq (weightedAffine w f)^2 ≤ 3/(p:ℝ) := by
    calc
      _ ≤ l2Sq f * l2Sq (weightedAffineAdjoint w (weightedAffine w f)) := hcs
      _ ≤ l2Sq f * ((3/(p:ℝ))*l2Sq f) :=
        mul_le_mul_of_nonneg_left hadj (l2Sq_nonneg f)
      _ = (3/(p:ℝ))*(l2Sq f)^2 := by ring
      _ ≤ (3/(p:ℝ))*1^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (l2Sq_nonneg f) hfn 2) (by positivity)
      _ = _ := by ring
  exact (Real.le_sqrt (l2Sq_nonneg _) (by positivity)).mpr hx

end
end Ostmann.FiniteField

end OAI

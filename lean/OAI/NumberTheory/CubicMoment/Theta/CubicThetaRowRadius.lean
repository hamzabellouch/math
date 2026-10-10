import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinUnfold

namespace OAI

/-! Exact scaling and absolute convergence of a nonzero Eisenstein row
in the radial coordinate used for the Gaussian Mellin integral. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaRowRadius (c : Eisenstein) (p : ℂ × ℝ) (d : Eisenstein) : ℝ :=
  Complex.normSq (p.1+(d:ℂ)/(c:ℂ))+p.2^2

lemma cubicThetaRowRadius_pos (c d : Eisenstein) {p : ℂ × ℝ} (hp : 0 < p.2) :
    0 < cubicThetaRowRadius c p d :=
  add_pos_of_nonneg_of_pos (Complex.normSq_nonneg _) (sq_pos_of_pos hp)

lemma cubicThetaRowRadius_scale {c : Eisenstein} (hc : c ≠ 0)
    (p : ℂ × ℝ) (d : Eisenstein) :
    norm c*cubicThetaRowRadius c p d =
      Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2 := by
  have hcC : (c:ℂ) ≠ 0 := fun h => hc (Subtype.ext h)
  unfold cubicThetaRowRadius
  rw [mul_add]
  congr 1
  change Complex.normSq (c:ℂ)*Complex.normSq (p.1+(d:ℂ)/(c:ℂ)) = _
  rw [← map_mul, mul_add, mul_div_cancel₀ _ hcC]

lemma cubicThetaEisensteinGridTerm_row {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (d : Eisenstein) (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinGridTerm (c,d) p s = cubicThetaEisensteinWeight c d*
      ((p.2/(Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2):ℝ):ℂ)^s := by
  by_cases hd : primary d ∧ IsCoprime c d <;>
    simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,
      cubicThetaEisensteinWeight,hc,hd]

lemma cubicThetaRowRadius_power {c : Eisenstein} (hc : c ≠ 0)
    {p : ℂ × ℝ} (hp : 0 < p.2) (d : Eisenstein) (σ : ℝ) :
    (cubicThetaRowRadius c p d)^(-σ) = (norm c/p.2)^σ*
      (p.2/(Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2))^σ := by
  have hN := norm_pos_of_ne_zero hc
  have hR := cubicThetaRowRadius_pos c d hp
  rw [← cubicThetaRowRadius_scale hc]
  rw [← Real.mul_rpow (div_pos hN hp).le (div_pos hp (mul_pos hN hR)).le]
  have he : (norm c/p.2)*(p.2/(norm c*cubicThetaRowRadius c p d)) =
      (cubicThetaRowRadius c p d)⁻¹ := by field_simp
  rw [he, Real.inv_rpow hR.le, Real.rpow_neg hR.le]

theorem cubicThetaRowRadius_summable {c : Eisenstein} (hc : (3:Eisenstein) ∣ c)
    (hc0 : c ≠ 0) {p : ℂ × ℝ} (hp : 0 < p.2) {s : ℂ} (hs : 2 < s.re) :
    Summable (fun d : Eisenstein => ‖cubicThetaEisensteinWeight c d‖*
      (cubicThetaRowRadius c p d)^(-s.re)) := by
  have hr := ((cubicThetaEisensteinGrid_summable hp hs).norm).comp_injective
    (show Function.Injective (fun d : Eisenstein => (c,d)) from fun _ _ he => (Prod.mk.inj he).2)
  have hi := hr.mul_left ((norm c/p.2)^s.re)
  apply hi.congr
  intro d
  dsimp only [Function.comp_apply]
  have hpos : 0 < p.2/(Complex.normSq ((c:ℂ)*p.1+d)+norm c*p.2^2) := by
    rw [← cubicThetaRowRadius_scale hc0]
    exact div_pos hp (mul_pos (norm_pos_of_ne_zero hc0) (cubicThetaRowRadius_pos c d hp))
  rw [cubicThetaEisensteinGridTerm_row hc, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos,
    cubicThetaRowRadius_power hc0 hp]
  ring

end CubicFirstMoment

end

end OAI

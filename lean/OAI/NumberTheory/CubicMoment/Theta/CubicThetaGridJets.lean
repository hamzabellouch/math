import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateJets

namespace OAI

/-! Relative bounds for all actual grid summands, with the zero row and
the inadmissible-pair extension included. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaHeightPower_first_norm (s : ℂ) {v : ℝ} (hv : 0<v) :
    ‖deriv (fun t : ℝ => (t:ℂ)^s) v‖=‖(v:ℂ)^s‖*(‖s‖/v) := by
  rw [cubicThetaHeightPower_deriv s hv,
    Complex.cpow_sub s 1 (Complex.ofReal_ne_zero.mpr hv.ne'),Complex.cpow_one]
  simp only [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  ring

lemma cubicThetaHeightPower_second_norm (s : ℂ) {v : ℝ} (hv : 0<v) :
    ‖deriv (deriv (fun t : ℝ => (t:ℂ)^s)) v‖=‖(v:ℂ)^s‖*(‖s*(s-1)‖/v^2) := by
  rw [cubicThetaHeightPower_second_deriv s hv,
    Complex.cpow_sub s 2 (Complex.ofReal_ne_zero.mpr hv.ne')]
  norm_num only [Complex.cpow_ofNat]
  simp only [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  ring

lemma cubicThetaHeightPower_jetBound (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateJetBound (fun _ _ t => (t:ℂ)^s) s x y v := by
  have hn := cubicThetaJetConstants_nonneg s
  intro k
  cases k with
  | x =>
    simp only [cubicThetaAxisFunction,cubicThetaCoordinateCenter,deriv_const',deriv_const,norm_zero]
    exact ⟨mul_nonneg (_root_.norm_nonneg _) (div_nonneg hn.1 hv.le),
      mul_nonneg (_root_.norm_nonneg _) (div_nonneg hn.2 (sq_nonneg _))⟩
  | y =>
    simp only [cubicThetaAxisFunction,cubicThetaCoordinateCenter,deriv_const',deriv_const,norm_zero]
    exact ⟨mul_nonneg (_root_.norm_nonneg _) (div_nonneg hn.1 hv.le),
      mul_nonneg (_root_.norm_nonneg _) (div_nonneg hn.2 (sq_nonneg _))⟩
  | height =>
    change ‖deriv (fun t : ℝ => (t:ℂ)^s) v‖ ≤ _ ∧
      ‖deriv (deriv (fun t : ℝ => (t:ℂ)^s)) v‖ ≤ _
    rw [cubicThetaHeightPower_first_norm s hv,cubicThetaHeightPower_second_norm s hv]
    constructor
    · apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      apply div_le_div_of_nonneg_right _ hv.le
      unfold cubicThetaFirstJetConstant
      linarith [_root_.norm_nonneg s]
    · apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      apply div_le_div_of_nonneg_right _ (sq_nonneg v)
      unfold cubicThetaSecondJetConstant
      have hpos : 0 ≤ 4*‖s‖*‖s+1‖ := by positivity
      linarith [_root_.norm_nonneg s,_root_.norm_nonneg (4*s^2+2*s)]

lemma cubicThetaZero_jetBound (s : ℂ) (x y v : ℝ) :
    CubicThetaCoordinateJetBound (fun _ _ _ => (0:ℂ)) s x y v := by
  intro k
  cases k <;> simp [cubicThetaAxisFunction,cubicThetaCoordinateCenter]

theorem cubicThetaEisensteinGrid_jetBound (c d : Eisenstein) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateJetBound
      (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s)
      s x y v := by
  by_cases hc0 : c=0
  · subst c
    simp only [cubicThetaEisensteinGridTerm_zero,cubicThetaCartesianPoint]
    by_cases hd : d=1
    · simp only [ite_eq_left hd]
      exact cubicThetaHeightPower_jetBound s x y hv
    · simp only [ite_eq_right hd]
      exact cubicThetaZero_jetBound s x y v
  · by_cases hc : (3:Eisenstein)∣c
    · exact cubicThetaCoordinateJetBound_congr
        (fun a b t ht => cubicThetaEisensteinGridTerm_cartesian hc hc0 d s a b ht) hv
        (cubicThetaCoordinateJetBound_translate
          (cubicThetaEisensteinWeight c d*(norm c:ℂ)^(-s))
          ((d:ℂ)/(c:ℂ)).re ((d:ℂ)/(c:ℂ)).im x y v
          (cubicThetaCartesian_jetBound s _ _ hv))
    · have he : (fun a b t => cubicThetaEisensteinGridTerm (c,d) (cubicThetaCartesianPoint a b t) s)=
          (fun _ _ _ => (0:ℂ)) := by
        funext a b t
        simp [cubicThetaEisensteinGridTerm,cubicThetaAdmissiblePair,hc]
      rw [he]
      exact cubicThetaZero_jetBound s x y v

end CubicFirstMoment

end

end OAI

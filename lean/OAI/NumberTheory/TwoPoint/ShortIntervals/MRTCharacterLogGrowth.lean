import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterZeroTerms

namespace OAI

/-! One absolute constant in the nonprincipal disk bounds, with all
modulus and height dependence kept in log(q*(abs(t)+2)). -/

namespace TwoPointCorrelations

noncomputable def mrtCharacterHeight (q : ℕ) (t : ℝ) : ℝ :=
  Real.log ((q:ℝ)*(|t|+2))

lemma mrt_character_height_split (q : ℕ) [NeZero q] (t : ℝ) :
    mrtCharacterHeight q t=Real.log (q:ℝ)+Real.log (|t|+2) := by
  exact Real.log_mul (by exact_mod_cast NeZero.ne q) (by positivity)

lemma mrt_character_height_ge (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (|t|+2) ≤ mrtCharacterHeight q t := by
  rw [mrt_character_height_split]
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  linarith [Real.log_nonneg hq]

lemma mrt_character_height_pos (q : ℕ) [NeZero q] (t : ℝ) :
    0 < mrtCharacterHeight q t :=
  (Real.log_pos (by linarith [abs_nonneg t] : 1 < |t|+2)).trans_le
    (mrt_character_height_ge q t)

lemma mrt_character_log_modulus_le_height (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (q:ℝ) ≤ mrtCharacterHeight q t := by
  rw [mrt_character_height_split]
  linarith [Real.log_nonneg (show 1 ≤ |t|+2 by linarith [abs_nonneg t])]

lemma mrt_character_height_double (q : ℕ) [NeZero q] (t : ℝ) :
    mrtCharacterHeight q (2*t) ≤ 2*mrtCharacterHeight q t := by
  have hq : 0 ≤ Real.log (q:ℝ) :=
    Real.log_nonneg (by exact_mod_cast NeZero.pos q)
  have hd : Real.log (|2*t|+2) ≤ 2*Real.log (|t|+2) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc
      _  ≤  Real.log ((|t|+2)^2) := by
        apply Real.log_le_log (by positivity)
        nlinarith [abs_nonneg t,sq_nonneg (|t|)]
      _ = _ := by rw [Real.log_pow]; norm_num
  rw [mrt_character_height_split,mrt_character_height_split]
  linarith

lemma mrtCharacterLogDerivativeConstant_pos : 0 < mrtCharacterLogDerivativeConstant := by
  have hl : 0 < Real.log ((15/16:ℝ)/(7/8)) := Real.log_pos (by norm_num)
  unfold mrtCharacterLogDerivativeConstant
  positivity

lemma mrt_character_log_disk_growth (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log ((2*q:ℝ)*mrtCharacterInverseConstant*(|t|+4)) ≤
      (Real.log (4*mrtCharacterInverseConstant)/Real.log 2+1)*mrtCharacterHeight q t := by
  have hK : 1 ≤ mrtCharacterInverseConstant := by
    unfold mrtCharacterInverseConstant
    exact le_add_of_nonneg_right (tsum_nonneg (fun _ => norm_nonneg _))
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hA : 0 < 4*mrtCharacterInverseConstant := by positivity
  have hlogA : 0 ≤ Real.log (4*mrtCharacterInverseConstant) :=
    Real.log_nonneg (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : Real.log 2 ≤ mrtCharacterHeight q t :=
    (Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])).trans
      (mrt_character_height_ge q t)
  have hr : Real.log (4*mrtCharacterInverseConstant) ≤
      (Real.log (4*mrtCharacterInverseConstant)/Real.log 2)*mrtCharacterHeight q t := by
    calc
      _ = (Real.log (4*mrtCharacterInverseConstant)/Real.log 2)*Real.log 2 :=
        (div_mul_cancel₀ _ hlog2.ne').symm
      _  ≤  _ := mul_le_mul_of_nonneg_left hH (div_nonneg hlogA hlog2.le)
  have hc : (2*q:ℝ)*mrtCharacterInverseConstant*(|t|+4) ≤
      (4*mrtCharacterInverseConstant)*((q:ℝ)*(|t|+2)) := by
    calc
      _ = ((q:ℝ)*mrtCharacterInverseConstant)*(2*(|t|+4)) := by ring
      _  ≤  ((q:ℝ)*mrtCharacterInverseConstant)*(4*(|t|+2)) :=
        mul_le_mul_of_nonneg_left (by linarith [abs_nonneg t]) (by positivity)
      _ = _ := by ring
  calc
    _  ≤  Real.log ((4*mrtCharacterInverseConstant)*((q:ℝ)*(|t|+2))) :=
      Real.log_le_log (by positivity) hc
    _ = Real.log (4*mrtCharacterInverseConstant)+mrtCharacterHeight q t :=
      Real.log_mul hA.ne' (by positivity)
    _  ≤  _ := by nlinarith

theorem mrt_character_logderiv_growth_constant : ∃ C : ℝ, 0 < C ∧
    ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 →
    ∀ t σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ)+Complex.I*(t:ℂ))/
        DirichletCharacter.LFunction χ ((σ:ℂ)+Complex.I*(t:ℂ))).re ≤
          C*mrtCharacterHeight q t ∧
      ∀ β : ℝ, 3/4 ≤ β → β ≤ 1 →
        DirichletCharacter.LFunction χ ((β:ℂ)+Complex.I*(t:ℂ))=0 →
        (-deriv (DirichletCharacter.LFunction χ) ((σ:ℂ)+Complex.I*(t:ℂ))/
          DirichletCharacter.LFunction χ ((σ:ℂ)+Complex.I*(t:ℂ))).re ≤
            C*mrtCharacterHeight q t-1/(σ-β) := by
  let C := (2/3:ℝ)*mrtCharacterLogDerivativeConstant*
    (Real.log (4*mrtCharacterInverseConstant)/Real.log 2+1)
  have hC : 0 < C := by
    have hD := mrtCharacterLogDerivativeConstant_pos
    have hK := mrtCharacterInverseConstant_pos
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hK1 : 1 ≤ mrtCharacterInverseConstant := by
      unfold mrtCharacterInverseConstant
      exact le_add_of_nonneg_right (tsum_nonneg (fun _ => norm_nonneg _))
    have hlogK : 0 ≤ Real.log (4*mrtCharacterInverseConstant) :=
      Real.log_nonneg (by linarith)
    dsimp only [C]
    positivity
  refine ⟨C,hC,?_⟩
  intro q _ χ hχ t σ hσ hσ2
  have hE : (2/3:ℝ)*mrtCharacterLogDerivativeConstant*
      Real.log ((2*q:ℝ)*mrtCharacterInverseConstant*(|t|+4)) ≤ C*mrtCharacterHeight q t := by
    dsimp only [C]
    calc
      _  ≤  ((2/3:ℝ)*mrtCharacterLogDerivativeConstant)*
          ((Real.log (4*mrtCharacterInverseConstant)/Real.log 2+1)*mrtCharacterHeight q t) :=
        mul_le_mul_of_nonneg_left (mrt_character_log_disk_growth q t)
          (mul_nonneg (by norm_num) mrtCharacterLogDerivativeConstant_pos.le)
      _ = _ := by ring
  refine ⟨(mrtCharacter_neg_logderiv_re_le χ hχ t hσ hσ2).trans hE,?_⟩
  intro β hβ hβ1 hzero
  exact (mrtCharacter_neg_logderiv_re_le_of_zero χ hχ t hσ hσ2 hβ hβ1 hzero).trans
    (sub_le_sub_right hE _)

end TwoPointCorrelations

end OAI

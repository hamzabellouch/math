import OAI.NumberTheory.CubicMoment.Estimates.PrincipalZetaLogDerivative

namespace OAI

/-! The numerical contradiction in the de la Vallée Poussin argument,
at the explicit displacement 1/(4E). -/
noncomputable section
namespace CubicFirstMoment

lemma hecke_zero_free_numerical {E e : ℝ} (hE : 0 < E)
    (he0 : 0 ≤ e) (he : e ≤ 1/(32*E)) :
    3/(1/(4*E))-4/(1/(4*E)+e)+E < 0 := by
  let d : ℝ := 1/(4*E)
  have hd : 0 < d := by dsimp [d]; positivity
  have hde : 0 < d+e := add_pos_of_pos_of_nonneg hd he0
  have he' : e ≤ d/8 := by
    convert he using 1
    dsimp [d]
    ring
  have hA : 0 ≤ 3/d+E := by positivity
  have hAd : (3/d+E)*d=13/4 := by
    dsimp [d]
    field_simp
    ring
  have hprod := mul_le_mul_of_nonneg_left he' hA
  have hprod' : (3/d+E)*(d+e) < 4 := by
    calc
      (3/d+E)*(d+e)=(3/d+E)*d+(3/d+E)*e := mul_add _ _ _
      _ ≤ (3/d+E)*d+(3/d+E)*(d/8) := by linarith
      _ = 117/32 := by simp only [←mul_div_assoc,hAd]; norm_num
      _ < 4 := by norm_num
  have hineq : 3/d+E < 4/(d+e) := (lt_div_iff₀ hde).mpr hprod'
  change 3/d-4/(d+e)+E < 0
  linarith

end CubicFirstMoment

end

end OAI

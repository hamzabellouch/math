import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNonzeroHeat
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRowGaussBounds

namespace OAI

/-! Arbitrary inverse-frequency decay of the nonzero heat modes.
The order is chosen after the spectral parameter, without restricting
the latter to its initial half-plane. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicTheta_inverse_heat_power_bound {A t : ℝ} (hA : 0<A) (ht : 0<t) (k : ℕ) :
    Real.exp (-A/t)≤((k.factorial:ℝ)/A^k)*t^k := by
  have h := power_exp_bound (by norm_num : (0:ℝ)<1) k (A/t) (div_pos hA ht).le
  simp only [one_pow,div_one,neg_one_mul] at h
  rw [div_pow,div_mul_eq_mul_div] at h
  have hh := (div_le_iff₀ (pow_pos ht k)).mp h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos hA k)).mpr
  simpa only [mul_comm,neg_div] using hh

lemma cubicThetaNonzeroHeat_integrable {v A : ℝ} (hv : 0<v) (hA : 0<A) (s : ℂ) :
    IntegrableOn (cubicThetaDualHeat v s A) (Ioi 0) := by
  have h := cubicThetaDoubleHeat_mellinConvergent hv hA (s-1)
  change IntegrableOn (fun t : ℝ => (t:ℂ)^(s-2)*(Real.exp (-v^2*t-A/t):ℂ)) (Ioi 0)
  simpa only [MellinConvergent,smul_eq_mul,cubicThetaDoubleHeat,
    show s-1-1=s-2 by ring] using h

lemma cubicThetaNonzeroHeat_norm_mass_power {v A : ℝ} (hv : 0<v) (hA : 0<A)
    (s : ℂ) (k : ℕ) (hk : 0<s.re+(k:ℝ)-1) :
    (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s A t‖)≤
      ((k.factorial:ℝ)/A^k)*
        (Real.Gamma (s.re+(k:ℝ)-1)*(v^2)^(-(s.re+(k:ℝ)-1))) := by
  have hi := (integrable_laplace_rpow hk (sq_pos_of_pos hv)).const_mul
    ((k.factorial:ℝ)/A^k)
  calc
    _ ≤ ∫ t in Ioi (0:ℝ), ((k.factorial:ℝ)/A^k)*
        (t^((s.re+(k:ℝ)-1)-1)*Real.exp (-v^2*t)) := by
      apply integral_mono_ae (cubicThetaNonzeroHeat_integrable hv hA s).norm hi
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [cubicThetaDualHeat_norm v s A ht]
      calc
        _ ≤ t^(s.re-2)*Real.exp (-v^2*t)*(((k.factorial:ℝ)/A^k)*t^k) :=
          mul_le_mul_of_nonneg_left (cubicTheta_inverse_heat_power_bound hA ht k)
            (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _))
        _ = _ := by
          have he : t^(s.re-2)*t^k=t^((s.re+(k:ℝ)-1)-1) := by
            rw [←Real.rpow_natCast,←Real.rpow_add ht]
            congr 1
            ring
          calc
            _ = ((k.factorial:ℝ)/A^k)*(t^(s.re-2)*t^k)*Real.exp (-v^2*t) := by ring
            _ = _ := by rw [he]; ring
    _ = _ := by rw [integral_const_mul,laplace_rpow hk (sq_pos_of_pos hv)]

theorem cubicThetaNonzeroHeat_mass_summable {v : ℝ} (hv : 0<v) (s : ℂ) :
    Summable (fun h : Eisenstein => if h=0 then 0 else
      ∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat v s (cubicThetaRowHeatScale h) t‖) := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (2:ℝ) (2-s.re))
  have hk2 : 1<(k:ℝ) := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hk)
  have hks : 0<s.re+(k:ℝ)-1 := by
    have := (le_max_right (2:ℝ) (2-s.re)).trans_lt hk
    linarith
  let b : ℝ := 4*Real.pi^2/27
  have hb : 0<b := by dsimp [b]; positivity
  let J : ℝ := Real.Gamma (s.re+(k:ℝ)-1)*(v^2)^(-(s.re+(k:ℝ)-1))
  let K : ℝ := ((k.factorial:ℝ)/b^k)*J
  have hK : 0≤K := by
    dsimp [K,J]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (pow_pos hb k).le)
      (mul_nonneg (Real.Gamma_pos_of_pos hks).le (Real.rpow_nonneg (sq_nonneg _) _))
  apply ((summable_eisenstein_norm_rpow hk2).mul_left K).of_nonneg_of_le
  · intro h
    split_ifs
    · exact le_rfl
    · exact integral_nonneg (fun _ => _root_.norm_nonneg _)
  · intro h
    by_cases hh : h=0
    · rw [ite_eq_left hh]
      exact mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [ite_eq_right hh]
      apply (cubicThetaNonzeroHeat_norm_mass_power hv (cubicThetaRowHeatScale_pos hh) s k hks).trans_eq
      rw [cubicThetaRowHeatScale_eq,show 4*Real.pi^2/27=b from rfl,mul_pow,
        Real.rpow_neg (norm_nonneg _),Real.rpow_natCast]
      dsimp only [K,J]
      ring

end CubicFirstMoment

end

end OAI

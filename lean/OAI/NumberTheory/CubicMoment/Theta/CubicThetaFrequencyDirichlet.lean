import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierRemainder

namespace OAI

/-! The actual nonzero Fourier Dirichlet coefficients and their common
majorant on Re(s)>2. This permits reordering the two lattice sums. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaFrequencyTerm (s : ℂ) (h c : Eisenstein) : ℂ :=
  if (3:Eisenstein)∣c ∧ c≠0 then
    cubicThetaEisensteinGaussCoefficient c h*(norm c:ℂ)^(-s) else 0

def cubicThetaFrequencyDirichlet (h : Eisenstein) (s : ℂ) : ℂ :=
  ∑' c : Eisenstein, cubicThetaFrequencyTerm s h c

lemma cubicThetaEisensteinGaussCoefficient_norm_real {c : Eisenstein} (hc : c≠0)
    (h : Eisenstein) : ‖cubicThetaEisensteinGaussCoefficient c h‖≤9*norm c := by
  have hb := cubicThetaEisensteinGaussCoefficient_norm hc h
  rw [residues_card (mul_ne_zero (by norm_num) hc),normNat_cast] at hb
  have h3 : norm (3:Eisenstein)=9 := by
    change Complex.normSq (3:ℂ)=9
    norm_num
  simpa only [norm_mul_eq,h3] using hb

lemma cubicThetaFrequencyTerm_bound {s : ℂ} (_hs : 2<s.re) (h c : Eisenstein) :
    ‖cubicThetaFrequencyTerm s h c‖≤9*(norm c)^(-(s.re-1)) := by
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · rw [cubicThetaFrequencyTerm,ite_eq_left hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_of_ne_zero hc.2)]
    simp only [Complex.neg_re]
    calc
      _ ≤ (9*norm c)*(norm c)^(-s.re) :=
        mul_le_mul_of_nonneg_right (cubicThetaEisensteinGaussCoefficient_norm_real hc.2 h)
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := by
        have he : norm c*(norm c)^(-s.re)=(norm c)^(-(s.re-1)) := by
          calc
            _ = (norm c)^(1:ℝ)*(norm c)^(-s.re) := by rw [Real.rpow_one]
            _ = _ := by
              rw [←Real.rpow_add (norm_pos_of_ne_zero hc.2)]
              congr 1
              ring
        rw [mul_assoc,he]
  · simp only [cubicThetaFrequencyTerm,ite_eq_right hc,norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)

lemma cubicThetaFrequencyTerm_norm_summable {s : ℂ} (hs : 2<s.re) (h : Eisenstein) :
    Summable (fun c => ‖cubicThetaFrequencyTerm s h c‖) := by
  exact ((summable_eisenstein_norm_rpow (show 1<s.re-1 by linarith)).mul_left 9).of_nonneg_of_le
    (fun _ => _root_.norm_nonneg _) (cubicThetaFrequencyTerm_bound hs h)

lemma cubicThetaFrequencyDirichlet_zero (s : ℂ) :
    cubicThetaFrequencyDirichlet 0 s=cubicThetaConstantDirichlet s := rfl

lemma cubicThetaFrequency_heat_norm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun ch : Eisenstein × Eisenstein =>
      ‖cubicThetaFrequencyTerm s ch.2 ch.1*
        (Real.fourierChar (tracePair p.1 (cubicThetaRowFrequency ch.2)):ℂ)*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale ch.2) t)‖) := by
  have hc := (summable_eisenstein_norm_rpow (show 1<s.re-1 by linarith)).mul_left 9
  have hh := cubicThetaDualHeat_mass_summable hp (show 1<s.re by linarith)
  have hprod : Summable (fun ch : Eisenstein × Eisenstein =>
      (9*(norm ch.1)^(-(s.re-1)))*
        (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat p.2 s (cubicThetaRowHeatScale ch.2) t‖)) :=
    summable_mul_of_summable_norm hc.norm hh.norm
  apply hprod.of_nonneg_of_le (fun _ => _root_.norm_nonneg _)
  intro ch
  rw [norm_mul,norm_mul,Circle.norm_coe,mul_one]
  exact mul_le_mul (cubicThetaFrequencyTerm_bound hs ch.2 ch.1)
    (norm_integral_le_integral_norm _) (_root_.norm_nonneg _)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _))

end CubicFirstMoment

end

end OAI

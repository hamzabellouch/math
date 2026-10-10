import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInvertedFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRemainder

namespace OAI

/-! Absolute arithmetic and heat majorants for collecting the actual
inverted Fourier coefficients on their half-plane of convergence. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaInvertedFrequencyTerm (s : ℂ) (h c : Eisenstein) : ℂ :=
  if primary c then cubicThetaInvertedGaussCoefficient c h*(norm c:ℂ)^(-s) else 0

lemma cubicThetaInvertedFrequencyDirichlet_tsum (h : Eisenstein) (s : ℂ) :
    cubicThetaInvertedFrequencyDirichlet h s=
      ∑' c : Eisenstein, cubicThetaInvertedFrequencyTerm s h c := by
  have hsup : Function.support (cubicThetaInvertedFrequencyTerm s h) ⊆ {c | primary c} := by
    intro c hc
    by_contra hn
    change ¬primary c at hn
    exact hc (by simp [cubicThetaInvertedFrequencyTerm,hn])
  calc
    _ = ∑' c : CubicThetaPrimaryPart, cubicThetaInvertedFrequencyTerm s h c.val := by
      apply tsum_congr
      intro c
      simp only [cubicThetaInvertedFrequencyTerm,ite_eq_left c.property]
    _ = _ := tsum_subtype_eq_of_support_subset hsup

lemma cubicThetaInvertedFrequencyDirichlet_zero (s : ℂ) :
    cubicThetaInvertedFrequencyDirichlet 0 s=cubicThetaInvertedConstantDirichlet s := by
  rw [cubicThetaInvertedFrequencyDirichlet_tsum]
  unfold cubicThetaInvertedConstantDirichlet
  apply tsum_congr
  intro c
  simp only [cubicThetaInvertedFrequencyTerm,cubicThetaInvertedConstantWeight,
    cubicThetaInvertedGaussCoefficient_zero]

lemma cubicThetaInvertedGaussCoefficient_norm_real {c : Eisenstein} (hc : primary c)
    (h : Eisenstein) : ‖cubicThetaInvertedGaussCoefficient c h‖≤norm c := by
  have ht := cubicThetaInvertedGaussCoefficient_norm hc h
  rwa [residues_card (primary_ne_zero hc),normNat_cast] at ht

lemma cubicThetaInvertedFrequencyTerm_bound (s : ℂ) (h c : Eisenstein) :
    ‖cubicThetaInvertedFrequencyTerm s h c‖≤9*(norm c)^(-(s.re-1)) := by
  by_cases hc : primary c
  · have hc0 := primary_ne_zero hc
    rw [cubicThetaInvertedFrequencyTerm,ite_eq_left hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_of_ne_zero hc0)]
    simp only [Complex.neg_re]
    have hg : ‖cubicThetaInvertedGaussCoefficient c h‖≤9*norm c := by
      have ht := cubicThetaInvertedGaussCoefficient_norm_real hc h
      linarith [norm_nonneg c]
    calc
      _ ≤ (9*norm c)*(norm c)^(-s.re) :=
        mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg (norm_nonneg c) _)
      _ = _ := by
        have he : norm c*(norm c)^(-s.re)=(norm c)^(-(s.re-1)) := by
          calc
            _ = (norm c)^(1:ℝ)*(norm c)^(-s.re) := by rw [Real.rpow_one]
            _ = _ := by
              rw [←Real.rpow_add (norm_pos_of_ne_zero hc0)]
              congr 1
              ring
        rw [mul_assoc,he]
  · simp only [cubicThetaInvertedFrequencyTerm,ite_eq_right hc,norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)

lemma cubicThetaInvertedFrequencyTerm_norm_summable {s : ℂ} (hs : 2<s.re) (h : Eisenstein) :
    Summable (fun c => ‖cubicThetaInvertedFrequencyTerm s h c‖) :=
  ((summable_eisenstein_norm_rpow (show 1<s.re-1 by linarith)).mul_left 9).of_nonneg_of_le
    (fun _ => _root_.norm_nonneg _) (cubicThetaInvertedFrequencyTerm_bound s h)

lemma cubicThetaInvertedFrequency_heat_norm_summable {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun ch : Eisenstein × Eisenstein =>
      ‖cubicThetaInvertedFrequencyTerm s ch.2 ch.1*
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
  exact mul_le_mul (cubicThetaInvertedFrequencyTerm_bound s ch.2 ch.1)
    (norm_integral_le_integral_norm _) (_root_.norm_nonneg _)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _))

end CubicFirstMoment

end

end OAI

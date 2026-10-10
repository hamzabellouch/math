import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedRowFourier
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaShiftedGaussExplicit
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRemainder

namespace OAI

/-! Absolute arithmetic and heat majorants for collecting the actual
inverted Fourier coefficients on their half-plane of convergence. -/
noncomputable section
open MeasureTheory Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaShiftedFrequencyTerm (b : Eisenstein) (s : ℂ) (h c : Eisenstein) : ℂ :=
  if primary c then cubicThetaShiftedGaussCoefficient b c h*(norm c:ℂ)^(-s) else 0

lemma cubicThetaShiftedFrequencyDirichlet_tsum (b h : Eisenstein) (s : ℂ) :
    cubicThetaShiftedFrequencyDirichlet b h s=
      ∑' c : Eisenstein, cubicThetaShiftedFrequencyTerm b s h c := by
  have hsup : Function.support (cubicThetaShiftedFrequencyTerm b s h) ⊆ {c | primary c} := by
    intro c hc
    by_contra hn
    change ¬primary c at hn
    exact hc (by simp [cubicThetaShiftedFrequencyTerm,hn])
  calc
    _ = ∑' c : CubicThetaPrimaryPart, cubicThetaShiftedFrequencyTerm b s h c.val := by
      apply tsum_congr
      intro c
      simp only [cubicThetaShiftedFrequencyTerm,ite_eq_left c.property]
    _ = _ := tsum_subtype_eq_of_support_subset hsup

lemma cubicThetaShiftedGaussCoefficient_norm_real {c : Eisenstein} (hc : primary c)
    (b h : Eisenstein) : ‖cubicThetaShiftedGaussCoefficient b c h‖≤9*norm c := by
  have h3c : (3*c:Eisenstein)≠0 := mul_ne_zero (by norm_num) (primary_ne_zero hc)
  have ht := cubicThetaShiftedGaussCoefficient_norm hc b h
  rw [residues_card h3c,normNat_cast,norm_mul_eq] at ht
  have h3 : norm (3:Eisenstein)=9 := by change Complex.normSq (3:ℂ)=9; norm_num
  rwa [h3] at ht

lemma cubicThetaShiftedFrequencyTerm_bound (b : Eisenstein) (s : ℂ) (h c : Eisenstein) :
    ‖cubicThetaShiftedFrequencyTerm b s h c‖≤9*(norm c)^(-(s.re-1)) := by
  by_cases hc : primary c
  · have hc0 := primary_ne_zero hc
    rw [cubicThetaShiftedFrequencyTerm,ite_eq_left hc,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (norm_pos_of_ne_zero hc0)]
    simp only [Complex.neg_re]
    have hg : ‖cubicThetaShiftedGaussCoefficient b c h‖≤9*norm c := by
      exact cubicThetaShiftedGaussCoefficient_norm_real hc b h
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
  · simp only [cubicThetaShiftedFrequencyTerm,ite_eq_right hc,norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)

lemma cubicThetaShiftedFrequencyTerm_norm_summable (b : Eisenstein) {s : ℂ} (hs : 2<s.re) (h : Eisenstein) :
    Summable (fun c => ‖cubicThetaShiftedFrequencyTerm b s h c‖) :=
  ((summable_eisenstein_norm_rpow (show 1<s.re-1 by linarith)).mul_left 9).of_nonneg_of_le
    (fun _ => _root_.norm_nonneg _) (cubicThetaShiftedFrequencyTerm_bound b s h)

lemma cubicThetaShiftedFrequency_heat_norm_summable (b : Eisenstein) {p : ℂ × ℝ} (hp : 0<p.2)
    {s : ℂ} (hs : 2<s.re) :
    Summable (fun ch : Eisenstein × Eisenstein =>
      ‖cubicThetaShiftedFrequencyTerm b s ch.2 ch.1*
        (Real.fourierChar (tracePair p.1 (cubicThetaShiftedRowFrequency ch.2)):ℂ)*
        (∫ t in Ioi (0:ℝ), cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale ch.2) t)‖) := by
  have hc := (summable_eisenstein_norm_rpow (show 1<s.re-1 by linarith)).mul_left 9
  have hh := cubicThetaShiftedDualHeat_mass_summable hp (show 1<s.re by linarith)
  have hprod : Summable (fun ch : Eisenstein × Eisenstein =>
      (9*(norm ch.1)^(-(s.re-1)))*
        (∫ t in Ioi (0:ℝ), ‖cubicThetaDualHeat p.2 s (cubicThetaShiftedRowHeatScale ch.2) t‖)) :=
    summable_mul_of_summable_norm hc.norm hh.norm
  apply hprod.of_nonneg_of_le (fun _ => _root_.norm_nonneg _)
  intro ch
  rw [norm_mul,norm_mul,Circle.norm_coe,mul_one]
  exact mul_le_mul (cubicThetaShiftedFrequencyTerm_bound b s ch.2 ch.1)
    (norm_integral_le_integral_norm _) (_root_.norm_nonneg _)
    (mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _))

end CubicFirstMoment

end

end OAI

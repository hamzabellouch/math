import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.CutoffAsymptotics
import OAI.Analysis.HardSphere.Allocation.CertificateMeasurable

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Bridge
open Wiener GaussianPacking PathCutoff

lemma scaleMoment_two {t r : ℝ} (ht : 0 ≤ t) (w : Time) :
    scaleMoment 2 t r 0 w = 432*t*(w:ℝ)/r^2*normPowerMean 2 := by
  have hw : 0 ≤ (w:ℝ) := w.property.1
  unfold scaleMoment
  simp only [show ((0:Time):ℝ)=0 from rfl,sub_zero,mul_one,div_pow]
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2*t*(w:ℝ))]
  ring

lemma source_window_moment {D b t : ℝ} (hD : 0 < D) (ht : 0 ≤ t)
    (w : Time) (hw : t*(w:ℝ)=D⁻¹) :
    scaleMoment 2 t (b*D^(-(1/3):ℝ)/8) 0 w =
      27648*b⁻¹^2*D^(-(1/3):ℝ)*normPowerMean 2 := by
  rw [scaleMoment_two ht]
  have hp : (D^(-(1/3):ℝ))^2=D^(-(2/3):ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hD.le]
    norm_num
  have he : D⁻¹/(D^(-(1/3):ℝ))^2=D^(-(1/3):ℝ) := by
    rw [hp,←Real.rpow_neg_one,←Real.rpow_sub hD]
    norm_num
  calc
    _ = 27648*b⁻¹^2*(D⁻¹/(D^(-(1/3):ℝ))^2)*normPowerMean 2 := by
      rw [div_pow,mul_pow]
      simp only [div_eq_mul_inv,mul_inv,inv_pow]
      rw [show 432*t*(w:ℝ)=432*D⁻¹ by rw [mul_assoc,hw]]
      ring
    _ = _ := by rw [he]

lemma trialCutoff_mono_constants {L : Length} {n : ℕ} {r R C R' C' S : ℝ}
    {w : Time} {v : Point} {f : C(Time,Point)} (hR : R ≤ R') (hC : C ≤ C')
    (h : TrialCutoff L n r R C w S v f) : TrialCutoff L n r R' C' w S v f :=
  ⟨Groups.regular_mono_constants hR hC h.1,h.2⟩

def scalarTrialRemainder (Cn M c a b D : ℝ) : ℝ :=
  Cn*D^2*(3*M)*Real.exp (-(c/46656)*D^(1/6:ℝ))+
    Real.exp (-(a/8)*D)+3*M*Real.exp (-c*D^(1/6:ℝ))+
    3981312*b⁻¹^2*D^(-(1/3):ℝ)*normPowerMean 2

lemma scalarTrialRemainder_decay (Cn M b : ℝ) {c a : ℝ}
    (hc : 0 < c) (ha : 0 < a) :
    Tendsto (scalarTrialRemainder Cn M c a b) atTop (𝓝 0) := by
  have h₁ := (stretched_exp_decay 2 (by positivity : (0:ℝ) < c/46656)
    (by norm_num : (0:ℝ) < 1/6)).const_mul (Cn*(3*M))
  have h₂ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 (a/8) (by positivity)
  have h₃ := (stretched_exp_decay 0 hc (by norm_num : (0:ℝ) < 1/6)).const_mul (3*M)
  have h₄ := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/3)).const_mul
    (3981312*b⁻¹^2*normPowerMean 2)
  convert ((h₁.add h₂).add h₃).add h₄ using 1
  · funext D
    simp only [scalarTrialRemainder,Real.rpow_two,Real.rpow_zero,one_mul]
    ring
  · ring_nf

lemma scalarTrialRemainder_nonneg {Cn M : ℝ} (hCn : 0 ≤ Cn) (hM : 0 ≤ M)
    (c a b : ℝ) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ scalarTrialRemainder Cn M c a b D := by
  have hn := normPowerMean_nonneg 2
  unfold scalarTrialRemainder
  positivity

end HardSphere.Bridge

end
end

end

end OAI

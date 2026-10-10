import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothTests
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace OAI

/-! Actual local hyperbolic energy jets: the value has weight v^(-3/2),
and each Euclidean derivative has weight v^(-1/2). Their squared norm
is the hyperbolic mass plus Dirichlet density. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

abbrev CubicThetaLocalJet := EuclideanSpace ℂ (Fin 4)

def cubicThetaLocalEnergyJet (f : ℂ × ℝ → ℂ) (y : ℂ × ℝ) : CubicThetaLocalJet :=
  WithLp.toLp 2 ![(y.2^(-3/2:ℝ)) • f y,
    (y.2^(-1/2:ℝ)) • fderiv ℝ f y (1,0),
    (y.2^(-1/2:ℝ)) • fderiv ℝ f y (Complex.I,0),
    (y.2^(-1/2:ℝ)) • fderiv ℝ f y (0,1)]

lemma cubicTheta_weighted_positive_continuous (a : ℝ) {f : ℂ × ℝ → ℂ}
    (hf : Continuous f) (hp : tsupport f ⊆ {y : ℂ × ℝ | 0<y.2}) :
    Continuous (fun y => (y.2^a) • f y) := by
  have hw : ContinuousOn (fun y : ℂ × ℝ => y.2^a) {y | 0<y.2} :=
    continuous_snd.continuousOn.rpow_const (fun y hy => Or.inl hy.ne')
  apply (hw.smul hf.continuousOn).continuous_of_tsupport_subset
    (isOpen_lt continuous_const continuous_snd)
  exact (tsupport_smul_subset_right (fun y : ℂ × ℝ => y.2^a) f).trans hp

lemma cubicThetaLocalEnergyJet_continuous {f : ℂ × ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hp : tsupport f ⊆ {y : ℂ × ℝ | 0<y.2}) :
    Continuous (cubicThetaLocalEnergyJet f) := by
  have hd (v : ℂ × ℝ) : Continuous (fun y => fderiv ℝ f y v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hs (v : ℂ × ℝ) : tsupport (fun y => fderiv ℝ f y v) ⊆ {y : ℂ × ℝ | 0<y.2} :=
    (tsupport_fderiv_apply_subset (𝕜:=ℝ) (f:=f) v).trans hp
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact cubicTheta_weighted_positive_continuous _ hf.continuous hp
  · exact cubicTheta_weighted_positive_continuous _ (hd _) (hs _)
  · exact cubicTheta_weighted_positive_continuous _ (hd _) (hs _)
  · exact cubicTheta_weighted_positive_continuous _ (hd _) (hs _)

lemma cubicThetaLocalEnergyJet_compact {f : ℂ × ℝ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (cubicThetaLocalEnergyJet f) := by
  apply hf.mono'
  intro y hy
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  have hd := fderiv_of_notMem_tsupport (𝕜:=ℝ) hn
  apply hy
  ext i
  fin_cases i <;> simp [cubicThetaLocalEnergyJet,hz,hd]

lemma cubicThetaLocalEnergyJet_memLp {f : ℂ × ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ {y : ℂ × ℝ | 0<y.2}) :
    MemLp (cubicThetaLocalEnergyJet f) 2 (volume : Measure (ℂ × ℝ)) :=
  (cubicThetaLocalEnergyJet_continuous hf hp).memLp_of_hasCompactSupport
    (cubicThetaLocalEnergyJet_compact hc)

lemma cubicThetaLocalEnergyJet_norm_sq (f : ℂ × ℝ → ℂ) {y : ℂ × ℝ} (hy : 0<y.2) :
    ‖cubicThetaLocalEnergyJet f y‖^2=‖f y‖^2/y.2^3+
      (‖fderiv ℝ f y (1,0)‖^2+‖fderiv ℝ f y (Complex.I,0)‖^2+
        ‖fderiv ℝ f y (0,1)‖^2)/y.2 := by
  have hw (a : ℝ) : (y.2^a)^2=y.2^(a*2) := (Real.rpow_mul_natCast hy.le a 2).symm
  have h₁ : (y.2^(-3/2:ℝ))^2=(y.2^3)⁻¹ := by rw [hw]; norm_num
  have h₂ : (y.2^(-1/2:ℝ))^2=y.2⁻¹ := by rw [hw]; norm_num [Real.rpow_neg_one]
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [cubicThetaLocalEnergyJet,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one,
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hy.le _),mul_pow,h₁,h₂]
  ring

end CubicFirstMoment

end

end OAI

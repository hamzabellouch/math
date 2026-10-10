import OAI.Probability.InvariantIsing.Fields.SpinPriorLabeledMoments
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorRootVariance

namespace OAI

/-! The root Gaussian variance estimate is uniform in the normalized spin
constraint. Its constant is the physical tensor coefficient norm. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal InnerProductSpace
namespace InvariantIsing

theorem spinPriorCascadeValue_root_lipschitz {N m k : ℕ} (hN : 0 < N)
    (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    let B : ℝ≥0 := ⟨(site : ℝ)*N + ∑ j, (monomial j : ℝ)*amp j^2, by positivity⟩
    LipschitzWith (NNReal.sqrt B) (fun g => spinPriorCascadeValue π eig U c I degree amp n b v
      (tensorRootMark I degree (tensorVarianceProfile I degree site monomial) g)) := by
  intro B
  have hs : (NNReal.sqrt B : ℝ)^2 = B := by exact_mod_cast NNReal.sq_sqrt B
  have hn (σ : Spin N) :
      ‖tensorRootCoefficient U I degree amp (tensorVarianceProfile I degree site monomial) σ‖ ≤
        (NNReal.sqrt B : ℝ) := by
    have hcap := tensorRootCoefficient_norm_sq_le U I degree amp site monomial σ
    change ‖tensorRootCoefficient U I degree amp (tensorVarianceProfile I degree site monomial) σ‖^2 ≤ (B : ℝ) at hcap
    nlinarith [norm_nonneg (tensorRootCoefficient U I degree amp
      (tensorVarianceProfile I degree site monomial) σ), NNReal.coe_nonneg (NNReal.sqrt B)]
  apply LipschitzWith.of_dist_le_mul
  intro g h
  rw [Real.dist_eq]
  refine (energyRecursion_lipschitz n b _ π
    (fun i _ => tensorEnergyMarkLaw_moments hN U I degree amp (v i))
    (fun i hi => (hb.1 i hi).1) _ _).trans ?_
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (dist_nonneg))).mpr
  intro σ
  simp only [Pi.sub_apply, Real.norm_eq_abs, tensorSpinBaseEnergy,
    add_sub_add_left_eq_sub, spinTensorEnergy_tensorRootMark, ← inner_sub_right]
  exact (abs_real_inner_le_norm _ _).trans
    (by simpa only [dist_eq_norm] using mul_le_mul_of_nonneg_right (hn σ) (norm_nonneg (g-h)))

theorem spinPriorCascadeValue_root_memLp_variance (hpub : GaussianLipschitzVarianceInput)
    {N m k : ℕ} (hN : 0 < N) (π : Measure (Spin N)) [IsProbabilityMeasure π]
    (eig : Fin N → ℝ) (U : Rotation N) (c : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (degree : Fin k → Fin m → ℕ) (amp : Fin k → ℝ)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → SpinTensorIndex I degree → ℝ≥0)
    (hb : CascadeExponents n b) (site : ℝ≥0) (monomial : Fin k → ℝ≥0) :
    MemLp (spinPriorCascadeValue π eig U c I degree amp n b v) 2
      (tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial) : Measure _) ∧
    variance (spinPriorCascadeValue π eig U c I degree amp n b v)
      (tensorGaussianLaw I degree (tensorVarianceProfile I degree site monomial) : Measure _) ≤
      (site : ℝ)*N + ∑ j, (monomial j : ℝ)*amp j^2 := by
  let B : ℝ≥0 := ⟨(site : ℝ)*N + ∑ j, (monomial j : ℝ)*amp j^2, by positivity⟩
  let F := fun g => spinPriorCascadeValue π eig U c I degree amp n b v
    (tensorRootMark I degree (tensorVarianceProfile I degree site monomial) g)
  have hLip : LipschitzWith (NNReal.sqrt B) F :=
    spinPriorCascadeValue_root_lipschitz hN π eig U c I degree amp n b v hb site monomial
  have hLip0 : LipschitzWith (NNReal.sqrt B) (fun g => F g-F 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro g h
    simpa only [dist_sub_right] using hLip.dist_le_mul g h
  have hL := hLip0.comp_memLp (by simp)
    (IsGaussian.memLp_two_id : MemLp id 2 (stdGaussian (TensorGaussianSpace I degree)))
  have hF : MemLp F 2 (stdGaussian (TensorGaussianSpace I degree)) := by
    convert hL.add (memLp_const (F 0)) using 1
    ext g
    simp only [Pi.add_apply, Function.comp_apply, id_eq, sub_add_cancel]
  have hm := measurable_spinPriorCascadeValue π eig U c I degree amp n b v
  have hp := tensorRootMark_measurePreserving I degree (tensorVarianceProfile I degree site monomial)
  refine ⟨?_, ?_⟩
  · rw [← hp.map_eq]
    exact (memLp_map_measure_iff hm.aestronglyMeasurable hp.aemeasurable).mpr hF
  · have hv := hpub (Fintype.card (SpinTensorIndex I degree)) (NNReal.sqrt B) F hLip
    rw [hp.variance_fun_comp hm.aemeasurable] at hv
    exact hv.trans_eq (by
      change (NNReal.sqrt B : ℝ)^2 = (B : ℝ)
      exact_mod_cast NNReal.sq_sqrt B)

end InvariantIsing

end

end OAI

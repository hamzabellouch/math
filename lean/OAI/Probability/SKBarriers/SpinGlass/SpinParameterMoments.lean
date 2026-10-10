import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinParameterRegular
import OAI.Probability.SKBarriers.Calculus.ParameterHierarchyMoment
import OAI.Probability.SKBarriers.Gaussian.BlockStein

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem spinGibbs_paramSmooth {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (c : Config N → ℝ) (s : Config N) :
    ParamSmooth (fun z : (Fin d → ℝ) × ParameterSpace d =>
      affineGibbs c (spinExponent d z.1 I) z.2 s) := by
  have h := (((paramRegular_const (c s)).add (spinExponent_paramRegular d I s)).add
    ((spinTerminal_paramRegular d I c).const_mul (-1))).expSmooth
  have he : (fun z : (Fin d → ℝ) × ParameterSpace d =>
      Real.exp ((c s+spinExponent d z.1 I s z.2)+(-1)*affineLogPartition c (spinExponent d z.1 I) z.2)) =
      (fun z : (Fin d → ℝ) × ParameterSpace d => affineGibbs c (spinExponent d z.1 I) z.2 s) := by
    funext z
    rw [neg_one_mul,← sub_eq_add_neg,affineLogPartition,Real.exp_sub,
      Real.exp_log (affinePartition_pos c (spinExponent d z.1 I) z.2)]
    rfl
  rw [he] at h
  exact h

theorem spinMoment_paramSmooth {N : ℕ} (d : ℕ) (I : Fin d → Finset (Fin N))
    (c v : Config N → ℝ) :
    ParamSmooth (fun z : (Fin d → ℝ) × ParameterSpace d =>
      affineMoment c (spinExponent d z.1 I) v z.2) := by
  exact ParamSmooth.sum Finset.univ _ (fun s _ =>
    (spinGibbs_paramSmooth d I c s).mul (paramSmooth_const (v s)))

theorem spinHierarchyMean_paramSmooth {N : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (I : Fin d → Finset (Fin N)) (v : Config N → ℝ) (j : Fin (d+1)) :
    ParamSmooth (fun z : (Fin d → ℝ) × ParameterSpace d =>
      hierarchySpinMean d m (spinExponent d z.1 I) v j z.2) := by
  exact hierarchyMomentLevel_paramSmooth d m _ _
    (spinTerminal_paramRegular d I (fun _ => 0)) (spinMoment_paramSmooth d I (fun _ => 0) v) j

theorem spinHierarchyMeanSquare_paramSmooth {N K : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (I : Fin d → Finset (Fin N)) (v : Fin K → Config N → ℝ) (j : Fin (d+1)) :
    ParamSmooth (fun z : (Fin d → ℝ) × ParameterSpace d =>
      hierarchyMeanSquare d m (spinExponent d z.1 I) v j z.2) := by
  have h := (ParamSmooth.sum Finset.univ (fun i z =>
    hierarchySpinMean d m (spinExponent d z.1 I) (v i) j z.2 *
      hierarchySpinMean d m (spinExponent d z.1 I) (v i) j z.2)
    (fun i _ => (spinHierarchyMean_paramSmooth d m I (v i) j).mul
      (spinHierarchyMean_paramSmooth d m I (v i) j))).const_mul (K : ℝ)⁻¹
  simpa only [hierarchyMeanSquare,normalizedSquare,pow_two,div_eq_mul_inv,mul_comm] using h

theorem spinHierarchyAverageMeanSquare_paramSmooth {N K : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (I : Fin d → Finset (Fin N)) (v : Fin K → Config N → ℝ) (j : Fin (d+1)) :
    ParamSmooth (fun z : (Fin d → ℝ) × ℝ => hierarchyAverage d m
      (affineLogPartition (fun _ => 0) (spinExponent d z.1 I))
      (hierarchyMeanSquare d m (spinExponent d z.1 I) v j) z.2) := by
  exact hierarchyAverage_paramSmooth d m _ _
    (spinTerminal_paramRegular d I (fun _ => 0)) (spinHierarchyMeanSquare_paramSmooth d m I v j)

theorem spinHierarchyMeanOverlap_eq {N K : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (I : Fin d → Finset (Fin N)) (v : Fin K → Config N → ℝ)
    (hv : ∀ i s, ‖v i s‖ ≤ 1) (j : Fin (d+1)) (a : Fin d → ℝ) :
    hierarchyMeanOverlap d m (spinExponent d a I) v j = hierarchyAverage d m
      (affineLogPartition (fun _ => 0) (spinExponent d a I))
      (hierarchyMeanSquare d m (spinExponent d a I) v j) 0 := by
  exact (hierarchyAverage_eq_integral d m _ (affineLogPartition_boundedDerivs _ _) _
    (hierarchyMeanSquare_continuous d m _ v hv j) (C := 1) zero_le_one
    (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hierarchyMeanSquare_bounds d m _ v hv j z).1]
      exact (hierarchyMeanSquare_bounds d m _ v hv j z).2) 0).symm

theorem parameter_contDiff_at_field {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : P × E → ℝ}
    (hf : ContDiff ℝ 2 f) (y : E) : ContDiff ℝ 2 (fun a => f (a,y)) := by
  exact hf.comp (contDiff_id.prodMk contDiff_const)

theorem spinHierarchyOverlap_contDiff {N K : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (I : Fin d → Finset (Fin N)) (v : Fin K → Config N → ℝ)
    (hv : ∀ i s, ‖v i s‖ ≤ 1) (j : Fin (d+1)) :
    ContDiff ℝ 2 (fun a : Fin d → ℝ =>
      hierarchyMeanOverlap d m (spinExponent d a I) v j) := by
  simp_rw [spinHierarchyMeanOverlap_eq d m I v hv j]
  exact parameter_contDiff_at_field (spinHierarchyAverageMeanSquare_paramSmooth d m I v j).1 (0 : ℝ)
end SK.Analytic

end
end

end

end OAI

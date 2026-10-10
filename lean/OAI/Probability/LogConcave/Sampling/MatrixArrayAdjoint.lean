import Mathlib
import OAI.Probability.LogConcave.Sampling.ComposedJetMajorant
import OAI.Probability.LogConcave.JetEstimates.JetCompactIntegral

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set Function MeasureTheory
open scoped Classical NNReal BigOperators RealInnerProductSpace
open TensorEnergy

lemma matrixArray_adjoint {d : ℕ} (A : Point d →L[ℝ] Point d) :
    matrixArray d A.adjoint=arrayRelabel (Equiv.sumComm Unit Unit) (matrixArray d A) := by
  funext c
  change inner ℝ _ (A.adjoint _)=inner ℝ _ (A _)
  rw [ContinuousLinearMap.adjoint_inner_right,real_inner_comm]
  rfl

theorem centeringKernel_iterated_split {d n : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r R T : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hR : 0<R) (hRT : R^2≤1-T^2)
    (hT0 : 0≤T) (hT1 : T<1) (y : Point d) :
    AllSplitBound (arrayTensor (iteratedFDeriv ℝ n
      (fun z => matrixArray d (centeringKernel hF x hr hl hT0 hT1 z)) y))
      (((lam:ℝ)*r)*kernelMajorant n/R^n) := by
  let : CompleteSpace (Point d →L[ℝ] Point d) := ContinuousLinearMap.instCompleteSpace
  let g : Point d × ℝ → (Unit ⊕ Unit → Fin d) → ℝ :=
    fun p => matrixArray d (steinIntegrand hF x hr hl hT0 hT1 (p.2,p.1))
  have hg : ContDiff ℝ (⊤:ℕ∞) g := (matrixArray d).contDiff.comp
    ((steinIntegrand_smooth hF x hr hlam hl hT0 hT1).comp (contDiff_snd.prodMk contDiff_fst))
  have hB : 0≤((lam:ℝ)*r)*kernelMajorant n/R^n := by
    exact div_nonneg (mul_nonneg (mul_nonneg lam.2 hr.le) (kernelMajorant_nonneg _)) (pow_nonneg hR.le _)
  have hh := compactIntegral_iterated_split (n:=n) hg (s:=Icc (0:ℝ) T) isCompact_Icc y hB
    (fun t ht => steinIntegrand_iterated_split hF x hr hlam hl hR hRT hT0 hT1 ⟨t,ht⟩ y)
  have hvol : volume.real (Icc (0:ℝ) T)=T := by
    simp only [Measure.real,Real.volume_Icc,sub_zero,ENNReal.toReal_ofReal hT0]
  rw [hvol] at hh
  have hb := hh.mono (mul_nonneg hT0 hB) (mul_le_of_le_one_left hB hT1.le)
  have hh' := AllSplitBound.array_relabel (Equiv.sumComm Unit Unit)
    (CompactIntegral.smooth_parametric hg isCompact_Icc) y hb
  have he : (fun z => matrixArray d (centeringKernel hF x hr hl hT0 hT1 z))=
      (arrayRelabel (Equiv.sumComm Unit Unit)) ∘ (fun z => ∫t in Icc (0:ℝ) T,g (z,t)) := by
    funext z
    rw [centeringKernel,matrixArray_adjoint]
    congr 1
    exact ((matrixArray d).integral_comp_comm
      (((steinIntegrand_smooth hF x hr hlam hl hT0 hT1).continuous.comp
        (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact isCompact_Icc)).symm
  rw [he]
  exact hh'
end LogConcaveSampling

end

end

end

end OAI

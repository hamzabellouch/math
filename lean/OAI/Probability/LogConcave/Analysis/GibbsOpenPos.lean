import Mathlib
import OAI.Probability.LogConcave.Sampling.PrimitiveExpectedField

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory MeasureTheory.Measure Function
open scoped Classical BigOperators RealInnerProductSpace NNReal

lemma gibbs_openPos {d : ℕ} {H : Point d → ℝ} (hH : Continuous H)
    (hi : Integrable (fun z => Real.exp (-H z))) : IsOpenPosMeasure (gibbs H) := by
  have hd : Measurable (gibbsDensity H) := (Real.continuous_exp.comp hH.neg).measurable.ennreal_ofReal
  have hp : ∀ᵐ y : Point d ∂volume, gibbsDensity H y≠0 := Filter.Eventually.of_forall
    (fun y => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
  let : IsOpenPosMeasure (volume.withDensity (gibbsDensity H)) :=
    (withDensity_absolutelyContinuous' hd.aemeasurable hp).isOpenPosMeasure
  exact isOpenPosMeasure_smul (volume.withDensity (gibbsDensity H))
    (ENNReal.inv_ne_zero.mpr (partition_ne_top_of_integrable hi))

lemma directional_adjoint_basis {d : ℕ} (A : Point d →L[ℝ] Point d)
    (u : Point d) (φ : Point d → ℝ) (y : Point d) :
    directional (A.adjoint u) φ y=∑i : Fin d,
      inner ℝ u (A (EuclideanSpace.basisFun (Fin d) ℝ i))*
        directional (EuclideanSpace.basisFun (Fin d) ℝ i) φ y := by
  rw [directional_basis_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [OrthonormalBasis.repr_apply_apply,ContinuousLinearMap.adjoint_inner_right,real_inner_comm]

theorem stein_weak_to_strong {d : ℕ} {H : Point d → ℝ}
    (hH : ContDiff ℝ 1 H) (hi : Integrable (fun z => Real.exp (-H z)))
    {K : Point d → (Point d →L[ℝ] Point d)} (hK : ContDiff ℝ 1 K)
    {m : Point d → Point d} (hm : Continuous m)
    (hw : ∀u φ,ContDiff ℝ 1 φ → HasCompactSupport φ →
      (∫y,inner ℝ u (m y)*φ y ∂gibbs H)=∫y,directional ((K y).adjoint u) φ y ∂gibbs H)
    (u : Point d) :
    tensorAdjoint H (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i y => inner ℝ u (K y (EuclideanSpace.basisFun (Fin d) ℝ i)))=
      fun y => inner ℝ u (m y) := by
  let b := EuclideanSpace.basisFun (Fin d) ℝ
  let V := fun (i : Fin d) y => inner ℝ u (K y (b i))
  have hV (i : Fin d) : ContDiff ℝ 1 (V i) :=
    contDiff_const.inner ℝ (hK.clm_apply contDiff_const)
  have hd : Continuous (tensorAdjoint H b V) := by
    apply continuous_finsetSum
    intro i _
    exact (((hV i).continuous_fderiv (by norm_num)).clm_apply continuous_const).neg.add
      (((hH.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul (hV i).continuous)
  have hc : Continuous (fun y => inner ℝ u (m y)) := continuous_const.inner hm
  let : IsProbabilityMeasure (gibbs H) := probability_gibbs_of_partition
    (partition_pos_of_continuous hH.continuous).ne' (partition_ne_top_of_integrable hi)
  let : IsOpenPosMeasure (gibbs H) := gibbs_openPos hH.continuous hi
  apply Measure.eq_of_ae_eq (μ:=gibbs H) _ hd hc
  apply ae_eq_of_integral_contDiff_smul_eq (μ:=gibbs H) hd.locallyIntegrable hc.locallyIntegrable
  intro φ hφ hφc
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hp := tensorAdjoint_compact_pairing hH hi hV hφ1 hφc b
  have ht := hw u φ hφ1 hφc
  simp only [smul_eq_mul]
  simp_rw [mul_comm (φ _)]; rw [hp,ht]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (directional_adjoint_basis (K y) u φ y).symm

theorem centeringKernel_strong {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T : ℝ} (hr : 0<r) (hlam : 0<lam)
    (hl : (lam:ℝ)*r^2≤1/2) (hT0 : 0≤T) (hT1 : T<1) (u : Point d) :
    tensorAdjoint (interpolationPotential F x r T) (EuclideanSpace.basisFun (Fin d) ℝ)
      (fun i y => inner ℝ u (centeringKernel hF x hr hl hT0 hT1 y (EuclideanSpace.basisFun (Fin d) ℝ i)))=
      fun y => inner ℝ u (conditionalFieldMean F x r T y-primitiveExpectedField F x r) := by
  have hs := interpolationPotential_smooth hF x hr.le hl hT0 hT1
  have hi := (interpolationPotential_lowerTail hF x hr.le (by linarith only [hl]) hT0 hT1).integrable_exp hs.continuous
  apply stein_weak_to_strong (hs.of_le (by simp)) hi
    ((centeringKernel_smooth hF x hr hlam hl hT0 hT1).of_le (by simp))
    ((conditionalFieldMean_smooth hF x hr.le hl hT0 hT1).continuous.sub continuous_const) _ u
  intro u φ hφ hφc
  have hh := centeringKernel_weak hF x hr hlam hl hT0 hT1 u hφ hφc
  rw [interpolationLaw_eq_gibbs hF x hr.le (by linarith only [hl])
    (by nlinarith [probability_time hT0 hT1])] at hh
  exact hh

end LogConcaveSampling

end

end

end

end OAI

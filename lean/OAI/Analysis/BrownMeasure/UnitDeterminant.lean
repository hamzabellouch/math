import Mathlib
import OAI.Analysis.BrownMeasure.Model

namespace OAI

noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped ComplexInnerProductSpace Topology ENNReal Ring
namespace FiniteFactor
local instance unitDeterminantRealModule : Module ℝ ProductOp := Module.complexToReal ProductOp
local instance unitDeterminantFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℝ ProductOp IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

lemma sourceVacuumFunctional_mono {A B : ProductOp} (h : A≤B) :
    (sourceVacuumFunctional A).re≤(sourceVacuumFunctional B).re := by
  have hpos := (ContinuousLinearMap.nonneg_iff_isPositive (f := B-A)).mp
    (sub_nonneg.mpr h)
  have hb := hpos.re_inner_nonneg_right sourceVacuum
  change 0≤(inner ℂ sourceVacuum ((B-A) sourceVacuum)).re at hb
  simp only [sub_apply,inner_sub_right,Complex.sub_re] at hb
  exact sub_nonneg.mp hb

lemma product_abs_isUnit {T : ProductOp} (hT : IsUnit T) : IsUnit (CFC.abs T) := by
  apply (isUnit_pow_iff (by norm_num : (2:ℕ)≠0)).mp
  rw [pow_two, CFC.abs_mul_abs]
  exact hT.star.mul hT

lemma product_abs_spectrum_pos {T : ProductOp} (hT : IsUnit T) {y : ℝ}
    (hy : y∈spectrum ℝ (CFC.abs T)) : 0<y := by
  refine (spectrum_nonneg_of_nonneg (CFC.abs_nonneg T) hy).lt_of_ne ?_
  intro he
  exact spectrum.zero_notMem ℝ (product_abs_isUnit hT) (he ▸ hy)

lemma logarithmCutoff_cfc_eq_log {A : ProductOp} (hA : 0≤A) (hu : IsUnit A) :
    ∃ n:ℕ,cfc (logarithmCutoff n) A=CFC.log A := by
  have hself := hA.isSelfAdjoint
  obtain ⟨y,hy,hmin⟩ := (spectrum.isCompact (𝕜:=ℝ) A).exists_isMinOn
    (ContinuousFunctionalCalculus.spectrum_nonempty A hself) continuous_id.continuousOn
  have hy0 : 0<y := by
    refine (spectrum_nonneg_of_nonneg hA hy).lt_of_ne ?_
    intro he
    exact spectrum.zero_notMem ℝ hu (he ▸ hy)
  have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hy0)).exists
  refine ⟨n,?_⟩
  apply cfc_congr
  intro x hx
  change Real.log (max (Real.exp (-(n:ℝ))) x)=Real.log x
  have hn' : Real.exp (-(n:ℝ))≤x := hn.le.trans (hmin hx)
  rw [max_eq_right hn']

lemma FugledeKadisonDeterminant_of_isUnit (T : ProductOp) (hu : IsUnit T) :
    FugledeKadisonDeterminant sourceVacuumFunctional T=
      ENNReal.ofReal (Real.exp (sourceVacuumFunctional (CFC.log (CFC.abs T))).re) := by
  have hp : ∀y∈spectrum ℝ (CFC.abs T),0<y := fun y hy=>product_abs_spectrum_pos hu hy
  have hc : ContinuousOn Real.log (spectrum ℝ (CFC.abs T)) := by
    apply Real.continuousOn_log.mono
    intro y hy
    exact (hp y hy).ne'
  apply le_antisymm
  · obtain ⟨n,hn⟩ := logarithmCutoff_cfc_eq_log (CFC.abs_nonneg T) (product_abs_isUnit hu)
    exact (iInf_le _ n).trans_eq
      (congrArg (fun operator : ProductOp =>
        ENNReal.ofReal (Real.exp (sourceVacuumFunctional operator).re)) hn)
  · apply le_iInf
    intro n
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply sourceVacuumFunctional_mono
    apply cfc_mono (hf:=hc) (hg:=(logarithmCutoff n).continuous.continuousOn)
    intro y hy
    exact Real.log_le_log (hp y hy) (le_max_right _ _)
end FiniteFactor
end

end OAI

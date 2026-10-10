import Mathlib
import OAI.Analysis.BrownMeasure.Mercator

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace BrownLog
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A] [Nontrivial A]
  [StarRing A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma mercator_eq_cfc_log_one_sub {a : A} (ha : IsSelfAdjoint a) (hn : ‖a‖<1) :
    mercator a=CFC.log (1-a) := by
  let : CompactSpace (spectrum ℝ a) := isCompact_iff_compactSpace.mp (spectrum.isCompact a)
  let : Nonempty (spectrum ℝ a) := (ContinuousFunctionalCalculus.spectrum_nonempty a ha).to_subtype
  let X : C(spectrum ℝ a,ℝ) := (ContinuousMap.id ℝ).restrict (spectrum ℝ a)
  have hX : ‖X‖<1 := by
    apply lt_of_le_of_lt ?_ hn
    apply (X.norm_le (norm_nonneg a)).mpr
    intro x
    exact spectrum.norm_le_norm_of_mem x.property
  let L : C(spectrum ℝ a,ℝ) →L[ℝ] A :=
    { toLinearMap := (cfcHom ha).toLinearMap, cont := cfcHom_continuous ha }
  have hXa : L X=a := cfcHom_id ha
  have hLX (n : ℕ) : L (((n+1:ℝ)⁻¹) • X^(n+1))=((n+1:ℝ)⁻¹) • a^(n+1) := by
    rw [map_smul]
    change ((n+1:ℝ)⁻¹) • (cfcHom ha) (X^(n+1))=_
    rw [map_pow]
    exact congrArg (fun z:A=>((n+1:ℝ)⁻¹) • z^(n+1)) hXa
  have hML : L (mercator X)=mercator a := by
    unfold mercator
    rw [map_neg,L.map_tsum (mercator_summable hX)]
    simp_rw [hLX]
  have hx1 (x : spectrum ℝ a) : |(x:ℝ)|<1 :=
    lt_of_le_of_lt (spectrum.norm_le_norm_of_mem x.property) hn
  have hxne (x : spectrum ℝ a) : 1-(x:ℝ)≠0 := by
    have := (abs_lt.mp (hx1 x)).2
    linarith
  let g : C(spectrum ℝ a,ℝ) :=
    ⟨fun x=>Real.log (1-(x:ℝ)),(continuous_const.sub continuous_subtype_val).log hxne⟩
  have hMg : mercator X=g := by
    apply ContinuousMap.ext
    intro x
    have h := (ContinuousMap.evalCLM ℝ x).hasSum (mercator_summable hX).hasSum
    have hv := Real.hasSum_pow_div_log_of_abs_lt_one (hx1 x)
    have he : (∑' n:ℕ,((n+1:ℝ)⁻¹) • X^(n+1)) x= -Real.log (1-(x:ℝ)) := by
      apply HasSum.unique ?_ hv
      simpa [X,smul_eq_mul,div_eq_mul_inv,mul_comm] using h
    change -(∑' n:ℕ,((n+1:ℝ)⁻¹) • X^(n+1)) x=_
    rw [he,neg_neg]
    rfl
  rw [← hML,hMg]
  change (cfcHom ha) g=CFC.log (1-a)
  have hcont : ContinuousOn (fun t:ℝ=>Real.log (1-t)) (spectrum ℝ a) := by
    exact continuousOn_iff_continuous_domRestrict.mpr g.continuous
  have hc1 : cfc (fun x:ℝ=>1-x) a=1-a := by
    rw [cfc_sub _ _ a (by fun_prop) (by fun_prop),cfc_const 1 a ha,cfc_id' ℝ a ha]
    simp
  rw [CFC.log,← hc1,← cfc_comp Real.log (fun x:ℝ=>1-x) a ha (by
    rintro _ ⟨x,hx,rfl⟩
    exact Real.continuousAt_log (hxne ⟨x,hx⟩) |>.continuousWithinAt) (by fun_prop)]
  exact (cfc_apply (fun x:ℝ=>Real.log (1-x)) a ha hcont).symm
end BrownLog
end

end OAI

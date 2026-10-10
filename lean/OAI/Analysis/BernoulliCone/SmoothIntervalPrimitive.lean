import OAI.Analysis.BernoulliCone.PiecewiseFoliationGraph

namespace OAI

universe uE uG

section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace Bernoulli.ParametricIntegral
variable {E : Type uE} {G : Type uG} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

omit [CompleteSpace G] in
lemma fixed_contDiff_one [CompleteSpace G] {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (fun x:E=>∫t in (0:ℝ)..1,F (x,t)) := by
  let D:E×ℝ→E→L[ℝ] G:=fun p=>fderiv ℝ F p ∘L ContinuousLinearMap.inl ℝ E ℝ
  have hD:Continuous D:=(hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hc:Continuous (fun x:E=>∫t in Icc (0:ℝ) 1,D (x,t)):=
    continuous_parametric_integral_of_continuous hD isCompact_Icc
  have he: (fun x:E=>∫t in Icc (0:ℝ) 1,D (x,t))=
      (fun x:E=>∫t in (0:ℝ)..1,D (x,t)) := by
    ext x
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_Icc_eq_integral_Ioc]
  rw [he] at hc
  exact contDiff_one_iff_hasFDerivAt.mpr ⟨_,hc,fun x=>fixed_hasFDerivAt hF x 0 1⟩

lemma heightPrimitive_contDiff_one {F:E×ℝ→G} (hF:ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (heightPrimitive F) := by
  let B:(E×ℝ)×ℝ→G:=fun z=>z.1.2 • F (z.1.1,z.2*z.1.2)
  have hB:ContDiff ℝ 1 B:=by
    have hm:ContDiff ℝ 1 (fun z:(E×ℝ)×ℝ=>(z.1.1,z.2*z.1.2)):=by fun_prop
    exact (contDiff_fst.snd).smul (hF.comp hm)
  have he:heightPrimitive F=(fun y:E×ℝ=>∫s in (0:ℝ)..1,B (y,s)):=
    funext (heightPrimitive_rescale F)
  rw [he]
  exact fixed_contDiff_one hB
end Bernoulli.ParametricIntegral

end
end

end OAI

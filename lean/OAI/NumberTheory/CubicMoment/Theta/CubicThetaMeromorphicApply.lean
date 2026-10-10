import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMeromorphicLinear

namespace OAI

/-! Applying a meromorphic operator to an analytic vector preserves its
finite pole order. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaMeromorphic_apply {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {A : ℂ → E →L[ℂ] F} {u : ℂ → E} {z : ℂ}
    (hA : MeromorphicAt A z) (hu : AnalyticAt ℂ u z) :
    MeromorphicAt (fun w => A w (u w)) z := by
  obtain ⟨n,hn⟩ := hA
  refine ⟨n,?_⟩
  have hb := (ContinuousLinearMap.id ℂ (E →L[ℂ] F)).analyticAt_bilinear
    ((z-z)^n • A z,u z)
  have h := hb.comp (f:=fun w => ((w-z)^n • A w,u w)) (x:=z) (hn.prod hu)
  simpa only [Function.comp_def,ContinuousLinearMap.id_apply,
    smul_apply] using h

end CubicFirstMoment

end

end OAI

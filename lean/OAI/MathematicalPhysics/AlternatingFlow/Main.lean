import OAI.MathematicalPhysics.AlternatingFlow.AnalyticResult
import OAI.MathematicalPhysics.AlternatingFlow.ForceNames
import OAI.MathematicalPhysics.AlternatingFlow.Compilers

namespace OAI

section MainResultDevelopment

namespace AlternatingNS

theorem alternating (ν : ℝ) (hν : 0 < ν) (hc : ComputableReal ν) :
    AlternatingConclusion ν := by
  obtain ⟨cf,hcf,hf⟩ := Effective.Certified.programs
    (Effective.force_certified ν) (Effective.force_named ν hc)
  obtain ⟨cu,hcu,hu⟩ := Effective.Certified.programs
    Effective.velocity_certified Effective.velocity_named
  refine ⟨cf,cu,hcf,hcu,Spatial.box,Spatial.box_compact,?_⟩
  intro M w hM hw
  obtain ⟨_,hfs,hUs,hfk,hUk,hfr,hUr,hr,hNS,hE,huniq,X,hX,hXuniq,hhalt⟩ :=
    Construction.alternating_analytic ν hν M w hM hw
  exact ⟨Construction.force ν M w,Construction.velocity M w,X,
    (hf (M,w)).congr_half (Effective.fullForce_half ν M w),hu (M,w),
    hfs,hUs,hfk,hUk,hfr,hUr,hr,hNS,hE,huniq,hX,hXuniq,hhalt⟩

end AlternatingNS

end MainResultDevelopment

end OAI

import Mathlib
import OAI.Geometry.PrescribedPotential.PatchCutoffs
import OAI.Geometry.PrescribedPotential.PositivePotentialLinearization
import OAI.Geometry.PrescribedPotential.RealSobolev
import OAI.Geometry.PrescribedPotential.SmoothPotentialDifference
import OAI.Geometry.PrescribedPotential.VolumePath
import OAI.Geometry.PrescribedRicci.SmoothPositivePath

namespace OAI

/-! Positive Path Openness. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical ComplexOrder
namespace Anticanonical.SourceSmooth
open GlobalElliptic
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
lemma logRatio_eq_log_density (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) (x : X) :
    (g.logRatio (g.deform φ hp)).value x = Real.log ((g.potentialDensity φ).value x) := by
  obtain ⟨i,hi⟩ := A.covers x
  rw [g.potentialDensity_quotient φ i hi]
  change g.logRatioValue (g.deform φ hp) x = _
  rw [g.logRatioValue_local _ i hi,Real.log_div
    (Complex.pos_iff.mp (hp i _ ((A.chart i).mapsTo hi)).det_pos).1.ne'
    (g.volumeCoefficient_pos i ((A.chart i).mapsTo hi)).ne']
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
lemma positive_add_of_deformed (g : KaehlerMetric A) (φ ψ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) (hq : (g.deform φ hp).PositivePotential ψ) :
    g.PositivePotential (φ.addFunction ψ) := by
  intro i z hz
  rw [SmoothRealFunction.hessian_addFunction _ _ i hz,← add_assoc]
  exact hq i z hz

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
lemma logRatio_add_deformed (g : KaehlerMetric A) (φ ψ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) (hq : (g.deform φ hp).PositivePotential ψ) (x : X) :
    (g.logRatio (g.deform (φ.addFunction ψ) (g.positive_add_of_deformed φ ψ hp hq))).value x =
    (g.logRatio (g.deform φ hp)).value x +
    ((g.deform φ hp).logRatio ((g.deform φ hp).deform ψ hq)).value x := by
  obtain ⟨i,hi⟩ := A.covers x
  change g.logRatioValue _ x = g.logRatioValue _ x + (g.deform φ hp).logRatioValue _ x
  rw [g.logRatioValue_local _ i hi,g.logRatioValue_local _ i hi,
    (g.deform φ hp).logRatioValue_local _ i hi]
  simp only [volumeCoefficient,deform,SmoothRealFunction.hessian_addFunction _ _ i ((A.chart i).mapsTo hi),add_assoc]
  ring
end KaehlerMetric

theorem volumePath_soluble_isOpen (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    IsOpen {t : ℝ | ∃ (φ : SmoothRealFunction A) (b : ℝ), SolvesVolumePath g h t φ b} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro t ⟨φ,b,hp,he⟩
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨S,⟨D⟩⟩ := exists_gluingData (g.deform φ hp)
  have hn := D.smooth_positive_path_eventually (RealSmooth.ofReal (prescribedForcing g h)) x₀
  have hsub : Tendsto (fun u : ℝ => u-t) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self] using (show Continuous (fun u : ℝ => u-t) from continuous_id.sub continuous_const).tendsto t
  filter_upwards [hsub.eventually hn] with u hu
  obtain ⟨ψ,c,hq,_,hden⟩ := hu
  refine ⟨φ.addFunction ψ,b+c,g.positive_add_of_deformed φ ψ hp hq,fun x => ?_⟩
  rw [g.logRatio_add_deformed φ ψ hp hq x,he x,
    (g.deform φ hp).logRatio_eq_log_density ψ hq x,hden x,Real.log_exp]
  change t*(prescribedForcing g h).value x+b+((u-t)*(prescribedForcing g h).value x+c) = _
  ring
end Anticanonical.SourceSmooth

end
end

end OAI

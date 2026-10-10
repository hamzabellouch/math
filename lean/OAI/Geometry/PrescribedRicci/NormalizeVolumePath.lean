import Mathlib
import OAI.Geometry.PrescribedPotential.SmoothPotentialDifference
import OAI.Geometry.PrescribedPotential.VolumePath
import OAI.Geometry.PrescribedRicci.KahlerIntegralPos
import OAI.Geometry.PrescribedRicci.PathUniformSobolevBase

namespace OAI

/-! Normalize Volume Path. -/

section

 
noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace Anticanonical.SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}
namespace KaehlerMetric
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
lemma positive_add_constant (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) (c : ℝ) :
    g.PositivePotential (φ.addFunction (SmoothRealFunction.constant c)) := by
  intro i z hz
  rw [SmoothRealFunction.hessian_addFunction _ _ i hz,SmoothRealFunction.hessian_constant,add_zero]
  exact hp i z hz

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
lemma logRatio_add_constant (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    (hp : g.PositivePotential φ) (c : ℝ) (x : X) :
    (g.logRatio (g.deform (φ.addFunction (SmoothRealFunction.constant c))
      (g.positive_add_constant φ hp c))).value x = (g.logRatio (g.deform φ hp)).value x := by
  obtain ⟨i,hi⟩ := A.covers x
  change g.logRatioValue _ x = g.logRatioValue _ x
  rw [g.logRatioValue_local _ i hi,g.logRatioValue_local _ i hi]
  simp only [volumeCoefficient,deform,
    SmoothRealFunction.hessian_addFunction _ _ i ((A.chart i).mapsTo hi),
    SmoothRealFunction.hessian_constant,add_zero]

lemma normalizeVolumePath (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) {φ : SmoothRealFunction A} {b : ℝ}
    (hsol : SolvesVolumePath g line t φ b) :
    ∃ z : g.NormalizedPathSolution line, z.time = t ∧ z.constant = b := by
  obtain ⟨hp,he⟩ := hsol
  let V := g.integral (fun _ => (1:ℝ))
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hV : 0 < V := g.integral_pos continuous_const (fun _ => zero_le_one) (x:=x₀) zero_lt_one
  let c := -g.integral φ.value/V
  let ψ := φ.addFunction (SmoothRealFunction.constant c)
  have hm : g.integral ψ.value = 0 := by
    change g.integral (fun x => φ.value x+c) = 0
    rw [g.integral_add φ.continuous continuous_const]
    have hc : g.integral (fun _ : X => c) = c*V := by
      simpa only [mul_one] using g.integral_const_mul c (fun _ => (1:ℝ))
    rw [hc]
    dsimp [c]
    rw [div_mul_cancel₀ _ hV.ne']
    ring
  refine ⟨⟨ψ,g.positive_add_constant φ hp c,hm,t,ht,b,?_⟩,rfl,rfl⟩
  intro x
  rw [g.logRatio_add_constant φ hp c x,he x]
end KaehlerMetric
end Anticanonical.SourceSmooth

end
end

end OAI

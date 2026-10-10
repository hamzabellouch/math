import Mathlib
import OAI.Geometry.PrescribedPotential.NormalizedPoisson
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Dimension Zero Potential. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff Classical ComplexOrder
namespace Anticanonical.SourceSmooth
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas 0 X}

lemma dimensionZero_forcing_constant (g : KaehlerMetric A)
    (line : SemipositiveAnticanonicalMetric A) :
    ∃ c : ℝ, ∀ x, (prescribedForcing g line).value x = c := by
  obtain ⟨u,c,_,he⟩ := normalizedPoisson 0 X A g (Classical.arbitrary X) (prescribedForcing g line)
  refine ⟨c,fun x => ?_⟩
  obtain ⟨i,hi⟩ := A.covers x
  have h := he i (A.chart i x) ((A.chart i).mapsTo hi)
  have hz : g.linearizedMongeAmpere u i (A.chart i x) = 0 := by
    simp [KaehlerMetric.linearizedMongeAmpere,Matrix.trace]
  rw [hz,zero_add] at h
  have hx : (prescribedForcing g line).localExpression i (A.chart i x) =
      (prescribedForcing g line).value x := by
    simp only [SmoothRealFunction.localExpression,Function.comp_apply,(A.chart i).left_inv hi]
  exact (h.trans hx).symm

lemma volumePath_zeroDim_one (g : KaehlerMetric A) (line : SemipositiveAnticanonicalMetric A) :
    ∃ (φ : SmoothRealFunction A) (b : ℝ), SolvesVolumePath g line 1 φ b := by
  obtain ⟨c,hc⟩ := dimensionZero_forcing_constant g line
  obtain ⟨hp,hzero⟩ := volumePath_zero g line
  refine ⟨SmoothRealFunction.constant 0,-c,hp,fun x => ?_⟩
  rw [hzero x,hc x]
  ring

end Anticanonical.SourceSmooth

end
end

end OAI

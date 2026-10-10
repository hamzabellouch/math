import OAI.Analysis.MarkovType.Renormed
import OAI.Analysis.MarkovType.JConvexityBasic
import OAI.Analysis.MarkovType.UniformSmoothNonsquare

namespace OAI

namespace MarkovSuperreflexivity

universe u
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace Renormed

@[simp] theorem normSeminorm_comp_original (N : EquivalentNorm X) :
    (normSeminorm ℝ (Renormed N)).comp (linearEquiv N).toLinearMap = N.p := by
  ext x
  rfl

@[simp] theorem originalSeminorm_comp_inverse (N : EquivalentNorm X) :
    N.p.comp (linearEquiv N).symm.toLinearMap = normSeminorm ℝ (Renormed N) := by
  ext x
  rfl

theorem ambientJConvex_iff (N : EquivalentNorm X) :
    AmbientJConvex (Renormed N) ↔ JConvex N.p := by
  constructor
  · intro h
    simpa only [normSeminorm_comp_original] using h.comp (linearEquiv N).toLinearMap
  · intro h
    change JConvex (normSeminorm ℝ (Renormed N))
    simpa only [originalSeminorm_comp_inverse] using h.comp (linearEquiv N).symm.toLinearMap

theorem ambientJConvex_of_uniformConvex (N : EquivalentNorm X) (h : UniformConvex N.p) :
    AmbientJConvex (Renormed N) :=
  (ambientJConvex_iff N).mpr h.jConvex

theorem ambientJConvex_of_uniformSmooth (N : EquivalentNorm X) (h : UniformSmooth N.p) :
    AmbientJConvex (Renormed N) :=
  (ambientJConvex_iff N).mpr h.jConvex

end Renormed
end MarkovSuperreflexivity

end OAI

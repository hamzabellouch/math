import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Bounded linear transport preserves the finite pole order. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaMeromorphic_clm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) {f : ℂ → E} {z : ℂ} (hf : MeromorphicAt f z) :
    MeromorphicAt (fun w => L (f w)) z := by
  obtain ⟨n,hn⟩ := hf
  refine ⟨n,?_⟩
  have h := (L.analyticAt _).comp (f:=fun w : ℂ => (w-z)^n • f w) (x:=z) hn
  simpa only [Function.comp_def, L.map_smul] using h

end CubicFirstMoment

end

end OAI

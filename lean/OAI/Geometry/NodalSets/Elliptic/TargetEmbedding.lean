import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import OAI.Geometry.NodalSets.Model

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section
abbrev AmbientBase := EuclideanSpace ℝ (Fin 5)
abbrev Ambient := AmbientBase × ℂ
attribute [local instance] finrank_real_complex_fact'
local instance : Fact (Module.finrank ℝ AmbientBase = 4 + 1) := ⟨by simp [AmbientBase]⟩

def targetEmbedding (x : Manifold5) : Ambient := ((x.1 : AmbientBase),(x.2 : ℂ))

lemma targetEmbedding_smooth : ContMDiff modelWithCorners 𝓘(ℝ,Ambient) ∞ targetEmbedding := by
  rw [show 𝓘(ℝ,Ambient) = 𝓘(ℝ,AmbientBase).prod 𝓘(ℝ,ℂ) from modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact (contMDiff_coe_sphere (E := AmbientBase) (n := 4)).prodMap
    (contMDiff_coe_sphere (E := ℂ) (n := 1))

lemma targetEmbedding_derivative (x : Manifold5) :
    mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding x =
      (mfderiv (𝓡 4) 𝓘(ℝ,AmbientBase) (Subtype.val : Base → AmbientBase) x.1).prodMap
      (mfderiv (𝓡 1) 𝓘(ℝ,ℂ) (fun z : Circle ↦ (z : ℂ)) x.2) := by
  rw [show 𝓘(ℝ,Ambient) = 𝓘(ℝ,AmbientBase).prod 𝓘(ℝ,ℂ) from modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mfderiv_prodMap
    ((contMDiff_coe_sphere (E := AmbientBase) (n := 4) (m := ∞)).mdifferentiable (by simp) x.1)
    ((contMDiff_coe_sphere (E := ℂ) (n := 1) (m := ∞)).mdifferentiable (by simp) x.2)

lemma targetEmbedding_immersion (x : Manifold5) :
    Function.Injective (mfderiv modelWithCorners 𝓘(ℝ,Ambient) targetEmbedding x) := by
  rw [targetEmbedding_derivative]
  intro v w he
  apply Prod.ext
  · apply injective_mvfderiv_subtypeVal_sphere (n := 4) x.1
    exact congrArg Prod.fst he
  · apply injective_mvfderiv_subtypeVal_sphere (n := 1) x.2
    exact congrArg Prod.snd he

end
end Yau.Target

end OAI

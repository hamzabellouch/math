import Mathlib
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.IntegerBounds

namespace OAI

/-! Schwartz Conjugation. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap Classical
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def schwartzConj : 𝓢(E,ℂ) →L[ℝ] 𝓢(E,ℂ) := SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap

@[simp] lemma schwartzConj_apply (f : 𝓢(E,ℂ)) (x : E) : schwartzConj f x = star (f x) := rfl

lemma schwartzConj_deriv (v : E) (f : 𝓢(E,ℂ)) :
    (∂_{v} (schwartzConj f) : 𝓢(E,ℂ)) = schwartzConj (∂_{v} f) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,schwartzConj_apply]
  exact congrArg (fun L : E →L[ℝ] ℂ => L v)
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp x
      ((f.smooth ⊤).differentiable (by simp) x).hasFDerivAt).fderiv

lemma schwartzConj_word (ws : List E) (f : 𝓢(E,ℂ)) :
    schwartzWord ws (schwartzConj f) = schwartzConj (schwartzWord ws f) := by
  induction ws generalizing f with
  | nil => rfl
  | cons v ws ih =>
    change ∂_{v} (schwartzWord ws (schwartzConj f)) = schwartzConj (∂_{v} (schwartzWord ws f))
    rw [ih,schwartzConj_deriv]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartzConj_norm_zero (f : 𝓢(E,ℂ)) :
    ‖schwartzCoord 0 (schwartzConj f)‖ = ‖schwartzCoord 0 f‖ := by
  have he (u : 𝓢(E,ℂ)) : schwartzCoord 0 u = u.toLp 2 volume := by
    apply l2_injective
    simpa [realize] using realize_schwartzCoord 0 u
  rw [he,he,SchwartzMap.norm_toLp,SchwartzMap.norm_toLp]
  congr 1
  apply eLpNorm_congr_norm_ae (schwartzConj f).continuous.aestronglyMeasurable
    f.continuous.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simp)

lemma schwartzConj_integer_bound (k : ℕ) : CoreBound (k : ℝ) (k : ℝ) (schwartzConj (E := E)) := by
  have hh := coreBound_of_words_integer k (s := (k : ℝ)) (t := 0) (schwartzConj (E := E)) (fun ws hws => by
    obtain ⟨C,hC,hb⟩ := coreBound_word ws (s := (k : ℝ)) (t := 0) (by
      have hh : (ws.length : ℝ) ≤ k := by exact_mod_cast hws
      linarith)
    refine ⟨C,hC,fun f => ?_⟩
    dsimp only
    rw [schwartzConj_word,schwartzConj_norm_zero]
    exact hb f)
  simpa using hh
end SobolevChart

end
end

end OAI

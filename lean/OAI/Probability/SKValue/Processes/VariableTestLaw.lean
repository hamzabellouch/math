import Mathlib
import OAI.Probability.SKValue.Equations.ResponseContraction
import OAI.Probability.SKValue.Gaussian.UniformError
import OAI.Probability.SKValue.Equations.UniformPolynomial

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma IsDiffusion.splitResponse_varying {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) (t:Ioo (0:ℝ) 1) {F:ℕ → ℝ → ℝ} {f:ℝ → ℝ}
    (hF:∀ n,BoundedSmooth (F n)) (hf:BoundedSmooth f) (hl:BoundedUniformLimit F f) :
    Tendsto (fun n ↦ profileResponse (splitTerminal γ t n) (F n) (γ.splitSegment 0 t t.property.1.le n) 0 0)
      atTop (𝓝 (∫ z, f (X t z) ∂W.μ)) := by
  obtain ⟨C,hC,hb,hfb⟩:=hl.bound
  have he:∀ n,∃ D:ℝ,∀ x,|F n x-f x| ≤ D :=
    fun n ↦ ⟨C+C,fun x ↦ (abs_sub _ _).trans (add_le_add (hb n x) (hfb x))⟩
  have hel:=uniformDistance_tendsto hl.tendsto he
  have hd:Tendsto (fun n ↦ profileResponse (splitTerminal γ t n) (F n) (γ.splitSegment 0 t t.property.1.le n) 0 0-
      profileResponse (splitTerminal γ t n) f (γ.splitSegment 0 t t.property.1.le n) 0 0) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n ↦ ?_) hel
    rw [Real.norm_eq_abs]
    exact (splitTerminal_smooth γ t n).profile_response_contraction (hF n) hf (le_uniformDistance (he n)) _ _ _
  have ht:=hd.add (hX.splitResponse_tendsto t hf)
  simpa only [sub_add_cancel,zero_add] using ht
end SKValue

end

end OAI

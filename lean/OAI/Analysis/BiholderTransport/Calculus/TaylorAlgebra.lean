import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.Pole

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def SecondTaylorRemainder (f : E → ℝ) (D : E →L[ℝ] ℝ)
    (K : E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  (fun h => f h-f 0-D h-K h h/2) =o[𝓝 0] (fun h : E => ‖h‖^2)

lemma SecondTaylorRemainder.sub {f g : E → ℝ} {D D' : E →L[ℝ] ℝ}
    {K K' : E →L[ℝ] E →L[ℝ] ℝ} (hf : SecondTaylorRemainder f D K)
    (hg : SecondTaylorRemainder g D' K') :
    SecondTaylorRemainder (fun h => f h-g h) (D-D') (K-K') := by
  unfold SecondTaylorRemainder at *
  convert! hf.sub hg using 1
  funext h
  simp only [sub_apply]
  ring

lemma SecondTaylorRemainder.const_mul {f : E → ℝ} {D : E →L[ℝ] ℝ}
    {K : E →L[ℝ] E →L[ℝ] ℝ} (hf : SecondTaylorRemainder f D K) (c : ℝ) :
    SecondTaylorRemainder (fun h => c*f h) (c • D) (c • K) := by
  unfold SecondTaylorRemainder at *
  convert! hf.const_mul_left c using 1
  funext h
  simp only [smul_apply,smul_eq_mul]
  ring

lemma SecondTaylorRemainder.sum {ι : Type*} (s : Finset ι)
    {f : ι → E → ℝ} {D : ι → E →L[ℝ] ℝ} {K : ι → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ∀ i ∈ s, SecondTaylorRemainder (f i) (D i) (K i)) :
    SecondTaylorRemainder (fun h => ∑ i ∈ s, f i h) (∑ i ∈ s, D i) (∑ i ∈ s, K i) := by
  unfold SecondTaylorRemainder at *
  have H := Asymptotics.IsLittleO.sum hf
  convert! H using 1
  funext h
  simp only [Finset.sum_apply,sum_apply,Finset.sum_sub_distrib,Finset.sum_div]

lemma SecondTaylorRemainder.comp_linear {f : F → ℝ} {D : F →L[ℝ] ℝ}
    {K : F →L[ℝ] F →L[ℝ] ℝ} (hf : SecondTaylorRemainder f D K) (T : E →L[ℝ] F) :
    SecondTaylorRemainder (fun h => f (T h)) (D.comp T) (K.bilinearComp T T) := by
  have H := second_order_substitution_exact_linear hf (map_zero T) (T.hasFDerivAt (x := 0))
  simpa only [SecondTaylorRemainder,map_zero,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.bilinearComp_apply] using H


end WeakMTWTransport
end

end OAI

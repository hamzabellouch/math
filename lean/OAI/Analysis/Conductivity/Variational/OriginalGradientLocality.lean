import Mathlib
import OAI.Analysis.Conductivity.Variational.LocalSmoothWeakDerivative

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma original_local_constant_gradient (u : H1) {U : Set R3}
    (hU : IsOpen U) (hUb : U⊆ball) (c : ℝ)
    (hv : ∀ᵐ x∂ballMeasure,x∈U → weakValue u x=c) :
    ∀ᵐ x∂ballMeasure,x∈U → weakGradient u x=0 := by
  have he : weakValue u=ᵐ[volume.restrict U] fun _ => c := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hUb hv,ae_restrict_mem hU.measurableSet] with x hx hm
    exact hx hm
  have hg := original_contDiffOn_representative_gradient u hU hUb (fun _ => c) contDiffOn_const he
  filter_upwards [ae_restrict_of_ae hg] with x hx hm
  rw [hx hm]
  exact gradient_fun_const x c

lemma original_local_value_difference_gradient (u v : H1) {U : Set R3}
    (hU : IsOpen U) (hUb : U⊆ball) (c : ℝ)
    (hv : ∀ᵐ x∂ballMeasure,x∈U → weakValue u x-weakValue v x=c) :
    ∀ᵐ x∂ballMeasure,x∈U → weakGradient u x=weakGradient v x := by
  have he : ∀ᵐ x∂ballMeasure,x∈U → weakValue (u-v) x=c := by
    filter_upwards [hv,weakValue_sub u v] with x hx hs hm
    rw [hs]
    exact hx hm
  filter_upwards [original_local_constant_gradient (u-v) hU hUb c he,weakGradient_sub u v]
    with x hx hs hm
  have hh := hx hm
  rw [hs] at hh
  exact sub_eq_zero.mp hh

end ScalarConductivity

end
end

end OAI
